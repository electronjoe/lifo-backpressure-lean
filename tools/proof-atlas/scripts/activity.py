"""Publish short-lived proof activity for the claim inventory."""
import argparse
import base64
import json
from pathlib import Path
import re
import subprocess
import sys
import threading
import time
from uuid import uuid4

from atlas import atomic, proof_work_description


def gh(endpoint, body=None):
    args = ["gh", "api", endpoint]
    if body is not None:
        args.extend(["--method", "PUT", "--input", "-"])
    result = subprocess.run(args, input=json.dumps(body) if body else None,
                            text=True, encoding="utf-8", capture_output=True, timeout=25)
    if result.returncode:
        raise RuntimeError(result.stderr.strip())
    return json.loads(result.stdout)


def publish(project, event):
    repo = project["hosting"]["repository"].removeprefix("https://github.com/").rstrip("/")
    if not re.fullmatch(r"[\w.-]+/[\w.-]+", repo):
        raise ValueError("Activity publishing requires a GitHub repository")
    branch = "proof-atlas-activity"
    endpoint = f"repos/{repo}/contents/activity.json"
    for attempt in range(3):
        try:
            old = gh(endpoint + "?ref=" + branch)
            records = json.loads(base64.b64decode(old["content"]))["runs"]
        except RuntimeError as exc:
            if "404" not in str(exc):
                raise
            old, records = {}, []
        recent = {r["id"]: r for r in records if r["updated"] > time.time()-86400}
        if recent.get(event["id"], {}).get("updated", 0) > event["updated"]:
            return
        recent[event["id"]] = event
        content = base64.b64encode(json.dumps({"runs": list(recent.values())}).encode()).decode()
        body = dict(message="Update proof activity", branch=branch, content=content)
        if old:
            body["sha"] = old["sha"]
        try:
            gh(endpoint, body)
            return
        except RuntimeError as exc:
            if attempt == 2 or not any(code in str(exc) for code in ("409", "422")):
                raise


class Activity:
    def __init__(self, root, claim, task, run_id, public):
        self.root = root
        self.project = json.loads((root / "project.json").read_bytes())
        self.claim = claim or self.project["focus"]
        claims = json.loads((root / "dist/inventory.json").read_bytes())
        print("Authorized proof work: " + proof_work_description(self.project, claims), flush=True)
        print(f"Claim: {self.claim} | Task: {task}", flush=True)
        if self.claim not in {c["id"] for c in claims}:
            raise ValueError(f"Unknown inventory claim {self.claim}")
        self.task = task
        self.run_id = run_id or uuid4().hex
        if not re.fullmatch(r"[A-Za-z0-9_-]{1,80}", self.run_id):
            raise ValueError("Use letters, digits, hyphens or underscores in an activity ID")
        self.public = public
        self.stop = threading.Event()

    def report(self, phase):
        now = int(time.time())
        event = dict(id=self.run_id, claim=self.claim, task=self.task, phase=phase, updated=now,
                     expires=now + (900 if phase == "writing" else 300))
        folder = self.root / ".proof-atlas-activity"
        folder.mkdir(exist_ok=True)
        atomic(folder / (self.run_id + ".json"), json.dumps(event).encode())
        runs = [json.loads(path.read_bytes()) for path in folder.glob("*.json")]
        atomic(self.root / "dist/activity.json", json.dumps({"runs": runs}).encode())
        if self.public:
            publish(self.project, event)

    def report_check(self, phase):
        try:
            self.report(phase)
        except (OSError, RuntimeError, subprocess.SubprocessError) as exc:
            print(f"Activity update failed: {exc}", file=sys.stderr, flush=True)

    def __enter__(self):
        self.report_check("checking")
        def heartbeat():
            while not self.stop.wait(100):
                self.report_check("checking")
        self.thread = threading.Thread(target=heartbeat, daemon=True)
        self.thread.start()
        return self

    def __exit__(self, kind, value, trace):
        self.stop.set()
        self.thread.join()
        self.report_check("failed" if kind else "finished")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path)
    parser.add_argument("phase", choices=("writing", "paused"))
    parser.add_argument("--claim")
    parser.add_argument("--task", required=True)
    parser.add_argument("--id", required=True)
    parser.add_argument("--publish", action="store_true")
    args = parser.parse_args()
    Activity(args.project, args.claim, args.task, args.id, args.publish).report(args.phase)
