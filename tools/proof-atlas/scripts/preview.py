"""Serve the generated Atlas and rebuild both entry points as project inputs change."""
import argparse
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
import json
import os
from pathlib import Path
import threading
import webbrowser

from atlas import atomic, build_local, local


def inputs(root):
    paths = {root / "project.json", root / "reviews.json", root / "comparisons.json", root / "manuscript-edits.json"}
    p = json.loads((root / "project.json").read_text(encoding="utf-8-sig"))
    paths.update(local(root, src["path"]) for src in [p["pdf"], *p["tex"]])
    if figure := p.get("folio", {}).get("figure"):
        paths.add(local(root, figure["path"]))
    for w in p.get("work", {}).values():
        for name in [w.get("lean"), w.get("run_log"), w.get("closure", {}).get("audit"), *w.get("lean_sources", []), *w.get("checked_inputs", {})]:
            if name:
                paths.add(local(root, name))
    if p.get("reader"):
        metadata = local(root, p["reader"])
        paths.add(metadata)
        for record in json.loads(metadata.read_text(encoding="utf-8-sig")).get("claims", {}).values():
            if record.get("lamport"):
                paths.add(local(root, record["lamport"]))
    def stamp(path):
        try:
            stat = path.stat()
            return (os.fspath(path), stat.st_mtime_ns, stat.st_size)
        except FileNotFoundError:
            return (os.fspath(path), None, None)
    return tuple(stamp(path) for path in sorted(paths))


def watch(root, stop, last):
    status = root / "dist" / "preview-status.json"
    error = None
    atomic(status, b'{}')
    while not stop.wait(1):
        try:
            current = inputs(root)
            if current != last or error:
                build_local(root)
                last = current
                error = None
                atomic(status, b'{}')
        except (OSError, ValueError, KeyError, TypeError) as exc:
            if str(exc) != error:
                error = str(exc)
                print("Preview rebuild failed:", error, flush=True)
                atomic(status, json.dumps({"error":error}).encode())


class Handler(SimpleHTTPRequestHandler):
    def end_headers(self):
        self.send_header("Cache-Control", "no-cache")
        super().end_headers()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path)
    parser.add_argument("--port", type=int, default=0)
    parser.add_argument("--open", action="store_true", help="Open the Explorer and dashboard in the default browser")
    args = parser.parse_args()
    root = args.project.resolve()
    initial = inputs(root)
    build_local(root)
    with ThreadingHTTPServer(("127.0.0.1", args.port), partial(Handler, directory=str(root / "dist"))) as server:
        base = f"http://127.0.0.1:{server.server_port}/"
        print(f"Proof Atlas: {base}proofs/index.html\nDashboard: {base}progress.html", flush=True)
        stop = threading.Event()
        watcher = threading.Thread(target=watch, args=(root, stop, initial), daemon=True)
        watcher.start()
        if args.open:
            for url in ("progress.html", "proofs/index.html"):
                webbrowser.open_new_tab(base + url)
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            pass
        finally:
            stop.set()
            watcher.join()


if __name__ == "__main__":
    main()
