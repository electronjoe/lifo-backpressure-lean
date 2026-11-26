"""Provision the project's Lean toolchain and run its Lake build. Python 3.9+."""
import argparse
from contextlib import nullcontext
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import urllib.request
import zipfile
from activity import Activity


def run(args, package, env, log, *, required=True):
    print("$", subprocess.list2cmdline([str(a) for a in args]), file=log, flush=True)
    if required:
        # Let the agent tail long package builds without keeping Mathlib output in memory.
        result = subprocess.run(args, cwd=package, env=env, stdout=log,
                                stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
        if result.returncode:
            raise RuntimeError(f"{args[-1]} exited {result.returncode}; see preceding command output")
        return None
    result = subprocess.run(args, cwd=package, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
    encoding = "utf-16-le" if b"\x00" in result.stdout[:80] else "utf-8-sig"
    output = result.stdout.decode(encoding, errors="replace").strip()
    print(output, file=log, flush=True)
    return output if result.returncode == 0 else None


def install_elan(package, env, log):
    if os.name == "nt":
        url = "https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-pc-windows-msvc.zip"
    else:
        url = "https://elan.lean-lang.org/elan-init.sh"
    print(f"Downloading official Elan installer from {url}", file=log, flush=True)
    with tempfile.TemporaryDirectory() as temp:
        archive = Path(temp) / "download"
        with urllib.request.urlopen(url, timeout=60) as response, archive.open("wb") as out:
            shutil.copyfileobj(response, out)
        if os.name == "nt":
            installer = Path(temp) / "elan-init.exe"
            with zipfile.ZipFile(archive) as bundle, bundle.open(installer.name) as src, installer.open("wb") as dst:
                shutil.copyfileobj(src, dst)
            command = [installer]
        else:
            command = ["sh", archive]
        run([*command, "-y", "--no-modify-path", "--default-toolchain", "none"], package, env, log)


def select_lake(package, pin, env, log, offline=False):
    private = package / ".proof-atlas-tools" / "elan"
    suffix = ".exe" if os.name == "nt" else ""
    user_home = Path(env.get("ELAN_HOME", Path.home() / ".elan"))
    elan_run = ["run", *([] if offline else ["--install"]), pin, "lake"]
    for home in (private, user_home):
        elan = home / "bin" / ("elan" + suffix)
        if elan.is_file():
            env["ELAN_HOME"] = str(home)
            return [str(elan), *elan_run]
    elan = shutil.which("elan")
    if elan:
        return [elan, *elan_run]

    # A standalone release may have been unpacked without Elan.
    lean = shutil.which("lean")
    exact = re.fullmatch(r"(?:leanprover/lean4:)?v?(\d+\.\d+\.\d+(?:-[\w.-]+)?)", pin)
    if lean and exact:
        lake = Path(lean).with_name("lake" + suffix)
        version = run([lean, "--version"], package, env, log, required=False)
        if lake.is_file() and version and re.search(r"\bversion " + re.escape(exact[1]) + r"(?=[ ,)])", version):
            env["PATH"] = str(lake.parent) + os.pathsep + env.get("PATH", "")
            return [str(lake)]

    if os.name == "nt" and shutil.which("wsl"):
        wsl = ["wsl", "--cd", str(package), "--exec", "sh", "-c"]
        locate = 'export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"; command -v elan'
        location = run([*wsl, locate], package, env, log, required=False)
        if location:
            return ["wsl", "--cd", str(package), "--exec", location.splitlines()[-1], *elan_run]
        if exact:
            version = run([*wsl, "command -v lake >/dev/null && lean --version"],
                          package, env, log, required=False)
            if version and re.search(r"\bversion " + re.escape(exact[1]) + r"(?=[ ,)])", version):
                return ["wsl", "--cd", str(package), "--exec", "lake"]

    if offline:
        raise RuntimeError("No installed Lean toolchain manager or matching Lean/Lake pair was found")
    env["ELAN_HOME"] = str(private)
    install_elan(package, env, log)
    return [str(private / "bin" / ("elan" + suffix)), *elan_run]


def check(package, log, mathlib_modules=(), offline=False, targets=()):
    pin = (package / "lean-toolchain").read_text(encoding="utf-8-sig").strip()
    if not pin or any(char.isspace() for char in pin) or pin.startswith("-"):
        raise ValueError("Invalid lean-toolchain file")
    if not any((package / name).is_file() for name in ("lakefile.toml", "lakefile.lean")):
        raise ValueError("Missing Lake package configuration")
    print(f"Lean toolchain: {pin}", file=log, flush=True)
    env = os.environ.copy()
    env["ELAN_TOOLCHAIN"] = pin
    lake = select_lake(package, pin, env, log, offline)
    if offline or mathlib_modules:
        env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    if offline:
        env["GIT_ALLOW_PROTOCOL"] = "file"
    if lake[0] == "wsl":
        forward = [name for name in ("MATHLIB_NO_CACHE_ON_UPDATE", "GIT_ALLOW_PROTOCOL") if name in env]
        env["WSLENV"] = ":".join(filter(None, [env.get("WSLENV"), *forward]))
    run([*lake, "--version"], package, env, log)
    if mathlib_modules and not offline:
        # Mathlib's cold-start hook otherwise fetches every module in the library.
        try:
            run([*lake, "exe", "cache", "get", *mathlib_modules], package, env, log)
        except RuntimeError as exc:
            print(f"Precompiled cache unavailable ({exc}); continuing with Lake build.", file=log, flush=True)
    build_args = ["--no-cache", "build"] if offline else ["build"]
    run([*lake, *build_args, *targets], package, env, log)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("--logs", type=Path, help="Directory for one timestamped log per run")
    parser.add_argument("--mathlib-module", action="append", default=[],
                        help="Fetch precompiled dependencies for this Mathlib import; repeat per module")
    parser.add_argument("--offline", action="store_true",
                        help="Reuse the installed toolchain and local dependencies; disable remote Git and cache downloads")
    parser.add_argument("--project", type=Path, help="Atlas project containing the claim inventory")
    parser.add_argument("--claim", help="Inventory label being checked (defaults to the project focus)")
    parser.add_argument("--task", default="Check the selected Lean declarations")
    parser.add_argument("--activity-id", help="Continue an existing proof-writing activity")
    parser.add_argument("--target", action="append", default=[], help="Check a specific Lake module or library during proof development")
    parser.add_argument("--publish-activity", action="store_true", help="Also report activity to the configured GitHub repository")
    args = parser.parse_args()
    if any(not re.fullmatch(r"[A-Za-z_][\w'.]*", name) for name in args.target):
        parser.error("--target expects a Lean module or library name")
    package = args.package.resolve(strict=True)
    logs = args.logs or package / ".proof-atlas-tools" / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=logs, delete=False,
                                     prefix=f"lean-{stamp}-", suffix=".log") as log:
        print(f"Lean run log: {log.name}", flush=True)
        try:
            root = args.project or package.parent
            activity = nullcontext()
            bound = (root / "dist/inventory.json").is_file() and (root / "project.json").is_file()
            if args.claim or args.project or args.publish_activity or (bound and json.loads((root / "project.json").read_bytes()).get("focus")):
                activity = Activity(root, args.claim, args.task, args.activity_id, args.publish_activity)
            with activity:
                check(package, log, args.mathlib_module, args.offline, args.target)
        except (OSError, ValueError, RuntimeError, KeyError, zipfile.BadZipFile) as exc:
            print(f"Build incomplete: {exc}", file=log)
            print(f"Build incomplete: {exc}", file=sys.stderr)
            return 1
        print("Lake build completed.", file=log)
        print("Lake build completed.")
        return 0


if __name__ == "__main__":
    sys.exit(main())
