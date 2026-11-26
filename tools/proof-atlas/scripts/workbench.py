"""Paper-agnostic v2 Audit Workbench generator for Proof Atlas.

Synthesizes `dist/index.html`, `dist/workbench.css`, and `dist/workbench.js`
directly from live repository records (`project.json`, `reader.json`,
`comparisons.json`, `manuscript-edits.json`, `quality.json`, `lamport/*.md`,
`evidence/*.json`, Lean sources, and GitHub Actions CI receipts).
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from html import escape
from pathlib import Path

KIND_POLARITY = {
    "agrees": "agrees",
    "stronger": "stronger",
    "other form": "nuance",
    "chosen reading": "nuance",
    "restriction": "gap",
    "added hypothesis": "gap",
    "weaker conclusion": "gap",
}


def _file_sha8(path: Path) -> str:
    if path.is_file():
        return hashlib.sha256(path.read_bytes()).hexdigest()[:8]
    return ""


def _git_short_head(root: Path) -> str:
    try:
        out = subprocess.check_output(
            ["git", "-C", str(root), "rev-parse", "--short", "HEAD"],
            stderr=subprocess.DEVNULL,
            text=True,
        ).strip()
        return out
    except Exception:
        return ""


def _scan_lean_stats(root: Path, project: dict) -> dict:
    """Compute live Lean LoC, file count, toolchain, and Mathlib revision."""
    pkg_dir = root / "lean"
    for w in project.get("work", {}).values():
        pkg = (w.get("closure") or w.get("statement_check") or {}).get("package")
        if pkg:
            pkg_dir = root / pkg
            break

    lean_files = []
    raw_loc = 0
    nonempty_loc = 0
    stmt_raw_loc = 0
    stmt_nonempty_loc = 0

    if pkg_dir.is_dir():
        for p in sorted(pkg_dir.rglob("*.lean")):
            if ".lake" in p.parts or "build" in p.parts:
                continue
            lean_files.append(p)
            lines = p.read_text(encoding="utf-8-sig").splitlines()
            ne = sum(1 for ln in lines if ln.strip())
            raw_loc += len(lines)
            nonempty_loc += ne
            if "Statements" in p.parts or p.name == "Statements.lean":
                stmt_raw_loc += len(lines)
                stmt_nonempty_loc += ne

    toolchain = ""
    tc_file = pkg_dir / "lean-toolchain"
    if tc_file.is_file():
        toolchain = tc_file.read_text(encoding="utf-8-sig").strip()

    mathlib_rev = ""
    manifest_file = pkg_dir / "lake-manifest.json"
    if manifest_file.is_file():
        try:
            mf = json.loads(manifest_file.read_text(encoding="utf-8-sig"))
            for pkg in mf.get("packages", []):
                if pkg.get("name") == "mathlib":
                    mathlib_rev = str(pkg.get("rev", ""))[:12]
                    break
        except Exception:
            pass

    return {
        "lean_files": len(lean_files),
        "raw_loc": raw_loc,
        "nonempty_loc": nonempty_loc,
        "stmt_raw_loc": stmt_raw_loc,
        "stmt_nonempty_loc": stmt_nonempty_loc,
        "toolchain": toolchain,
        "mathlib_rev": mathlib_rev,
    }


def _parse_lamport_markdown(text: str) -> dict:
    """Parse structured Lamport Markdown into hierarchical ⟨1⟩i / ⟨1⟩i.⟨2⟩j cards."""
    provenance = ""
    statement = ""
    groups: list[dict] = []
    cur_group: dict | None = None
    cur_step: dict | None = None

    lines = text.splitlines()
    for raw in lines:
        line = raw.rstrip()
        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith("# "):
            continue
        m_prov = re.match(r"^\*Provenance:\s*(.+?)\*$", stripped)
        if m_prov and not groups:
            provenance = m_prov.group(1).strip()
            continue
        if not groups and re.match(r"^\*\*(Theorem|Lemma|Proposition|Corollary|Claim)\b", stripped):
            statement = stripped
            continue

        # Top-level numbered group: "1. **Title**" or "1. **Title.**"
        m_grp = re.match(r"^(\d+)\.\s+\*\*(.+?)\*\*\s*(.*)$", stripped)
        if m_grp and not raw.startswith(" "):
            g_num = m_grp.group(1)
            g_title = m_grp.group(2).rstrip(".")
            g_tail = m_grp.group(3).strip()
            cur_group = {"id": f"⟨1⟩{g_num}", "title": g_title, "steps": []}
            groups.append(cur_group)
            cur_step = None
            if g_tail:
                cur_step = {
                    "id": f"⟨1⟩{g_num}.⟨2⟩1",
                    "title": g_title,
                    "body": g_tail,
                    "uses": [],
                    "lean": "",
                }
                cur_group["steps"].append(cur_step)
            continue

        # Metadata lines under a substep: "- *Uses:* ..." or "- *Lean:* `...`"
        m_uses = re.match(r"^[-*]\s+\*Uses:\*\s*(.+)$", stripped)
        if m_uses and cur_step is not None:
            items = [x.strip() for x in m_uses.group(1).split(",") if x.strip()]
            cur_step["uses"].extend(items)
            continue
        m_lean = re.match(r"^[-*]\s+\*Lean:\*\s*`?([^`]+)`?$", stripped)
        if m_lean and cur_step is not None:
            cur_step["lean"] = m_lean.group(1).strip()
            continue

        # Substep: "- 2.1. **Title**: body" or "- 2.1. body"
        m_sub = re.match(r"^[-*]\s+(\d+)\.(\d+)\.\s+(?:\*\*(.+?)\*\*:?\s*)?(.*)$", stripped)
        if m_sub and cur_group is not None:
            g_num, s_num = m_sub.group(1), m_sub.group(2)
            s_title = (m_sub.group(3) or "").strip()
            s_body = (m_sub.group(4) or "").strip()
            if not s_title:
                s_title = s_body[:72] + ("…" if len(s_body) > 72 else "")
            cur_step = {
                "id": f"⟨1⟩{g_num}.⟨2⟩{s_num}",
                "title": s_title,
                "body": s_body,
                "uses": [],
                "lean": "",
            }
            cur_group["steps"].append(cur_step)
            continue

        # Continuation text for current step or group
        if cur_step is not None:
            cur_step["body"] = (cur_step["body"] + " " + stripped).strip()
        elif cur_group is not None:
            idx = len(cur_group["steps"]) + 1
            cur_step = {
                "id": f'{cur_group["id"]}.⟨2⟩{idx}',
                "title": cur_group["title"],
                "body": stripped,
                "uses": [],
                "lean": "",
            }
            cur_group["steps"].append(cur_step)
        elif statement:
            statement = (statement + " " + stripped).strip()

    return {"provenance": provenance, "statement": statement, "groups": groups}


def _case_code(case_title: str, idx: int) -> str:
    m = re.match(r"^([A-Za-z]+\d+)\b", (case_title or "").strip())
    return m.group(1) if m else f"C{idx}"


def _format_vars(text: str, fmt: dict) -> str:
    if not isinstance(text, str):
        return text
    try:
        return text.format(**fmt)
    except Exception:
        return text


def _build_quality(root: Path, fmt: dict, all_signed: bool) -> dict | None:
    qpath = root / "quality.json"
    if not qpath.is_file():
        return None
    raw = json.loads(qpath.read_text(encoding="utf-8-sig"))
    sfx = "signed" if all_signed else "pending"

    layers = []
    for l in raw.get("layers", []):
        layers.append({
            "id": l["id"],
            "name": l["name"],
            "grade": l.get(f"grade_{sfx}", l.get("grade", "")),
            "color": l.get(f"color_{sfx}", l.get("color", "teal")),
            "summary": _format_vars(l.get(f"summary_{sfx}", l.get("summary", "")), fmt),
        })

    gates = []
    for g in raw.get("gates", []):
        gates.append({
            "gate": g["gate"],
            "name": g["name"],
            "status": g.get(f"status_{sfx}", g.get("status", "partial")),
            "good": _format_vars(g.get("good", ""), fmt),
            "improve": _format_vars(g.get(f"improve_{sfx}", g.get("improve", "")), fmt),
        })

    action_plan = []
    for a in raw.get("action_plan", []):
        done = bool(a.get("done")) or (all_signed and bool(a.get("done_when_signed")))
        action_plan.append({
            "id": a.get("id", ""),
            "priority": "Done" if done else a.get("priority", "P2"),
            "effort": a.get("effort", ""),
            "closes": a.get("closes", ""),
            "title": _format_vars(a.get("title", ""), fmt),
            "how": _format_vars(a.get("how", ""), fmt),
            "done": done,
        })

    modes = []
    for m in raw.get("modes", []):
        modes.append({
            "id": m["id"],
            "layer": m["layer"],
            "name": m["name"],
            "status": m.get(f"status_{sfx}", m.get("status", "")),
            "tone": m.get(f"tone_{sfx}", m.get("tone", "good")),
            "evidence": _format_vars(m.get("evidence", ""), fmt),
            "gap": _format_vars(m.get(f"gap_{sfx}", m.get("gap", "")), fmt),
        })

    census_rows = [
        {
            "dim": r["dim"],
            "ours": _format_vars(r["ours"], fmt),
            "benchmark": _format_vars(r["benchmark"], fmt),
        }
        for r in raw.get("census_rows", [])
    ]

    return {
        "rubric_name": raw.get("rubric_name", "survey-lean-proofs-eng-arxiv"),
        "survey_citation": raw.get("survey_citation"),
        "paradigm": raw.get("paradigm", ""),
        "tier_badge": raw.get(f"tier_badge_{sfx}", raw.get("tier_badge", "")),
        "score": raw.get(f"score_{sfx}", raw.get("score", "")),
        "headline_summary": _format_vars(raw.get(f"headline_summary_{sfx}", raw.get("headline_summary", "")), fmt),
        "layers": layers,
        "gates": gates,
        "action_plan": action_plan,
        "modes": modes,
        "census_rows": census_rows,
    }


def _build_badges(ci_level: str, quality: dict | None, all_signed: bool) -> list[dict]:
    badges = [
        {
            "tone": "green",
            "label": "Lean Checked",
            "short": "Unconditional kernel theorem (.thmInfo) using only standard axioms {propext, Classical.choice, Quot.sound}.",
        },
        {
            "tone": "slate",
            "label": "Spec SHA-Frozen",
            "short": "Statements/*.lean locked at Gate 1 and hash-verified in CI so proofs cannot silently weaken theorem signatures.",
        },
        {
            "tone": "teal",
            "label": "Non-Vacuity Witnessed",
            "short": "A compilable Lean example proves all hypotheses are jointly satisfiable (blocking vacuous truth & junk-value exploits).",
        },
        {
            "tone": "green",
            "label": "Aligned Route",
            "short": "Lean proof follows the mathematical strategy of the paper (or companion paper), distilled into clean Routine/ modules.",
        },
        {
            "tone": "indigo",
            "label": "Lean-Only Route",
            "short": "Proves the exact same formal theorem via an alternative, self-contained Lean argument rather than step-checking the manuscript's route.",
        },
        {
            "tone": "coral",
            "label": "Repaired / Diff Flagged",
            "short": "Lean intentionally formalizes a mathematically repaired version of a printed discrepancy, tracked in manuscript-edits.json.",
        },
    ]
    if ci_level == "paranoid":
        badges.append({
            "tone": "green",
            "label": "Paranoid Dual-Kernel CI",
            "short": "Verified in an offline unshare -rn network namespace with hash-locked Challenge/Solution comparator and built-in leanchecker --fresh replay.",
        })
    badges.append({
        "tone": "green" if all_signed else "amber",
        "label": "Author Signed" if all_signed else "Awaiting Human Sign-Off",
        "short": "Co-authors audited Statements/*.lean against the manuscript."
        if all_signed else "Automated & blind case-by-case checks are complete; awaiting named co-author review under Buzzard's Protocol.",
    })
    if quality:
        badges.append({
            "tone": "green" if all_signed else "gold",
            "label": f'{quality["tier_badge"]} ({quality["score"]})',
            "short": f'Evaluated against the 12-mode, 5-gate rubric of {quality.get("rubric_name", "survey-lean-proofs-eng-arxiv")}.',
        })
    return badges


def _folio_figure_relpath(root: Path, output: Path, folio: dict) -> str:
    fig = folio.get("figure") or {}
    path_str = fig.get("path")
    if not path_str:
        return ""
    src = root / path_str
    if not src.is_file():
        return ""
    data = src.read_bytes()
    name = f"folio-{hashlib.sha256(data).hexdigest()[:16]}{src.suffix}"
    dest = output / name
    if not dest.exists():
        dest.write_bytes(data)
    return name


def build_workbench(
    root: Path,
    output: Path,
    assets: Path,
    project: dict,
    materials: dict,
    built_records: list[dict],
    comparisons: dict,
    grounded_edges: list[dict],
    *,
    ci: dict | None = None,
    commit: str | None = None,
    artifact_id: int | None = None,
) -> bytes:
    """Build the v2 Audit Workbench `index.html` and write `workbench.css`/`.js`."""
    lean_stats = _scan_lean_stats(root, project)
    hosting = project.get("hosting") or {}
    folio = project.get("folio") or {}
    reader_paper = materials.get("paper") or {}
    reader_claims = materials.get("claims") or {}
    edit_summaries = materials.get("edit_summaries") or {}
    layered_cfg = materials.get("layered_graph") or {}
    short_ids_cfg = layered_cfg.get("claim_short_ids") or {}

    short_title = folio.get("short_title") or project["title"]
    repo_url = hosting.get("repository", "")
    ci_level = hosting.get("lean_ci_level", "standard")
    head_commit = (commit or (ci or {}).get("commit") or _git_short_head(root) or "")
    short_commit = head_commit[:7] if head_commit else ""

    # Determine live CI verification state from built_records / ci
    ci_verified = False
    ci_url = f"{repo_url}/actions/workflows/verify-lean.yml" if repo_url else ""
    kernels_checked: list[str] = []
    if ci:
        ci_verified = True
        ci_url = f'{repo_url}/actions/runs/{ci["run_id"]}/attempts/{ci["attempt"]}' if repo_url else ""
    for rec in built_records:
        v = rec["entry"].get("verification") or {}
        if v.get("evidence"):
            ci_verified = True
            if v.get("url"):
                ci_url = v["url"]
            if v.get("kernels_checked"):
                kernels_checked = list(v["kernels_checked"])
            if v.get("ci_level"):
                ci_level = v["ci_level"]
    if not kernels_checked:
        kernels_checked = ["lean-kernel", "leanchecker"] if ci_level == "paranoid" else ["lean-kernel"]

    if ci_verified:
        if ci_level == "paranoid":
            ci_summary = f'Paranoid CI · {" + ".join(kernels_checked)} ({short_commit})'
        else:
            ci_summary = f'CI Verified · {lean_stats["toolchain"].split(":")[-1]} ({short_commit})'
    else:
        if ci_level == "paranoid":
            ci_summary = "Paranoid CI configured (offline unshare -rn + Challenge/Solution + leanchecker --fresh)"
        else:
            ci_summary = f'Local build · {lean_stats["toolchain"]}'

    # Build claim payload records
    claims_payload = []
    total_cases = 0
    total_gap = 0
    total_defaults = 0
    defaults_ok = 0
    closed_claims = 0
    reviewed_claims = 0
    witnessed_claims = 0

    for idx, rec in enumerate(built_records, 1):
        c = rec["claim"]
        e = rec["entry"]
        w = rec["work"]
        m = rec["note"]
        rd = rec["rd"]
        audit = rec["audit"] or {}
        cid = c["id"]

        if rec["checked"]:
            closed_claims += 1
        approved = bool(e.get("verification", {}).get("approved"))
        if approved:
            reviewed_claims += 1
        witness_decl = (w.get("assembly") or {}).get("witness", "")
        if witness_decl and e.get("hypotheses"):
            witnessed_claims += 1

        comp_raw = comparisons.get(cid) or {}
        analysis = comp_raw.get("analysis") or {}
        raw_cases = analysis.get("cases") or comp_raw.get("cases") or []
        cases_out = []
        counts = {"agrees": 0, "stronger": 0, "nuance": 0, "gap": 0}
        for ci_idx, cs in enumerate(raw_cases, 1):
            kind = str(cs.get("kind", "agrees")).lower()
            pol = KIND_POLARITY.get(kind, "nuance")
            counts[pol] = counts.get(pol, 0) + 1
            cases_out.append({
                "code": _case_code(cs.get("case", ""), ci_idx),
                "case": cs.get("case", ""),
                "kind": kind,
                "polarity": pol,
                "paper": cs.get("paper", ""),
                "lean": cs.get("lean", ""),
                "why": cs.get("why", ""),
            })
        total_cases += len(cases_out)
        total_gap += counts["gap"]

        diff_spans = m.get("diff_spans") or {}
        lamport_text = e.get("steps", "")
        lamport_parsed = _parse_lamport_markdown(lamport_text) if lamport_text else {"provenance": "", "statement": "", "groups": []}

        # Pull Lean statement source
        lean_source = ""
        if e.get("sources"):
            lean_source = e["sources"][0].get("text", "")

        # Pull Statement SHA-256
        stmt_sha = ""
        if isinstance(audit.get("statement"), dict):
            stmt_sha = audit["statement"].get("sha256", "")
        if not stmt_sha and w.get("lean"):
            stmt_sha = _file_sha8(root / w["lean"])

        # Pull defaults + assessments from analysis.default_assessments
        default_assessments = analysis.get("default_assessments") or {}
        claim_defaults = []
        for d in e.get("defaults") or []:
            total_defaults += 1
            assess = default_assessments.get(d.get("id", "")) or {}
            st = assess.get("status") or d.get("status", "justified")
            if st in ("justified", "guarded", "irrelevant", "ok"):
                defaults_ok += 1
            lines_val = d.get("lines")
            line_str = f"{lines_val[0]}–{lines_val[1]}" if isinstance(lines_val, list) and len(lines_val) == 2 else str(d.get("line", ""))
            claim_defaults.append({
                "construct": d.get("construct") or d.get("operation", ""),
                "constant": d.get("constant") or d.get("declaration", ""),
                "file": d.get("file", ""),
                "line": line_str,
                "status": st,
                "explanation": assess.get("explanation") or d.get("explanation") or d.get("meaning", ""),
            })

        metrics = rec.get("proof_metrics") or {}
        loc = metrics.get("checked_lean_loc", 0)
        raw_defs = audit.get("reachable_local_defs", 0)
        raw_thms = audit.get("reachable_local_theorems", 0)
        defs_n = raw_defs if isinstance(raw_defs, int) else len(raw_defs or [])
        thms_n = raw_thms if isinstance(raw_thms, int) else len(raw_thms or [])

        basis = rec.get("basis") or "aligned"
        basis_label = (
            "Lean proves the exact same formal theorem via an alternative, self-contained proof route rather than step-checking the manuscript's argument."
            if basis == "lean"
            else "Lean proof follows the mathematical strategy of the manuscript / companion paper."
        )

        claims_payload.append({
            "id": cid,
            "short_id": (short_ids_cfg.get(cid) or {}).get("id", f"T{idx}"),
            "reference": e.get("reference", f"Claim {idx}"),
            "title": e.get("title", c.get("title", cid)),
            "page": e.get("page"),
            "paper_loc": m.get("paper_loc") or f'Page {e.get("page", "?")}',
            "proof_origin": m.get("proof_origin") or "Main paper",
            "status": e.get("status", "open"),
            "closed": rec["checked"],
            "approved": approved,
            "basis": basis,
            "basis_label": basis_label,
            "distilled": bool(rec.get("distilled")),
            "loc": loc,
            "defs": defs_n,
            "thms": thms_n,
            "witness": witness_decl,
            "witness_note": m.get("witness_note", ""),
            "plain_english": m.get("summary") or e.get("summary", ""),
            "proof_sketch": m.get("sketch", ""),
            "paper_statement": m.get("paper_statement") or c.get("source", ""),
            "paper_tex": c.get("source", ""),
            "fidelity_summary": m.get("fidelity_summary", ""),
            "route_note": m.get("route_note", ""),
            "repair_note": m.get("repair_note", ""),
            "declaration": (w.get("closure") or {}).get("declaration") or (w.get("assembly") or {}).get("declaration", ""),
            "expected": (w.get("closure") or w.get("statement_check") or {}).get("expected", ""),
            "axioms": audit.get("axioms") or [],
            "sha256": stmt_sha,
            "lean_source": lean_source,
            "defaults": claim_defaults,
            "lamport": lamport_parsed,
            "review_url": e.get("verification", {}).get("review_url", ""),
            "audit_log": e.get("audit_log", ""),
            "run_log": e.get("log", ""),
            "comparison": {
                "result": comp_raw.get("result", "match"),
                "summary": analysis.get("summary") or comp_raw.get("summary", ""),
                "issue": rd.get("issue") or comp_raw.get("issue", ""),
                "stronger_result": rd.get("stronger_result", ""),
                "paper_summary": comp_raw.get("paper_reading") or comp_raw.get("paper", ""),
                "lean_summary": comp_raw.get("lean_reading") or comp_raw.get("lean", ""),
                "counts": counts,
                "cases": cases_out,
                "paper_spans": diff_spans.get("paper", []),
                "lean_spans": diff_spans.get("lean", []),
            },
        })

    # Load manuscript-edits.json
    edits_payload = []
    edits_path = root / "manuscript-edits.json"
    if edits_path.is_file():
        edits_raw = json.loads(edits_path.read_text(encoding="utf-8-sig")).get("edits", {})
        for eid, ed in edits_raw.items():
            meta = edit_summaries.get(eid) or {}
            edits_payload.append({
                "id": eid,
                "claim": ed.get("claim", ""),
                "edition": ed.get("edition", ""),
                "location": ed.get("location", ""),
                "original": ed.get("original", ""),
                "replacement": ed.get("replacement", ""),
                "reason": ed.get("reason", ""),
                "status": ed.get("status", "Proposed"),
                "headline": meta.get("headline") or f'{eid} ({ed.get("location", "")})',
                "severity": meta.get("severity") or ed.get("claim", "Edit"),
                "tone": meta.get("tone", "amber"),
            })

    # Build Layered DAG dynamically (setup/routine/witness from reader.json + live theorem nodes + grounded uses edges)
    graph_nodes = []
    for n in layered_cfg.get("nodes", []):
        node = dict(n)
        fpath = root / node["file"] if node.get("file") else None
        if fpath and fpath.is_file():
            node["sha"] = _file_sha8(fpath)
            if node.get("layer") == "routine" and not node.get("loc"):
                node["loc"] = len(fpath.read_text(encoding="utf-8-sig").splitlines())
        graph_nodes.append(node)

    claim_id_to_node_id = {}
    for cp in claims_payload:
        cid = cp["id"]
        scfg = short_ids_cfg.get(cid) or {}
        nid = cp["short_id"]
        claim_id_to_node_id[cid] = nid
        status = (
            "verified_diff" if cp["comparison"]["result"] == "difference"
            else "verified_lean" if cp["basis"] == "lean"
            else "verified_aligned"
        )
        proof_file = ""
        w = (project.get("work") or {}).get(cid) or {}
        mod = (w.get("assembly") or {}).get("module", "")
        if mod:
            proof_file = "lean/" + mod.replace(".", "/") + ".lean"
        graph_nodes.append({
            "id": nid,
            "layer": "theorem",
            "ref": cp["reference"],
            "title": scfg.get("short_title") or cp["title"],
            "file": proof_file or w.get("lean", ""),
            "sha": (cp["sha256"] or "")[:8],
            "loc": cp["loc"],
            "status": status,
            "approved": cp["approved"],
            "diff_count": cp["comparison"]["counts"]["gap"] if cp["comparison"]["result"] == "difference" else 0,
            "nuance_count": cp["comparison"]["counts"]["nuance"],
            "stronger": bool(cp["comparison"]["stronger_result"]),
            "basis": cp["basis"],
            "summary": scfg.get("summary") or cp["plain_english"],
            "claim_id": cid,
        })

    graph_edges = list(layered_cfg.get("edges", []))
    seen_uses = set()
    for ge in grounded_edges:
        src_nid = claim_id_to_node_id.get(ge["prerequisite"])
        dst_nid = claim_id_to_node_id.get(ge["claim"])
        if src_nid and dst_nid and (src_nid, dst_nid) not in seen_uses:
            seen_uses.add((src_nid, dst_nid))
            graph_edges.append({
                "from": src_nid,
                "to": dst_nid,
                "kind": "uses",
                "reason": ge.get("reason", ""),
            })

    # Live stats & Quality Benchmark
    total_claims = len(claims_payload)
    all_signed = reviewed_claims >= total_claims and total_claims > 0
    fmt = {
        "nonempty_loc": f'{lean_stats["nonempty_loc"]:,}',
        "raw_loc": f'{lean_stats["raw_loc"]:,}',
        "lean_files": lean_stats["lean_files"],
        "stmt_raw_loc": lean_stats["stmt_raw_loc"],
        "stmt_nonempty_loc": lean_stats["stmt_nonempty_loc"],
        "reviewed": reviewed_claims,
        "total": total_claims,
        "closed": closed_claims,
        "total_cases": total_cases,
        "gap_cases": total_gap,
        "defaults_ok": defaults_ok,
        "defaults_total": total_defaults,
    }
    quality = _build_quality(root, fmt, all_signed)
    badges = _build_badges(ci_level, quality, all_signed)
    fig_src = _folio_figure_relpath(root, output, folio)

    payload = {
        "paper": {
            "short_title": short_title,
            "title": project["title"],
            "authors": project.get("authors", []),
            "edition": project.get("edition", ""),
            "citation": project.get("citation_details", ""),
            "publication": project.get("publication", ""),
            "repo_url": repo_url,
            "toolchain": lean_stats["toolchain"],
            "mathlib_rev": lean_stats["mathlib_rev"],
            "commit": short_commit,
            "ci_verified": ci_verified,
            "ci_level": ci_level,
            "ci_url": ci_url,
            "ci_summary": ci_summary,
            "kernels_checked": kernels_checked,
            "featured_claim": folio.get("featured_claim") or (claims_payload[-1]["id"] if claims_payload else ""),
            "overview": reader_paper.get("overview") or project.get("paper_overview", ""),
            "hero_blurb": reader_paper.get("hero_blurb") or folio.get("blurb", ""),
            "fig_src": fig_src,
            "fig_alt": (folio.get("figure") or {}).get("alt", ""),
            "fig_caption": reader_paper.get("fig_caption") or (folio.get("figure") or {}).get("caption", ""),
        },
        "stats": {
            "total_claims": total_claims,
            "closed_claims": closed_claims,
            "reviewed_claims": reviewed_claims,
            "witnessed_claims": witnessed_claims,
            "total_cases": total_cases,
            "gap_cases": total_gap,
            "total_defaults": total_defaults,
            "defaults_ok": defaults_ok,
            "lean_files": lean_stats["lean_files"],
            "raw_loc": lean_stats["raw_loc"],
            "nonempty_loc": lean_stats["nonempty_loc"],
            "stmt_raw_loc": lean_stats["stmt_raw_loc"],
        },
        "claims": claims_payload,
        "edits": edits_payload,
        "graph": {"nodes": graph_nodes, "edges": graph_edges},
        "quality": quality,
        "badges": badges,
    }

    # Build header byline HTML (includes exact publication & manuscript.pdf links for pages.yml checks!)
    last_names = [a.split()[-1] for a in project.get("authors", []) if a.strip()]
    if len(last_names) > 1:
        authors_short = ", ".join(last_names[:-1]) + " & " + last_names[-1]
    else:
        authors_short = last_names[0] if last_names else ""
    byline_parts = []
    if authors_short:
        pub = project.get("publication", "")
        ed = project.get("edition", "")
        if pub and ed:
            byline_parts.append(f'{escape(authors_short)} (<a href="{escape(pub, quote=True)}">{escape(ed)}</a>)')
        elif pub:
            byline_parts.append(f'{escape(authors_short)} (<a href="{escape(pub, quote=True)}">Publication</a>)')
        else:
            byline_parts.append(escape(authors_short))
    byline_parts.append('<a href="manuscript.pdf">PDF</a>')
    if lean_stats["toolchain"]:
        tc_short = lean_stats["toolchain"].split(":")[-1]
        byline_parts.append(f'Lean {escape(tc_short)}')
    if short_commit:
        if repo_url:
            byline_parts.append(f'<a href="{escape(repo_url, quote=True)}/commit/{escape(head_commit, quote=True)}" target="_blank" rel="noopener">Commit {escape(short_commit)}</a>')
        else:
            byline_parts.append(f'Commit {escape(short_commit)}')
    if ci_level == "paranoid":
        ci_lbl = "Paranoid CI ✓" if ci_verified else "Paranoid CI"
        if ci_url:
            byline_parts.append(f'<a href="{escape(ci_url, quote=True)}" target="_blank" rel="noopener">{ci_lbl}</a>')
        else:
            byline_parts.append(ci_lbl)
    if quality:
        byline_parts.append(f'Rubric: {escape(quality["rubric_name"])}')
    byline_html = " &middot; ".join(byline_parts)

    # Copy workbench static assets
    for name in ("workbench.css", "workbench.js"):
        src = assets / name
        dst = output / name
        dst.write_bytes(src.read_bytes())

    template = (assets / "workbench.html").read_text(encoding="utf-8-sig")
    packed = json.dumps(payload, ensure_ascii=False).replace("<", r"\u003c")
    html = (
        template
        .replace("__PAGE_TITLE__", escape(f"{short_title} — Proof Atlas Audit Workbench"))
        .replace("__SHORT_TITLE__", escape(short_title))
        .replace("__BYLINE_HTML__", byline_html)
        .replace("__DATA__", packed)
    )
    return html.encode("utf-8")
