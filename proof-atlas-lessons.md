# Proof Atlas Skill Lessons & Issues Journal

Running log of issues, edge cases, and improvement opportunities encountered while applying `../proof-atlas/build-proof-atlas` (`v0.11.0`) to `arXiv:1008.4895v2` (*LIFO-Backpressure Achieves Near Optimal Utility-Delay Tradeoff*).

---

## 2026-11-26 — Initial Setup & Inventory

### 1. `import_arxiv.py` regex fails on nested braces in `\newtheorem`
* **Where:** `build-proof-atlas/scripts/import_arxiv.py` L198 (`r"\\newtheorem\*?\{([\w*-]+)\}(?:\[[^\]]+\])?\{([^{}]+)\}"`).
* **Symptom:** `paper/qla-lifo-tech2-v5.tex` L93 declares `\newtheorem{thm}{\textbf{Theorem}}` (very common in older IEEEtran papers). Because `[^{}]+` forbids nested braces, `import_arxiv.py` does not recognize `thm` as a Theorem environment.
* **Workaround:** Created `project.json` manually with `"environments": ["claim", "coro", "lemma", "main", "prop", "thm"]`.
* **Suggested fix:** Strip simple formatting wrappers (`\textbf{...}`, `\emph{...}`, `\textnormal{...}`) or parse one level of balanced braces in `\newtheorem` declarations.

### 2. `atlas.py` `HEADLINE_KINDS` misclassifies `\begin{thm}` as Supporting
* **Where:** `build-proof-atlas/scripts/atlas.py` L19 (`HEADLINE_KINDS = frozenset({"theorem", "corollary", "proposition"})`) and L367 (`claim["kind"].casefold() in HEADLINE_KINDS`).
* **Symptom:** Because `inventory()` sets `kind` to the raw LaTeX environment name (`thm`), all four theorems default to `supporting` rather than `headline` unless `"headline": true` is overridden per claim in `reader.json`.
* **Workaround:** Set `"headline": true` explicitly for all four claims in `reader.json`.
* **Suggested fix:** Include common aliases (`thm`, `cor`, `coro`, `prop`, `main`) in `HEADLINE_KINDS`, or map `\newtheorem` environments to their canonical printed kind in `project.json`.

### 3. `import_arxiv.py` requires a brand-new directory
* **Where:** `build-proof-atlas/scripts/import_arxiv.py` L244–245 (`if target.exists(): parser.error(...)`).
* **Symptom:** When starting a Proof Atlas inside an already-initialized Git repository that already contains `paper/` (`.tex` + `.pdf`) and `references/`, `import_arxiv.py` cannot bootstrap into `.` in place.
* **Workaround:** Authored `project.json`, `reader.json`, and `import-review.json` directly against `paper/qla-lifo-tech2-v5.tex` and `paper/1008.4895v2.pdf`.
* **Suggested fix:** Add an `--init-existing` or `atlas.py init` command that hashes existing local `.tex` and `.pdf` files into `project.json` in an existing repo root.

### 4. Detached proofs skipped by `inventory()` when a brief commentary paragraph intervenes
* **Where:** `build-proof-atlas/scripts/atlas.py` L104 (`re.match(r"\s*\\begin\{proof\}.*?\\end\{proof\}", clean[stop:], re.S)`).
* **Symptom:** In `paper/qla-lifo-tech2-v5.tex`, Theorem 4 (`\end{thm}` at L629) is followed by a 3-line summary paragraph (L631–633) before `\begin{proof} (Theorem \ref{thm:qlalifo_delay})` at L635. As a result, `inventory()` sets `adjacent_proof: False` and truncates the Paper-view excerpt before the proof. Similarly, Theorem 1's proof is in Appendix A (L1019–1080) and Theorems 2–3's proofs are in bundled companion papers under `references/`.
* **Suggested fix:** Support an optional `proof_location` / `proof_excerpt` (or explicit line range / companion TeX path) in `reader.json` so detached proofs and companion-paper proofs appear cleanly in the Paper view.

### 5. Optional PDF text/render tools not checked upfront
* **Where:** `import_arxiv.py` L115–126 (`pdftotext` / `fitz`), and `SKILL.md` Folio hero figure cropping.
* **Symptom:** When `poppler-utils` (`pdftotext`/`pdftoppm`), `python3-fitz` (PyMuPDF), and `Pillow` are absent in a minimal Linux container, `import_arxiv.py` silently returns empty page lists without warning why page matching failed, and cropping Folio hero figures is unavailable until those packages are installed. (User subsequently installed `poppler-utils`, `python3-fitz`, and `python3-pil`, after which Fig. 1 cropped cleanly.)
* **Suggested fix:** Emit an explicit warning in `import_arxiv.py` when neither `pdftotext` nor `fitz` is found, and document the recommended system packages (`poppler-utils`, `python3-fitz`, `python3-pil`) in a prerequisites section of `SKILL.md`.

### 6. `atlas.atomic()` creates files with `0600` permissions
* **Where:** `build-proof-atlas/scripts/atlas.py` L68–71 (`NamedTemporaryFile` + `os.replace`).
* **Symptom:** Generated files such as `.github/workflows/verify-lean.yml` and `dist/*.html` are created with mode `0600` rather than respecting the user's `umask` (`0644`). Harmless for Git blobs (which normalize to `0644`), but awkward when serving `dist/` via another user/webserver.
* **Suggested fix:** Set readable permissions (e.g., `os.chmod(temp.name, 0o644)`) or apply the current `umask` before `os.replace`.

### 7. Gate 1 `--statement-only` has no batch mode CLI
* **Where:** `build-proof-atlas/scripts/audit_lean.py`.
* **Symptom:** Auditing 4 statements sequentially via `audit_lean.py --statement-only` pays the full Lake/Mathlib startup cost per claim (~35s × 4 ≈ 2.3 min), even though `audit_lean.py` already implements `audit_batch` internally for `verify_ci.py`.
* **Suggested fix:** Expose a `--batch` / multi-claim CLI mode for `--statement-only` Gate 1 audits so all `Statements/` claims can be fingerprinted in a single Lake invocation.

### 8. `atlas.py manifest` LaTeX snippet leaves Unicode symbols unescaped and flags classical `noncomputable` definitions as caveats
* **Where:** `build-proof-atlas/scripts/atlas.py` (`manifest` LaTeX formatter).
* **Symptom:** (a) Free-text strings from `stronger_result` (such as `(Ω, μ)`) are emitted verbatim into `\paragraph{Formal Verification and Scope.}` without escaping Greek Unicode characters for `pdflatex`. (b) On classical real-analysis / probability theorems (with no algorithmic/computability claim), every `noncomputable` helper (`Real.log`, `Real.sqrt`, Bochner integral, `Set.Finite.toFinset`) is listed verbosely under "Active formalization scope caveats", drowning out the genuine mathematical caveats.
* **Suggested fix:** Escape common Unicode math symbols (`Ω`, `μ`, `≤`, `≥`, `λ`, etc.) in the LaTeX emitter, and either suppress `noncomputable` from the prose caveat list when no `weaker conclusion` / algorithmic conflict is flagged or summarize it concisely (e.g., "uses classical real/measure definitions").

### 9. `atlas.py assemble --audit` runs sequential `audit_lean.audit()` per claim instead of `audit_lean.audit_batch()`
* **Where:** `build-proof-atlas/scripts/atlas.py` L2591–2624 (`for item in claim_reports: audit_data = audit_lean.audit(...)`).
* **Symptom:** Auditing `k` assembled claims via `atlas.py assemble . --audit` invokes `lake --no-cache build Assembly ...` `k` separate times (~35s × `k`), even though `audit_lean.audit_batch` already exists and builds the union of targets once before checking all claims in one pass.
* **Suggested fix:** Collect all claim audit specs for a package inside `assemble()` and invoke `audit_lean.audit_batch()` once per package.

### 10. `audit_lean.py` `HYPOTHESES_QUERY` reorders `Prop` typeclass binders without a `--print-witness-type` helper
* **Where:** `build-proof-atlas/scripts/audit_lean.py` L628–658 (`HYPOTHESES_QUERY` / `proofAtlasPath`).
* **Symptom:** For statements with `Prop`-valued typeclass binders like `[IsProbabilityMeasure μ]` interleaved among data binders, `proofAtlasPath` silently moves `IsProbabilityMeasure μ` out of the `∃` binder prefix and into the trailing `∧` conjuncts (`facts`). Authors writing a `--witness` theorem in `Examples/` cannot know the exact derived witness signature upfront without reading `audit_lean.py`'s source or failing an audit round-trip first.
* **Suggested fix:** Add an `--emit-witness-type` (or `--statement-only` output field `expected_witness_proposition`) so Gate 1 immediately records the exact Lean proposition required for `--witness` in `evidence/stmt-*.json`.

### 11. `SKILL.md` lacks guidance for atomic Git commits at logical proof milestones
* **Where:** `build-proof-atlas/SKILL.md` ("Work on a claim" / hosting & delivery sections).
* **Symptom:** `SKILL.md` instructs the agent to checkpoint `project.json` frequently and commit before `hosting.py --publish`, but does not instruct the agent to make small, atomic Git commits at each logical unit of work (e.g., Gate 1 statement lock, each closed or conditional theorem, each `Routine/` foundation module, each witness/distillation pass). As a result, multiple theorems and helper libraries accumulate uncommitted until the author explicitly asks or a handoff occurs.
* **Suggested fix:** Add a standing Git-hygiene guideline in `SKILL.md` ("Commit atomically at each audited milestone: after Gate 1, after each `Routine/` milestone, and after each newly closed or conditionally audited claim + its receipt") so commit history stays granular, reviewable, and bisect-friendly.

### 12. Missing context-budget handoff protocol (~40% halt / persist / publish / emit `/clear` resume prompt)
* **Where:** `build-proof-atlas/SKILL.md` (session continuity / resume workflow) and `build-proof-atlas/scripts/atlas.py`.
* **Symptom:** Paper-wide Lean 4 formalizations routinely span multiple sessions, and reasoning quality degrades when a single session climbs past ~40–50% context window usage (especially after several Lake builds, long error traces, and large proof files). Currently, `SKILL.md` assumes an unbroken session until the authorized stopping point or an impasse; it has no built-in protocol for proactively halting near ~40% context, saving durable state (`HANDOFF.md` + `project.json`), making atomic commits, pushing/publishing the latest GitHub Pages snapshot so progress is visible online, and emitting a ready-to-paste resume prompt for the user's `/clear` workflow.
* **Workaround:** Added a standing "40% Context Handoff Rule" in project-local `AGENTS.md` and manually authored `HANDOFF.md` + copy-paste resume prompts at each ~40% boundary.
* **Suggested fixes:**
  1. **Skill protocol in `SKILL.md`:** Document a first-class **Context-Budget Handoff** pattern (default target ~40% context at the nearest clean milestone boundary): finish/audit the current atomic unit, commit atomically, refresh `atlas.py build` + `atlas.py manifest`, optionally run `hosting.py PROJECT --publish` so live GitHub Pages reflects the latest milestone, write/update `HANDOFF.md`, and emit a succinct copy-paste prompt ready for `/clear` or a fresh session.
  2. **Deterministic `atlas.py handoff PROJECT` helper:** Add a subcommand that reads `project.json`, `atlas.py review-work`, `HANDOFF.md` (if present), and recent `git log` to deterministically render a compact resume brief and copy-paste continuation prompt (avoiding drift or omitted invariants like "do not edit `Statements/`").
  3. **Context-preserving delegation:** Pair the ~40% `/clear` handoff with delegating heavy per-claim tactic/build loops to isolated subagents (`invoke_subagent`) so the coordinator context stays lean and only absorbs distilled summaries and audited receipts.
