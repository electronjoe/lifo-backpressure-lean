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

### 13. `review-work` counts unconditionally closed claims with `"result": "difference"` under `"open"`
* **Where:** `build-proof-atlas/scripts/atlas.py` (`review-work` summary classification).
* **Symptom:** When a theorem is unconditionally proved, witnessed, and distilled in Lean (`status: "closed"`, `unconditional: true`, `distilled: true`), but intentionally formalizes a mathematically repaired statement (e.g., Theorem 4 `thm:qlalifo_delay`, where the printed manuscript has a missing `λ̃_j > 0` guard, reversed interval endpoints, and an off-by-`δ_max + 1` constant error under Eq. (3)) so `comparisons.json` records `"result": "difference"` for author review, `review-work` reports `unconditionally_closed: 3, open: 1` (lumping it into `"open"` alongside unproved theorems).
* **Suggested fix:** Add a distinct summary counter such as `closed_with_difference` (or `proved_pending_statement_review`) so dashboards and `review-work` distinguish unconditionally proved repaired statements from genuinely unproved claims.

---

## 2026-11-26 — Paranoid CI, Repo Front-Door Hygiene & Release Polish

### 14. `verify_ci.py` breaks in `"paranoid"` mode on Lean `v4.30.0`–`v4.34.1` because `leanprover/lean4checker` was archived and merged into Lean 4 as `leanchecker`
* **Where:** `build-proof-atlas/scripts/verify_ci.py` (`install_paranoid_tools`, L507–L544, and `run_lean4checker`, L315–L330).
* **Symptom:** `leanprover/lean4checker` was archived on 2026-03-25 (last tag `v4.29.0-rc8`) after being merged directly into the Lean 4 toolchain as `leanchecker` starting in `v4.28.0`. Because `verify_ci.py` only skips `lean4checker` cloning when `toolchain >= v4.35.0` (`supports_lake_paranoid`), running `--install-paranoid-tools` on any Lean toolchain in `v4.30.0`–`v4.34.1` (such as our `v4.33.1`) fails trying to `git clone --branch v4.33.1 https://github.com/leanprover/lean4checker.git`, and `run_lean4checker` never checks for the built-in `leanchecker` binary in the toolchain sysroot.
* **Workaround:** Patched `tools/proof-atlas/scripts/verify_ci.py` locally with `supports_builtin_leanchecker` (`>= v4.28.0`) and `_find_builtin_leanchecker` (`lake env lean --print-prefix` → `bin/leanchecker`) so paranoid CI runs built-in `leanchecker --fresh Solution` cleanly.
* **Suggested fix:** Upstream `supports_builtin_leanchecker` and built-in `leanchecker --fresh` detection into `build-proof-atlas/scripts/verify_ci.py` (preferring built-in `leanchecker` for `>= v4.28.0` and falling back to external `lean4checker` only for `< v4.28.0`).

### 15. Skill omits repository front-door hygiene (`README.md`, `LICENSE`, `CITATION.cff`, AI-use disclosure, release tag)
* **Where:** `build-proof-atlas/SKILL.md` ("Verification manifest and manuscript scope synchronization" and "Start a project" / GitHub publishing sections).
* **Symptom:** Proof Atlas generates a rich `dist/VERIFICATION.md` and GitHub Pages explorer, but never instructs updating the repository's root `README.md` (with CI badges, Verification Manifest summary, live Proof Atlas URL, exact `lake build` reproduction steps, documented manuscript discrepancies, and explicit AI-use/model provenance disclosure), nor creating `LICENSE` and `CITATION.cff`, nor tagging an immutable release (e.g., `v1.0.0`) after CI passes. Compared against the empirical best practices of `survey-lean-proofs-eng-arxiv` (Gate 5 / Mode #12), a completed Proof Atlas repo can look opaque/stale on its GitHub landing page despite passing every internal audit.
* **Workaround:** Manually upgraded `README.md`, added `LICENSE` (MIT) and `CITATION.cff`, and tagged `v1.0.0` once paranoid CI passed.
* **Suggested fix:** Add a `readme` / `release-check` checklist (or template helper) to `SKILL.md` / `atlas.py` so GitHub-published repositories automatically surface the Verification Manifest, Proof Atlas link, reproduction commands, AI-use disclosure, `LICENSE`, `CITATION.cff`, and an immutable release tag.

### 16. `"paranoid"` CI and `Challenge`/`Solution` harness setup are not proactively surfaced on `thorough` completion
* **Where:** `build-proof-atlas/SKILL.md` (L54–L56), `hosting.py`, and `atlas.py challenge`.
* **Symptom:** `hosting.py --lean-ci` defaults `lean_ci_level` to `"standard"` even for `thorough` paper-wide formalizations, and `atlas.py challenge` neither adds nor warns clearly when `[[lean_lib]] name = "Challenge"` and `[[lean_lib]] name = "Solution"` are missing from `lakefile.toml` (which silently downgrades `verify_ci.py` to the standalone elaboration fallback without cross-environment `.olean` comparison). Also, editing `lakefile.toml` invalidates `checked_inputs` hashes and requires a manual `atlas.py assemble . --audit` re-run.
* **Workaround:** Manually added `Challenge` and `Solution` `[[lean_lib]]` stanzas to `lean/lakefile.toml`, ran `hosting.py . --lean-ci-level paranoid`, re-ran `atlas.py assemble . --audit`, and generated `lean/Challenge.lean` + `lean/Solution.lean` via `atlas.py challenge .`.
* **Suggested fix:** Recommend `paranoid` CI automatically when initializing or completing a `thorough` profile project, add a `--configure-lakefile` flag to `atlas.py challenge`, and document the exact ordering (`lakefile.toml` → `assemble --audit` → `challenge`) in `SKILL.md`.

### 17. Local `dist/VERIFICATION.md` is not synced with GitHub Actions CI receipts (and `pages.yml` skips `atlas.py manifest`)
* **Where:** `build-proof-atlas/references/github-pages.yml` (copied to `.github/workflows/pages.yml`) and `atlas.py manifest`.
* **Symptom:** Even after `Verify Lean claims` succeeds on `HEAD`, `pages.yml` runs `atlas.py build . --ci-receipt ...` (updating the HTML explorer/dashboard) but does **not** run `atlas.py manifest . --ci-receipt ... --commit ...`, so `dist/VERIFICATION.md` on disk and in the deployed Pages artifact continues to report `Machine verified (CI): 0/4` and *"no GitHub Actions CI verification receipt is attached to this revision"*.
* **Suggested fix:** Run `python3 tools/proof-atlas/scripts/atlas.py manifest . "${args[@]}"` immediately after `atlas.py build` in `pages.yml` so the deployed `VERIFICATION.md` reflects live CI verification receipts automatically.

---

## 2026-11-26 — UI/UX & Published Site Audit (Reference Prototype: `uiux-demos/v2-audit-workbench.html`)

### 18. `explorer.js` Lamport renderer dumps standard Markdown as raw unformatted text
* **Where:** `build-proof-atlas/assets/explorer.js` L215–223 (`c.steps.split(/\n\s*\n/)` + `^\*\*(.*?)\*\*` + `rich()`).
* **Symptom:** `lamport/*.md` files written in standard Markdown (`#` headings, `*Provenance:...*`, indented `- 1.1.` nested bullet steps, inline backticked math) are dumped verbatim with literal `#`, `*`, `- 1.1.`, and backticks inside flat `<p>` tags, making the Lamport Proof tab hard to scan and visually broken compared to TINA's hierarchical `⟨1⟩1.⟨2⟩1` collapsible proof trees (`lamport.js`).
* **Reference prototype:** `uiux-demos/v2-audit-workbench.html` (Claim Inspector → Lamport Proof renders collapsible KaTeX `⟨1⟩i` / `⟨1⟩i.⟨2⟩j` step cards with provenance, `Uses`, and Lean declaration links).
* **Suggested fix:** Parse structured Lamport trees (`⟨1⟩i` collapsible `<details>` groups with `⟨1⟩i.⟨2⟩j` substeps, `Uses` links, Lean lemma refs, and KaTeX `$$...$$`/`$...$` rendering) or ship a lightweight Markdown+KaTeX renderer in `explorer.js` and enforce KaTeX `$...$` formatting in `lamport/*.md`.

### 19. `reader.json` silently omits `"sketch"` and renders raw ASCII math in `"summary"`
* **Where:** `build-proof-atlas/assets/explorer.js` L150–152 and `build-proof-atlas/scripts/atlas.py` (`build` / `review-work`).
* **Symptom:** When `reader.json` defines `"summary"` without `"sketch"` (as occurred on all 4 claims in `lifo-backpressure-lean`), the Plain English view renders `"A proof sketch has yet to be recorded."` on every claim. Furthermore, `"summary"` strings written with raw ASCII math (`gamma_V^*`, `delta_max`, `V^{log V}`) without `$...$` delimiters bypass KaTeX completely and read like dense raw code rather than Plain English.
* **Reference prototype:** `uiux-demos/v2-audit-workbench.html` (Plain English & High-Level Proof Sketch with KaTeX math for all 4 theorems).
* **Suggested fix:** Require (or warn in `atlas.py build` and `review-work`) that every headline claim in `reader.json` has both a genuinely accessible `summary` (Plain English with KaTeX `$...$` math) and a non-empty `sketch` (3–5 sentence high-level proof roadmap).

### 20. `explorer.html` embeds a 230-word `What the badges mean` prose wall on the home page
* **Where:** `build-proof-atlas/assets/explorer.html` L8–10 (`<aside class="badge-note">`).
* **Symptom:** Every generated Proof Atlas landing page injects two dense paragraphs explaining 10 badge types—including 6+ badges that do not even appear in the repository (e.g., `Proof supplied outside manuscript`, `Step-verified`, `Conditional`, `Subproofs checked`, `Multi-kernel / Comparator`)—directly above the Contents list, adding severe incidental complexity for first-time readers.
* **Reference prototype:** `uiux-demos/v2-audit-workbench.html` (instant hover/focus tooltips on every badge + compact `ⓘ Badge & Polarity Key` modal).
* **Suggested fix:** Remove the inline prose wall. Attach concise hover/focus tooltips directly to each rendered badge pill, and tuck the full glossary into a compact collapsible drawer or modal.

### 21. Dependency graph omits model assumptions, `Routine/` theory, witnesses, and status tokens
* **Where:** `build-proof-atlas/assets/graph.js` L119–131 and `build-proof-atlas/scripts/atlas.py` (`inventory()` / `dependencies`).
* **Symptom:** Because `atlas.py` only inventories `\begin{thm}` (and theorem-like) environments, `lifo-backpressure-lean`'s dependency graph renders just 4 theorem boxes and 3 arrows—omitting frozen model definitions/assumptions (`NetworkModel`, `η`-slackness, Eq. (3) queue dynamics, polyhedral growth, `LifoQueueRealization`), shared `Routine/` foundations (`MarkovMixing`, `BackpressureDrift`), and non-vacuity witnesses (`Examples/`). Moreover, `graph.js` only draws a plain relation dot (`selected`/`ancestor`/`descendant`) on each node rather than showing verification status, Gate-1 SHA freeze locks, author-review status, proof basis (`aligned` vs. `lean`-only route), or semantic-difference counts (as TINA's `app.js` does).
* **Reference prototype:** `uiux-demos/v2-audit-workbench.html` (Layered DAG tab: 13 nodes across 4 toggleable layers `uses` / `setup` / `routine` / `witness`, TINA-style status tokens `✓`, `🔒`, `⑂`, `★`, `👁`, `nΔ`, click-to-trace closure, and node inspector).
* **Suggested fix:** Support optional layered node kinds (`setup` / `routine` / `theorem` / `witness`) and typed edge filters with clean defaults (Theorems + key Assumptions visible by default; `Routine/` & Witnesses toggleable), and render compact status tokens directly on graph nodes.

### 22. `review_web.py` lacks semantic diff highlighting between Paper and Lean readings
* **Where:** `build-proof-atlas/scripts/review_web.py` L59–79 & L151–155 (`analysis_panel` and `columns`).
* **Symptom:** `comparisons.json` already records rich obligation-level semantic classifications (`agrees`, `stronger`, `other form`, `chosen reading`, `restriction`, `added hypothesis`, `weaker conclusion`) and `manuscript-edits.json` records exact TeX patches, yet `review_web.py` renders the comparison as a monochrome text table separated from two unannotated prose blocks (`Paper theorem` vs. `What Lean proved`).
* **Reference prototype:** `uiux-demos/v2-audit-workbench.html` (Semantic Diff & Edits tab: color-coded clause highlights linking Paper and Lean readings, polarity filter chips across all 37 obligations, and red/green LaTeX patch cards).
* **Suggested fix:** Color-code semantic polarities (`green` agrees, `teal` Lean proves more, `amber` minor normalization/typo fix, `coral` gap/added assumption/looser constant), support synchronized span annotations linking clauses across Paper and Lean readings, and display linked `manuscript-edits.json` entries inline as red/green TeX patches.

### 23. Missing upfront Five-Gate Quality Benchmark with explicit "What's Good vs. Needs Work" & Action Plan
* **Where:** `build-proof-atlas/assets/explorer.html` & `explorer.js` (landing & navigation IA).
* **Symptom:** The landing page provides no upfront, research-grounded quality scorecard (citing `survey-lean-proofs-eng-arxiv`'s Five-Gate / 12-Mode rubric), and summary tables that combine strengths and gaps into a single prose column fail to tell readers at a glance what is already verified vs. what concrete steps would raise proof quality.
* **Reference prototype:** `uiux-demos/v2-audit-workbench.html` (Overview & Quality tab: Five-Gate table split into `✓ What's Already Good` vs. `→ What Needs Work / How to Improve`, prioritized P1–P3 Action Plan, stacked 12-Mode bar, and imperative `→ How to Improve` column in the 12-Mode ledger; single clean tab bar without redundant role toggles).
* **Suggested fix:** Surface a compact, research-grounded **Five-Gate & 12-Mode Quality Benchmark** (citing `electronjoe/survey-lean-proofs-eng-arxiv`) directly on Overview with explicit split `Good` vs. `Needs Work` columns and an actionable improvement checklist.

### 24. Direction-ambiguous semantic tokens, buried Lean-only proof routes, understated `0/4` sign-off, and buried manuscript edits
* **Where:** `build-proof-atlas/scripts/review_web.py`, `comparisons.json` (`kind`), `manuscript-edits.json`, and `explorer.html` / `explorer.js`.
* **Symptom:** Four high-impact trust UX gaps surfaced during interactive prototype review:
  1. **Direction-ambiguous polarity tokens:** Raw `comparisons.json` kinds (`restriction`, `weaker conclusion`, `added hypothesis`, `other form`, `chosen reading`) do not indicate *direction* (`Lean vs. Paper`)—a reader cannot tell at a glance whether Lean is weaker than the paper or vice versa, or what `added hypothesis` entails.
  2. **Buried `basis: "lean"` proof-route divergence:** When Lean proves a theorem via a completely different mathematical route than the manuscript/companion paper (e.g., Theorem 2 via Doeblin mixing + Poisson's equation instead of renewal stopping times), burying that tag inside the Lean tab hides both an audit caveat (the paper's written proof route was not step-checked) and an author opportunity (a shorter self-contained alternative proof).
  3. **Understated `0/4` human sign-off:** Treating `0/4 Author Reviewed` as a small KPI caption understates the critical trust boundary: until a human author inspects `Statements/*.lean` and critical differing clauses, a green Lean build only proves the formal code compiles—not that it matches the paper.
  4. **Buried recommended manuscript edits:** Hiding `manuscript-edits.json` behind a separate top-bar link obscures one of the highest-value outputs of formalization (concrete LaTeX fixes for genuine mathematical bugs/typos in the paper).
* **Reference prototype:** `uiux-demos/v2-audit-workbench.html` implements all four fixes directly on `Overview & Quality`, `Results Ledger`, `Semantic Diff & Edits`, and `Claim Inspector`.
* **Suggested fix:** (a) Render every comparison token with explicit direction and hover tooltip (`↓ Lean proves looser constant`, `+ Lean adds missing assumption`, `↘ Lean narrows domain`, `↑ Lean proves MORE than paper`, `≈ Equivalent form in Lean`, `✎ Lean fixes ambiguity / typo`, `✓ Lean = Paper`); (b) surface a dedicated front-door callout on Overview & Theorem cards whenever a theorem uses a `lean`-only proof route; (c) display an unmistakable top-of-page **Human Co-Author Sign-Off Pending** banner whenever `author_reviewed < total`, linking directly to critical clauses and `Statements/*.lean`; and (d) display a scannable **Recommended Paper Edits** card grid directly on Overview with expandable red/green LaTeX diffs.

### 25. `pages.yml` header link assertion forbids extra anchor attributes on the publication link
* **Where:** `build-proof-atlas/references/github-pages.yml` (copied to `.github/workflows/pages.yml` L57–60).
* **Symptom:** The publication self-check splits `index.html` on `</h1>` and `</p>` and asserts the literal substring `f'<a href="{escape(publication, quote=True)}">'` — which fails if a custom or v2 template adds `target="_blank" rel="noopener"` or CSS classes to the publication anchor tag.
* **Workaround:** Emitted the bare `<a href="...">` form in `tools/proof-atlas/scripts/workbench.py`'s header byline so it passes the existing `pages.yml` check untouched.
* **Suggested fix:** Match `href="..."` with an HTML parser or regex (`<a\b[^>]*\bhref="..."`) in `github-pages.yml` so templates can safely include `rel="noopener"` or styling attributes.

### 26. Upstream-ready v2 Audit Workbench schema validated on live `lifo-backpressure-lean` data
* **Where:** `tools/proof-atlas/scripts/workbench.py`, `tools/proof-atlas/assets/workbench.{html,css,js}`, `reader.json`, `quality.json`, `lamport/*.md`.
* **Symptom / Finding:** Implementing the live data-driven v2 Audit Workbench cleanly inside `tools/proof-atlas/` validated the exact minimal schema needed for upstreaming to `../proof-atlas/build-proof-atlas`:
  1. `reader.json` carries optional paper-agnostic UX enrichments (`paper.{overview,hero_blurb,fig_caption}`, per-claim `sketch`/`paper_loc`/`proof_origin`/`paper_statement`/`fidelity_summary`/`route_note`/`repair_note`/`diff_spans`, `edit_summaries`, and `layered_graph.{claim_short_ids,nodes,edges}`) with zero breakage to existing `atlas.py` or `author_review.py`.
  2. `quality.json` carries the optional Five-Gate / 12-Mode rubric and Action Plan with `{nonempty_loc}` / `{reviewed}` / `{total}` template variables resolved dynamically from live repo stats and CI receipts.
  3. `lamport/*.md` with standard KaTeX `$...$` math and indented `- 1.1. **Title**: ...` + `- *Uses:*` / `- *Lean:*` lines parses cleanly into collapsible `⟨1⟩i` / `⟨1⟩i.⟨2⟩j` cards while remaining readable as plain GitHub Markdown.
  4. Truncating rich KaTeX text for overview cards must be math-delimiter-aware (`truncateRich`) so slices never cut inside `$...$` expressions.
* **Suggested fix:** Upstream `workbench.py` + `workbench.{html,css,js}` and document the optional `reader.json` enrichments and `quality.json` schema in `build-proof-atlas/SKILL.md`.
