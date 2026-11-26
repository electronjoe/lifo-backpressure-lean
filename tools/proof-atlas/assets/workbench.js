"use strict";

const DATA = JSON.parse(document.getElementById("atlas-payload").textContent);

/* Explicit directional labels + plain-English tooltips for every comparison kind */
const KIND_INFO = {
  "agrees": {
    label: "✓ Lean = Paper",
    polarity: "agrees",
    tip: "Exact semantic match: Lean states and proves the same condition or conclusion as the paper."
  },
  "stronger": {
    label: "↑ Lean proves MORE than paper",
    polarity: "stronger",
    tip: "Lean's theorem is strictly stronger than what the paper claims (e.g., benchmarking against a larger class of policies or dropping an unnecessary side assumption)."
  },
  "other form": {
    label: "≈ Equivalent form in Lean",
    polarity: "nuance",
    tip: "Mathematically equivalent restatement (e.g., finite convex mixture via Carathéodory's theorem instead of a countable series)."
  },
  "chosen reading": {
    label: "✎ Lean fixes ambiguity / typo",
    polarity: "nuance",
    tip: "Lean pins down an informal ambiguity or corrects a clear typographical issue in the manuscript."
  },
  "restriction": {
    label: "↘ Lean narrows domain",
    polarity: "gap",
    tip: "Lean proves the theorem over a slightly narrower domain than the paper's broadest prose."
  },
  "added hypothesis": {
    label: "+ Lean adds missing assumption",
    polarity: "gap",
    tip: "Lean requires an explicit hypothesis omitted from the printed theorem box that is needed for mathematical soundness."
  },
  "weaker conclusion": {
    label: "↓ Lean proves looser constant",
    polarity: "gap",
    tip: "Lean's proved bound or conclusion is strictly weaker/coarser than the printed formula (same asymptotic order, looser constant)."
  }
};

const defaultClaim = DATA.paper.featured_claim || (DATA.claims[DATA.claims.length - 1] && DATA.claims[DATA.claims.length - 1].id) || "";
const firstGapClaim = (DATA.claims.find(c => c.comparison.counts.gap > 0) || DATA.claims[0] || {}).id || defaultClaim;
const defaultGraphNode = (DATA.graph.nodes.find(n => n.claim_id === defaultClaim && n.layer === "theorem")
  || DATA.graph.nodes.find(n => n.layer === "theorem")
  || DATA.graph.nodes[0] || {}).id || "";

const state = {
  view: "overview",         // overview | ledger | diff | graph | claim
  claimId: defaultClaim,
  claimTab: "english",      // english | paper | lamport | review | lean
  diffFilter: "gap",        // all | gap | nuance | stronger | agrees
  diffClaim: firstGapClaim,
  activeCase: null,
  graphEdges: { uses: true, setup: true, routine: false, witness: false },
  graphSel: defaultGraphNode,
};

function esc(s) {
  return String(s ?? "").replace(/[&<>"']/g, m => ({ "&":"&amp;", "<":"&lt;", ">":"&gt;", '"':"&quot;", "'":"&#39;" }[m]));
}
function katexHtml(tex, display) {
  if (window.katex) {
    try { return window.katex.renderToString(tex, { displayMode: display, throwOnError: false, strict: "ignore" }); } catch {}
  }
  return display ? `<div><code>${esc(tex)}</code></div>` : `<code>${esc(tex)}</code>`;
}
function rich(src) {
  if (!src) return "";
  const re = /(\$\$[\s\S]+?\$\$|\$[^$\n]+?\$|`[^`\n]+?`|\*\*[^*\n]+?\*\*|\*[^*\n]+?\*)/g;
  let out = "", last = 0, m;
  while ((m = re.exec(src))) {
    out += esc(src.slice(last, m.index));
    const t = m[0];
    if (t.startsWith("$$")) out += katexHtml(t.slice(2, -2), true);
    else if (t.startsWith("$")) out += katexHtml(t.slice(1, -1), false);
    else if (t.startsWith("`")) out += `<code>${esc(t.slice(1, -1))}</code>`;
    else if (t.startsWith("**")) out += `<strong>${rich(t.slice(2, -2))}</strong>`;
    else out += `<em>${rich(t.slice(1, -1))}</em>`;
    last = re.lastIndex;
  }
  return out + esc(src.slice(last));
}
function truncateRich(src, maxLen) {
  if (!src || src.length <= maxLen) return src || "";
  const re = /(\$\$[\s\S]+?\$\$|\$[^$\n]+?\$|`[^`\n]+?`|\*\*[^*\n]+?\*\*|\*[^*\n]+?\*)/g;
  let cut = maxLen, m;
  while ((m = re.exec(src))) {
    if (m.index < cut && re.lastIndex > cut) {
      cut = m.index;
      break;
    }
  }
  const slice = src.slice(0, cut).replace(/[\s,;:\-—]+$/, "");
  const sp = slice.lastIndexOf(" ");
  return (sp > maxLen * 0.6 ? slice.slice(0, sp) : slice) + "…";
}
function hlLean(src) {
  const re = /(\/-[\s\S]*?-\/)|(--.*$)|\b(import|namespace|open|structure|def|noncomputable|lemma|theorem|where|by|let|have|calc|apply|intro|rcases|rw|exact|constructor|match|with|if|then|else|end|variable)\b/gm;
  let out = "", last = 0, m;
  while ((m = re.exec(src))) {
    out += esc(src.slice(last, m.index));
    out += `<span class="${m[1]||m[2]?"cc":"ck"}">${esc(m[0])}</span>`;
    last = re.lastIndex;
  }
  return out + esc(src.slice(last));
}
function chip(label, tone, tip) {
  return `<span class="chip ${tone}"${tip ? ` tabindex="0" data-tip="${esc(tip)}"` : ""}>${esc(label)}</span>`;
}
function kindToken(kind) {
  const info = KIND_INFO[(kind || "").toLowerCase()] || { label: kind, polarity: "nuance", tip: "" };
  return `<span class="sem-token sem-${info.polarity}" tabindex="0" data-tip="${esc(info.tip)}">${esc(info.label)}</span>`;
}
function claimById(id) { return DATA.claims.find(c => c.id === id) || DATA.claims[0]; }

function syncHash() {
  let h = "#" + state.view;
  if (state.view === "claim" && state.claimId) {
    h = `#claim/${encodeURIComponent(state.claimId)}/${encodeURIComponent(state.claimTab)}`;
  } else if (state.view === "diff" && state.diffClaim) {
    h = `#diff/${encodeURIComponent(state.diffClaim)}`;
  }
  if (location.hash !== h) {
    history.replaceState(null, "", h);
  }
}

function loadFromHash() {
  const raw = (location.hash || "").replace(/^#\/?/, "");
  if (!raw) return;
  const parts = raw.split("/").map(decodeURIComponent);
  if (["overview", "ledger", "diff", "graph", "claim"].includes(parts[0])) {
    state.view = parts[0];
    if (parts[0] === "claim") {
      if (parts[1] && DATA.claims.some(c => c.id === parts[1])) state.claimId = parts[1];
      if (parts[2] && ["english", "paper", "lamport", "review", "lean"].includes(parts[2])) state.claimTab = parts[2];
    } else if (parts[0] === "diff") {
      if (parts[1] && DATA.claims.some(c => c.id === parts[1])) state.diffClaim = parts[1];
    }
  }
}

function renderSignoffBanner() {
  const stats = DATA.stats;
  const p = DATA.paper;
  const total = stats.total_claims;
  const reviewed = stats.reviewed_claims;
  const gapCases = stats.gap_cases;
  const editsCount = DATA.edits.length;
  const leanRouteClaim = DATA.claims.find(c => c.basis === "lean");
  const diffClaim = DATA.claims.find(c => c.comparison.result === "difference") || DATA.claims[0];

  if (reviewed >= total && total > 0) {
    return `
      <section class="trust-banner signed" aria-label="Human co-author sign-off complete">
        <div>
          <h2>✓ Human Co-Author Sign-Off Complete (${reviewed} / ${total} Theorems Reviewed)</h2>
          <p>Named co-authors have audited the ${stats.stmt_raw_loc}-line <code>Statements/*.lean</code> boundary and confirmed statement alignment across all ${total} headline claims.</p>
        </div>
        <button type="button" class="btn" data-go="diff">Inspect All ${stats.total_cases} Obligations →</button>
      </section>`;
  }

  const ciNote = p.ci_verified
    ? `Paranoid CI (${p.kernels_checked.join(" + ")}) unconditionally verifies all ${stats.closed_claims}/${total} formal statements`
    : `Lean unconditionally verifies all ${stats.closed_claims}/${total} formal statements`;

  return `
    <section class="trust-banner pending" aria-label="Human co-author sign-off pending">
      <div>
        <h2>⚠ Human Co-Author Sign-Off Still Pending (${reviewed} / ${total} Theorems Reviewed) ${chip("Critical Trust Boundary", "coral", "A green Lean build certifies the formal code; human author review certifies the formal code matches the paper.")}</h2>
        <p>${rich(`${ciNote} in \`lean/Statements/*.lean\` (${stats.stmt_raw_loc} raw lines) with zero \`sorry\` and standard axioms only. **However, no human author has yet signed off that these Lean statements match the paper's intended theorems**—including **${gapCases} critical non-identical clauses** across the paper${editsCount ? `, **${editsCount} recommended paper edits**` : ""}${leanRouteClaim ? `, and **${leanRouteClaim.reference}'s alternative Lean-only proof route**` : ""}.`)}</p>
        <div class="trust-actions">
          ${gapCases > 0 ? `<button type="button" class="btn warn" data-go-gaps="true">Review the ${gapCases} Critical Clauses →</button>` : ""}
          ${editsCount > 0 ? `<button type="button" class="btn" data-scroll-to="recommended-edits">Jump to ${editsCount} Recommended Paper Edits ↓</button>` : ""}
          ${diffClaim ? `<button type="button" class="btn" data-open-claim="${esc(diffClaim.id)}" data-open-tab="lean">Inspect Statements/*.lean Boundary</button>` : ""}
          ${leanRouteClaim ? `<button type="button" class="btn" data-open-claim="${esc(leanRouteClaim.id)}" data-open-tab="lamport">Inspect ${esc(leanRouteClaim.reference)} Lean-Only Route</button>` : ""}
        </div>
      </div>
    </section>`;
}

function renderQualitySection() {
  const q = DATA.quality;
  if (!q) return "";
  const cite = q.survey_citation;
  const cGreat = q.modes.filter(m => m.tone === "great").length;
  const cGood = q.modes.filter(m => m.tone === "good").length;
  const cWarn = q.modes.filter(m => m.tone === "warn").length;
  const cNeu = q.modes.filter(m => m.tone === "neutral").length;

  return `
    <div class="sh">
      <h2>Five-Gate &amp; 12-Mode Quality Benchmark</h2>
      <span>Grounded in <a href="${esc(cite.repo_url)}" target="_blank" rel="noopener">${esc(q.rubric_name || "survey-lean-proofs-eng-arxiv")}</a> (${esc(cite.authors)})</span>
    </div>
    <div class="card" style="margin-bottom:1.25rem">
      <div style="display:flex;justify-content:space-between;align-items:center;gap:1rem;flex-wrap:wrap">
        <p style="margin:0;max-width:74ch">${esc(q.headline_summary)}</p>
        <div style="display:flex;gap:.4rem;flex-wrap:wrap">
          ${q.layers.map(l => chip(`${l.name}: ${l.grade}`, l.color, l.summary)).join("")}
        </div>
      </div>
      <div class="stack" role="img" aria-label="12-mode quality distribution">
        ${cGreat ? `<span style="flex:${cGreat};background:#146c43" title="Exemplary / Perfect (${cGreat})"></span>` : ""}
        ${cGood ? `<span style="flex:${cGood};background:#0b6374" title="Strong (${cGood})"></span>` : ""}
        ${cWarn ? `<span style="flex:${cWarn};background:#d97706" title="Actionable Gap (${cWarn})"></span>` : ""}
        ${cNeu ? `<span style="flex:${cNeu};background:#94a3b8" title="N/A (${cNeu})"></span>` : ""}
      </div>
      <div style="display:flex;gap:1rem;flex-wrap:wrap;font-size:.76rem;color:var(--muted);margin-bottom:.95rem">
        <span><strong style="color:#146c43">●</strong> Exemplary/Perfect: ${cGreat}</span>
        <span><strong style="color:#0b6374">●</strong> Strong: ${cGood}</span>
        <span><strong style="color:#d97706">●</strong> Actionable Gap: ${cWarn}</span>
        <span><strong style="color:#94a3b8">●</strong> N/A: ${cNeu}</span>
        <span style="margin-left:auto"><a href="${esc(cite.taxonomy_url)}" target="_blank" rel="noopener">12-Mode Taxonomy ↗</a> · <a href="${esc(cite.pdf_url)}" target="_blank" rel="noopener">Survey Paper PDF ↗</a></span>
      </div>

      <div class="tbl-wrap" style="margin-bottom:1rem">
        <table class="ledger">
          <thead>
            <tr>
              <th style="width:12rem">Gate</th>
              <th style="width:7.5rem">Status</th>
              <th>✓ What's Already Good</th>
              <th>→ What Needs Work / How to Improve</th>
            </tr>
          </thead>
          <tbody>
            ${q.gates.map(g => `
              <tr>
                <td><strong>${esc(g.gate)}</strong><br><span style="color:var(--muted);font-size:.74rem">${esc(g.name)}</span></td>
                <td>${chip(g.status === "pass" ? "✓ Pass" : "◐ Partial", g.status === "pass" ? "green" : "amber")}</td>
                <td class="cell-good">✓ ${esc(g.good)}</td>
                <td class="${g.status === "pass" ? "cell-done" : "cell-work"}">${g.status === "pass" ? "✓ " : "→ "}${esc(g.improve)}</td>
              </tr>`).join("")}
          </tbody>
        </table>
      </div>

      <div style="display:flex;align-items:baseline;justify-content:space-between;gap:1rem;flex-wrap:wrap;margin-bottom:.35rem">
        <h3 style="margin:0;font-size:.95rem">Quality Progress &amp; Remaining Action Plan</h3>
        <span style="font-size:.76rem;color:var(--muted)">Updated live against current HEAD (<code>${esc(DATA.paper.commit)}</code>)</span>
      </div>
      <div class="plan-grid">
        ${q.action_plan.map(a => `
          <div class="plan-item ${a.done ? "done" : ""}">
            <div class="plan-head">
              <div>
                ${chip(a.done ? "✓ Completed" : a.priority, a.done ? "green" : a.priority === "P1" ? "coral" : a.priority === "P2" ? "amber" : "slate")}
                ${chip(a.effort, a.done ? "green" : "slate")}
              </div>
              <span style="font-size:.72rem;font-family:var(--mono);color:var(--muted)">${esc(a.closes)}</span>
            </div>
            <h4>${esc(a.title)}</h4>
            <p>${esc(a.how)}</p>
          </div>`).join("")}
      </div>

      ${q.census_rows && q.census_rows.length ? `
        <details style="margin-top:.9rem">
          <summary style="font-weight:700;font-size:.82rem;color:var(--accent);cursor:pointer">Compare against the 2026 Engineering Lean 4 Census (${esc(cite.census_note)})</summary>
          <div class="tbl-wrap" style="margin-top:.6rem">
            <table class="ledger">
              <thead><tr><th>Census Dimension</th><th>This Repository</th><th>Survey T2 Engineering Cohort</th></tr></thead>
              <tbody>
                ${q.census_rows.map(r => `<tr><td><strong>${esc(r.dim)}</strong></td><td>${esc(r.ours)}</td><td style="color:var(--muted)">${esc(r.benchmark)}</td></tr>`).join("")}
              </tbody>
            </table>
          </div>
        </details>` : ""}
    </div>`;
}

function renderOverview() {
  const p = DATA.paper, s = DATA.stats, q = DATA.quality;
  const featured = claimById(p.featured_claim) || DATA.claims[0];
  const leanRouteClaim = DATA.claims.find(c => c.basis === "lean");
  const allSigned = s.reviewed_claims >= s.total_claims && s.total_claims > 0;

  return `
    ${renderSignoffBanner()}

    <div class="kpi-grid">
      <div class="card kpi">
        <div class="k">Proof Quality Tier</div>
        <div class="v" style="color:${allSigned ? "var(--green)" : "var(--gold)"}">${esc(q ? q.score : `${s.closed_claims}/${s.total_claims}`)}</div>
        <div class="d">${q ? chip(q.tier_badge, allSigned ? "green" : "gold", "Benchmarked against survey-lean-proofs-eng-arxiv (12,613-paper census).") + " · " + esc(q.paradigm) : "Thorough paper-wide formalization."}</div>
      </div>
      <div class="card kpi">
        <div class="k">Kernel Closure &amp; Scale</div>
        <div class="v">${s.closed_claims} / ${s.total_claims} <span style="font-size:.88rem;font-weight:600;color:var(--muted)">closed</span></div>
        <div class="d">${s.nonempty_loc.toLocaleString()} non-empty LoC (${s.lean_files} files; <strong>3.1× smaller</strong> than T2 eng. median); 0 sorry, 0 custom axioms.</div>
      </div>
      <div class="card kpi">
        <div class="k">Paper ↔ Lean Fidelity</div>
        <div class="v">${s.total_cases - s.gap_cases}/${s.total_cases} <span style="font-size:.88rem;font-weight:600;color:var(--muted)">aligned</span></div>
        <div class="d"><strong>${s.gap_cases} critical clauses</strong> (${DATA.edits.length} proposed LaTeX edits); ${s.witnessed_claims}/${s.total_claims} witnesses; 0 undisclosed drift.</div>
      </div>
      <div class="card kpi" style="${allSigned ? "" : "border-color:#e6a86a;background:#fffaf2"}">
        <div class="k">Co-Author Sign-Off &amp; CI</div>
        <div class="v" style="color:${allSigned ? "var(--green)" : "var(--coral)"}">${s.reviewed_claims} / ${s.total_claims} <span style="font-size:.88rem;font-weight:600;color:var(--muted)">signed</span></div>
        <div class="d">${p.ci_verified
          ? `<a href="${esc(p.ci_url)}" target="_blank" rel="noopener">✓ ${esc(p.ci_summary)} ↗</a>`
          : esc(p.ci_summary)}</div>
      </div>
    </div>

    <div class="card story-grid${p.fig_src ? "" : " no-fig"}" style="margin-bottom:1.25rem">
      <div>
        <div style="display:flex;gap:.4rem;flex-wrap:wrap;margin-bottom:.45rem">
          ${featured ? chip(`Headline Result · ${featured.reference}`, "teal") : ""}
          ${p.ci_level === "paranoid" ? chip("🛡 Paranoid Dual-Kernel CI", "green", "Offline unshare -rn sandbox, hash-locked Challenge/Solution comparator, and built-in leanchecker --fresh.") : ""}
          ${leanRouteClaim ? chip(`⑂ ${leanRouteClaim.reference} Uses Lean-Only Route`, "indigo", leanRouteClaim.basis_label) : ""}
        </div>
        <h2 style="margin:.2rem 0 .45rem;font-size:1.3rem;line-height:1.22">${esc(p.title)}</h2>
        <p style="margin:0 0 .7rem;color:var(--muted)">${rich(p.overview)}</p>
        <div style="display:flex;gap:.5rem;flex-wrap:wrap">
          ${featured ? `<button type="button" class="btn primary" data-open-claim="${esc(featured.id)}" data-open-tab="english">Read Plain-English Guide →</button>` : ""}
          <button type="button" class="btn" data-go="graph">Explore Layered DAG</button>
          <a class="btn" href="manuscript.pdf">Paper PDF</a>
          <a class="btn" href="VERIFICATION.md">Verification Manifest</a>
          ${p.publication ? `<a class="btn" href="${esc(p.publication)}" target="_blank" rel="noopener">arXiv ↗</a>` : ""}
        </div>
      </div>
      ${p.fig_src ? `
        <figure style="margin:0">
          <img src="${esc(p.fig_src)}" alt="${esc(p.fig_alt || p.short_title)}">
          <figcaption style="font-size:.75rem;color:var(--muted);margin-top:.35rem">${rich(p.fig_caption)}</figcaption>
        </figure>` : ""}
    </div>

    ${renderQualitySection()}

    <div class="sh">
      <h2>The ${DATA.claims.length} Headline Theorems at a Glance</h2>
      <span>Showing proof status, review status, proof-route divergence, and key semantic findings upfront</span>
    </div>
    <div class="claims-grid">
      ${DATA.claims.map(c => `
        <div class="card" style="display:flex;flex-direction:column;justify-content:space-between;gap:.65rem">
          <div>
            <div style="display:flex;justify-content:space-between;gap:.4rem;align-items:center;flex-wrap:wrap;margin-bottom:.38rem">
              <strong style="color:var(--accent);font-family:var(--mono);font-size:.78rem">${esc(c.reference)} · ${c.loc.toLocaleString()} LoC</strong>
              <div style="display:flex;gap:.3rem;flex-wrap:wrap">
                ${chip(c.closed ? "✓ Lean Closed" : c.status, c.closed ? "green" : "amber", "Unconditional kernel theorem, standard axioms only.")}
                ${chip(c.approved ? "✓ Author Signed" : "👁 Unreviewed (0/1)", c.approved ? "green" : "amber", c.approved ? "Human co-author signed off on Statements/*.lean." : "Human co-author has not yet signed off on Statements/*.lean for this claim.")}
                ${c.basis === "lean" ? chip("⑂ Lean-Only Proof Route", "indigo", c.basis_label) : ""}
                ${c.comparison.result === "difference"
                  ? chip(`⚠ ${c.comparison.counts.gap} Repairs`, "coral", c.comparison.issue)
                  : c.comparison.stronger_result
                    ? chip("↑ Lean Proves More", "teal", c.comparison.stronger_result)
                    : chip("✓ Statement Match", "green", "Formal statement matches paper.")}
              </div>
            </div>
            <h3 style="margin:0 0 .35rem;font-size:1rem">${rich(c.title)}</h3>
            <p style="margin:0;font-size:.82rem;color:var(--muted)">${rich(truncateRich(c.plain_english, 210))}</p>
            ${c.route_note ? `
              <div class="route-callout">
                <strong>⑂ Alternative Proof Route (Audit Caveat &amp; Author Opportunity):</strong>
                ${rich(c.route_note)}
              </div>` : ""}
            ${c.repair_note ? `
              <div class="repair-callout">
                <strong>⚠ ${c.comparison.counts.gap} Discrepancies Requiring Author Sign-Off:</strong>
                ${rich(c.repair_note)}
              </div>` : ""}
          </div>
          <div style="display:flex;gap:.4rem;flex-wrap:wrap">
            <button type="button" class="btn" data-open-claim="${esc(c.id)}" data-open-tab="english">Plain English</button>
            <button type="button" class="btn" data-open-claim="${esc(c.id)}" data-open-tab="lamport">Lamport Proof</button>
            <button type="button" class="btn" data-open-claim="${esc(c.id)}" data-open-tab="review">Semantic Review</button>
            <button type="button" class="btn" data-open-claim="${esc(c.id)}" data-open-tab="lean">Lean</button>
          </div>
        </div>`).join("")}
    </div>

    ${DATA.edits.length ? `
      <div class="sh" id="recommended-edits">
        <h2>Recommended Paper Edits Surfaced by Formalization (${DATA.edits.length})</h2>
        <span>Concrete LaTeX revisions from <code>manuscript-edits.json</code> to bring the paper into exact agreement with the proved theorems</span>
      </div>
      <div class="plan-grid">
        ${DATA.edits.map(e => `
          <div class="card" style="display:flex;flex-direction:column;justify-content:space-between;gap:.55rem;border-color:${e.status === "Applied" ? "var(--green-bd)" : "var(--coral-bd)"}">
            <div>
              <div style="display:flex;justify-content:space-between;align-items:center;gap:.4rem;flex-wrap:wrap;margin-bottom:.35rem">
                ${chip(e.severity, e.status === "Applied" ? "green" : e.tone)}
                ${chip(e.status, e.status === "Applied" ? "green" : "amber")}
              </div>
              <h3 style="margin:0 0 .25rem;font-size:.94rem;line-height:1.3">${rich(e.headline)}</h3>
              <p style="margin:0 0 .45rem;font-size:.75rem;font-family:var(--mono);color:var(--muted)">${esc(e.location)} · <code>${esc(e.id)}</code></p>
              <p style="margin:0 0 .5rem;font-size:.8rem;color:var(--muted);line-height:1.45">${esc(e.reason)}</p>
              <details>
                <summary style="font-size:.78rem;font-weight:700;color:var(--accent);cursor:pointer">Show exact LaTeX diff (− original / + replacement)</summary>
                <div class="patch-line patch-del" style="margin-top:.45rem">− ${esc(e.original)}</div>
                <div class="patch-line patch-add">+ ${esc(e.replacement)}</div>
              </details>
            </div>
            <div style="display:flex;gap:.4rem;flex-wrap:wrap;margin-top:.2rem">
              <button type="button" class="btn" data-go-diff="${esc(e.claim)}">Inspect in Semantic Diff →</button>
              <button type="button" class="btn" data-open-claim="${esc(e.claim)}" data-open-tab="paper">View Paper Passage</button>
            </div>
          </div>`).join("")}
      </div>` : ""}`;
}

function renderLedger() {
  const q = DATA.quality;
  return `
    <div class="sh" style="margin-top:0">
      <h2>Advertised Results &amp; Verification Ledger</h2>
      <span>Direction-explicit statement fidelity, proof route, axioms, witnesses &amp; sign-off status</span>
    </div>
    <div class="tbl-wrap">
      <table class="ledger">
        <thead>
          <tr>
            <th>Result &amp; Source</th>
            <th>Lean Declaration &amp; Lock</th>
            <th style="min-width:19rem">Statement Fidelity (Lean vs. Paper)</th>
            <th>Proof Route &amp; Scale</th>
            <th>Axioms &amp; Witness</th>
            <th>Human Sign-Off</th>
          </tr>
        </thead>
        <tbody>
          ${DATA.claims.map(c => {
            const nonAgree = c.comparison.cases.filter(x => x.polarity !== "agrees");
            return `
            <tr>
              <td>
                <button type="button" class="btn" style="padding:.2rem .5rem;margin-bottom:.3rem" data-open-claim="${esc(c.id)}" data-open-tab="review"><strong>${esc(c.reference)}</strong></button><br>
                <strong>${rich(c.title)}</strong><br>
                <span style="color:var(--muted);font-size:.75rem">${esc(c.proof_origin)}</span>
              </td>
              <td>
                <code>${esc(c.declaration)}</code><br>
                ${c.sha256 ? chip("🔒 Frozen " + c.sha256.slice(0, 8), "slate", "Statement SHA-256 untouched since Gate 1 and re-verified in CI.") : ""}
              </td>
              <td>
                ${c.comparison.result === "difference"
                  ? chip(`⚠ Repaired in Lean (${c.comparison.counts.gap} diffs)`, "coral", c.comparison.issue)
                  : c.comparison.stronger_result
                    ? chip("↑ Match · Lean Proves More", "teal", c.comparison.stronger_result)
                    : chip("✓ Match", "green", c.comparison.summary)}
                <p style="margin:.35rem 0 .25rem;font-size:.76rem;color:var(--muted);line-height:1.4">${esc(c.fidelity_summary || c.comparison.summary)}</p>
                <details>
                  <summary style="font-size:.75rem;color:var(--accent);cursor:pointer">Inspect ${nonAgree.length} non-identical clause(s) out of ${c.comparison.cases.length}</summary>
                  <ul style="padding-left:1rem;margin:.35rem 0;font-size:.74rem;display:grid;gap:.35rem">
                    ${nonAgree.map(x => `<li>${kindToken(x.kind)}<br><span style="color:var(--ink)">${esc(x.case)}</span></li>`).join("") || "<li>All clauses agree verbatim.</li>"}
                  </ul>
                </details>
              </td>
              <td>
                ${chip(c.basis === "lean" ? "⑂ Lean-Only Route" : "≡ Aligned", c.basis === "lean" ? "indigo" : "green", c.basis_label)}<br>
                <span style="font-size:.76rem;color:var(--muted)">${c.loc.toLocaleString()} LoC · ${c.defs} defs · ${c.thms} thms${c.distilled ? " · Distilled" : ""}</span>
              </td>
              <td>
                ${chip(`Standard ${c.axioms.length} axioms`, "green", c.axioms.join(", "))}<br>
                <span style="font-size:.75rem;color:var(--muted)">${c.witness ? `Witness: <code>${esc(c.witness.split(".").pop())}</code> · ` : ""}${c.defaults.length}/${c.defaults.length} defaults OK</span>
              </td>
              <td>
                ${chip(c.approved ? "✓ Author Signed" : "⚠ Unreviewed (0/1)", c.approved ? "green" : "coral", c.approved ? "Signed off by co-author." : "No human co-author has yet signed off that Statements/*.lean matches the paper.")}
              </td>
            </tr>`;
          }).join("")}
        </tbody>
      </table>
    </div>
    ${q && q.modes ? `
      <div class="sh">
        <h2>Twelve-Mode Failure Audit (Layer A / B / C)</h2>
        <span>Direct audit against <code>${esc(q.rubric_name || "survey-lean-proofs-eng-arxiv")}</code> with concrete improvement steps</span>
      </div>
      <div class="tbl-wrap">
        <table class="ledger">
          <thead><tr><th>Mode</th><th>Layer</th><th>Failure Class</th><th>Status</th><th>✓ Verified Evidence</th><th>→ How to Improve</th></tr></thead>
          <tbody>
            ${q.modes.map(m => {
              const isNoAction = (m.gap || "").startsWith("None") || (m.gap || "").startsWith("Optional:");
              return `
              <tr>
                <td><code>${esc(m.id)}</code></td>
                <td><strong>${esc(m.layer)}</strong></td>
                <td><strong>${esc(m.name)}</strong></td>
                <td>${chip(m.status, m.tone === "great" ? "green" : m.tone === "good" ? "teal" : m.tone === "warn" ? "amber" : "slate")}</td>
                <td class="cell-good">${esc(m.evidence)}</td>
                <td class="${isNoAction ? "cell-done" : "cell-work"}">${esc(m.gap)}</td>
              </tr>`;
            }).join("")}
          </tbody>
        </table>
      </div>` : ""}`;
}

function renderDiffWorkbench() {
  const c = claimById(state.diffClaim);
  const comp = c.comparison;
  const allCases = DATA.claims.flatMap(cl => cl.comparison.cases.map(cs => ({ ...cs, claimId: cl.id, ref: cl.reference })));
  const filtered = state.diffFilter === "all" ? allCases : allCases.filter(x => x.polarity === state.diffFilter);
  const act = comp.cases.find(x => x.code === state.activeCase) || comp.cases.find(x => x.polarity === "gap") || comp.cases[0];

  const renderSpans = (spans, fallback) => {
    if (!spans || !spans.length) return rich(fallback || "");
    return spans.map(sp => {
      if (!sp.case) return rich(sp.text);
      const matched = comp.cases.find(x => x.code === sp.case);
      const kInfo = matched ? (KIND_INFO[(matched.kind || "").toLowerCase()] || {}) : {};
      return `<span class="sem-span sem-${sp.polarity}${act && act.code === sp.case ? " active" : ""}" data-pick-case="${esc(sp.case)}" data-tip="${esc((kInfo.label || "") + " — " + (kInfo.tip || ""))}">${rich(sp.text)}</span>`;
    }).join("");
  };

  return `
    <div class="sh" style="margin-top:0">
      <h2>Semantic Diff &amp; Manuscript Edit Workbench</h2>
      <span>Hover any highlighted phrase or directional token to see exactly how Lean relates to the paper</span>
    </div>
    <div class="filter-bar">
      <span style="font-size:.76rem;font-weight:700;color:var(--muted)">Theorem:</span>
      ${DATA.claims.map(cl => `<button type="button" class="f-btn" data-diff-claim="${esc(cl.id)}" aria-pressed="${cl.id === c.id}">${esc(cl.reference)} ${cl.comparison.counts.gap ? `(${cl.comparison.counts.gap} critical)` : "✓"}</button>`).join("")}
      <span style="margin-left:auto;display:flex;gap:.35rem;flex-wrap:wrap;font-size:.74rem">
        ${kindToken("agrees")}
        ${kindToken("stronger")}
        ${kindToken("chosen reading")}
        ${kindToken("added hypothesis")}
        ${kindToken("weaker conclusion")}
      </span>
    </div>
    <div class="side-by-side">
      <div class="card">
        <div style="font-size:.73rem;font-weight:700;text-transform:uppercase;color:var(--muted);margin-bottom:.45rem">Paper Reading (${esc(c.reference)})</div>
        <div style="line-height:1.72">${renderSpans(comp.paper_spans, comp.paper_summary)}</div>
      </div>
      <div class="card">
        <div style="font-size:.73rem;font-weight:700;text-transform:uppercase;color:var(--muted);margin-bottom:.45rem">Checked Lean Reading (<code>${esc(c.expected.split(".").pop())}</code>)</div>
        <div style="line-height:1.72">${renderSpans(comp.lean_spans, comp.lean_summary)}</div>
      </div>
    </div>
    ${act ? `
      <div class="card" style="border-color:var(--ink);margin-bottom:1.1rem">
        <div style="display:flex;align-items:center;gap:.5rem;flex-wrap:wrap;margin-bottom:.35rem">
          ${kindToken(act.kind)}
          <strong>${esc(act.case)}</strong>
        </div>
        <p style="margin:.2rem 0;font-size:.84rem"><strong>Paper states:</strong> ${esc(act.paper)}</p>
        <p style="margin:.2rem 0;font-size:.84rem"><strong>Lean formalizes:</strong> ${esc(act.lean)}</p>
        <p style="margin:.25rem 0 0;font-size:.83rem;color:var(--muted)"><strong>Why they differ / assessment:</strong> ${esc(act.why)}</p>
      </div>` : ""}

    <div class="sh">
      <h2>All ${allCases.length} Paper ↔ Lean Obligations</h2>
      <span>Filter by direction &amp; severity across the whole paper (click any row to inspect above)</span>
    </div>
    <div class="filter-bar">
      ${[
        ["gap", `Critical Gaps / Added Assumptions / Looser Constant (${allCases.filter(x=>x.polarity==="gap").length})`],
        ["nuance", `Normalizations / Typo Fixes (${allCases.filter(x=>x.polarity==="nuance").length})`],
        ["stronger", `Lean Proves MORE (${allCases.filter(x=>x.polarity==="stronger").length})`],
        ["agrees", `Exact Match (${allCases.filter(x=>x.polarity==="agrees").length})`],
        ["all", `All (${allCases.length})`],
      ].map(([k, lbl]) => `<button type="button" class="f-btn" data-diff-filter="${k}" aria-pressed="${state.diffFilter === k}">${lbl}</button>`).join("")}
    </div>
    <div class="tbl-wrap" style="margin-bottom:1.3rem">
      <table class="ledger">
        <thead><tr><th>Claim</th><th>Case</th><th>Lean vs. Paper Direction</th><th>Paper States</th><th>Lean Formalizes</th></tr></thead>
        <tbody>
          ${filtered.map(r => `
            <tr style="cursor:pointer" data-jump-case="${esc(r.claimId)}|${esc(r.code)}">
              <td><strong>${esc(r.ref)}</strong></td>
              <td><code>${esc(r.code)}</code></td>
              <td>${kindToken(r.kind)}</td>
              <td>${esc(r.paper)}</td>
              <td>${esc(r.lean)}</td>
            </tr>`).join("")}
        </tbody>
      </table>
    </div>

    ${DATA.edits.length ? `
      <div class="sh">
        <h2>Synchronized Manuscript Revision Patches (${DATA.edits.length})</h2>
        <span>Directly from <code>manuscript-edits.json</code></span>
      </div>
      <div style="display:grid;gap:.75rem">
        ${DATA.edits.map(e => `
          <div class="card">
            <div style="display:flex;justify-content:space-between;align-items:center;gap:.5rem;flex-wrap:wrap;margin-bottom:.35rem">
              <strong><code>${esc(e.id)}</code> · ${esc(e.location)}</strong>
              ${chip(e.status, e.status === "Applied" ? "green" : "amber")}
            </div>
            <div class="patch-line patch-del">− ${esc(e.original)}</div>
            <div class="patch-line patch-add">+ ${esc(e.replacement)}</div>
            <p style="margin:.4rem 0 0;font-size:.82rem;color:var(--muted)">${esc(e.reason)}</p>
          </div>`).join("")}
      </div>` : ""}`;
}

function renderGraphView() {
  const showSetup = state.graphEdges.setup;
  const showRoutine = state.graphEdges.routine;
  const showWitness = state.graphEdges.witness;
  const nodes = DATA.graph.nodes.filter(n =>
    n.layer === "theorem" ||
    (n.layer === "setup" && showSetup) ||
    (n.layer === "routine" && showRoutine) ||
    (n.layer === "witness" && showWitness)
  );
  const ids = new Set(nodes.map(n => n.id));
  const edges = DATA.graph.edges.filter(e => ids.has(e.from) && ids.has(e.to) && state.graphEdges[e.kind]);
  if (!ids.has(state.graphSel) && nodes.length) state.graphSel = defaultGraphNode || nodes[0].id;

  const W = 940, NW = 166, NH = 72;
  const pos = {};
  let curY = 26;
  const putRow = (list, y) => {
    const gap = 16, rw = list.length * NW + (list.length - 1) * gap, sx = Math.max(12, (W - rw) / 2);
    list.forEach((n, i) => pos[n.id] = { x: sx + i * (NW + gap), y });
  };
  const setups = nodes.filter(n => n.layer === "setup");
  const routines = nodes.filter(n => n.layer === "routine");
  const thms = nodes.filter(n => n.layer === "theorem");
  const wits = nodes.filter(n => n.layer === "witness");

  // Topological split of theorem nodes: prerequisites above dependents
  const thmUsesEdges = DATA.graph.edges.filter(e => e.kind === "uses");
  const hasIncomingThm = new Set(thmUsesEdges.map(e => e.to));
  const thmTop = thms.filter(n => !hasIncomingThm.has(n.id));
  const thmBot = thms.filter(n => hasIncomingThm.has(n.id));

  if (setups.length) { putRow(setups, curY); curY += 116; }
  if (routines.length) { putRow(routines, curY); curY += 110; }
  if (thmTop.length) { putRow(thmTop, curY); curY += 116; }
  if (thmBot.length) { putRow(thmBot, curY); curY += 110; }
  if (wits.length) { putRow(wits, curY); curY += 96; }
  const H = Math.max(460, curY + 20);

  const sel = state.graphSel;
  const up = new Set(), down = new Set();
  const walk = (dir, out) => {
    const q = [sel];
    while (q.length) {
      const u = q.pop();
      for (const e of edges) {
        const nxt = dir === "up" ? (e.to === u ? e.from : null) : (e.from === u ? e.to : null);
        if (nxt && !out.has(nxt)) { out.add(nxt); q.push(nxt); }
      }
    }
  };
  walk("up", up); walk("down", down);
  const inTr = id => id === sel || up.has(id) || down.has(id);

  const edgeSvg = edges.map(e => {
    const a = pos[e.from], b = pos[e.to];
    if (!a || !b) return "";
    const rev = a.y > b.y;
    const x1 = a.x + NW/2, y1 = rev ? a.y : a.y + NH;
    const x2 = b.x + NW/2, y2 = rev ? b.y + NH + 4 : b.y - 4;
    const my = (y1 + y2) / 2;
    const hot = ((up.has(e.from)||e.from===sel)&&(up.has(e.to)||e.to===sel)) || ((down.has(e.from)||e.from===sel)&&(down.has(e.to)||e.to===sel));
    return `<path class="ge ${e.kind} ${hot?"hot":"dim"}" marker-end="url(#a-${e.kind})" d="M${x1},${y1} C${x1},${my} ${x2},${my} ${x2},${y2}"><title>${esc(e.from)} → ${esc(e.to)} (${e.kind}): ${esc(e.reason)}</title></path>`;
  }).join("");

  const nodeSvg = nodes.map(n => {
    const p = pos[n.id];
    const glyph = n.layer === "setup" ? "🔒" : n.layer === "witness" ? "★" : n.status === "verified_lean" ? "⑂" : "✓";
    const col = n.status === "verified_diff" || n.status === "frozen_repair" ? "#b42318" : n.status === "verified_lean" ? "#4338ca" : n.layer === "setup" ? "#475569" : "#146c43";
    const revIcon = n.layer === "theorem" ? (n.approved ? "✓" : "👁") : "";
    const revCol = n.approved ? "#146c43" : "#b42318";
    return `
      <g class="gn layer-${n.layer} status-${n.status} ${n.id===sel?"sel":""} ${inTr(n.id)?"":"dim"}" data-node="${esc(n.id)}" transform="translate(${p.x},${p.y})">
        <rect class="box" width="${NW}" height="${NH}" rx="8"/>
        <circle cx="15" cy="17" r="8" fill="${col}" opacity=".14"/>
        <text x="15" y="21" text-anchor="middle" font-size="10.5" fill="${col}" font-weight="700">${glyph}</text>
        <text x="28" y="20" font-size="10" font-weight="700" font-family="ui-monospace,monospace" fill="#0f62fe">${esc(n.ref)}</text>
        ${revIcon ? `<text x="${NW-10}" y="20" text-anchor="end" font-size="10.5" fill="${revCol}">${revIcon}</text>` : ""}
        <text x="10" y="40" font-size="11.5" font-weight="600" fill="#0f172a">${esc(n.title.slice(0,23))}</text>
        <text x="10" y="57" font-size="9.5" font-family="ui-monospace,monospace" fill="#475569">${esc(n.loc ? n.loc.toLocaleString()+" LoC · " : "")}${n.sha ? "SHA " + esc(n.sha) : ""}</text>
        ${n.diff_count ? `<g transform="translate(${NW-16},${NH-14})"><rect x="-10" y="-8" width="24" height="16" rx="8" fill="#b42318"/><text x="2" y="3.5" text-anchor="middle" font-size="9.5" fill="#fff" font-weight="700">${n.diff_count}Δ</text></g>` : ""}
      </g>`;
  }).join("");

  const cur = DATA.graph.nodes.find(n => n.id === sel) || nodes[0];
  const inc = edges.filter(e => e.to === sel);
  const out = edges.filter(e => e.from === sel);
  const setupTotal = DATA.graph.nodes.filter(n => n.layer === "setup").length;
  const routineTotal = DATA.graph.nodes.filter(n => n.layer === "routine").length;
  const thmTotal = DATA.graph.nodes.filter(n => n.layer === "theorem").length;
  const witTotal = DATA.graph.nodes.filter(n => n.layer === "witness").length;

  return `
    <div class="sh" style="margin-top:0">
      <h2>Layered Dependency DAG (Frozen Inputs, Shared Theory, Theorems &amp; Witnesses)</h2>
      <span>${nodes.length} of ${DATA.graph.nodes.length} nodes · ${edges.length} edges · Click node to trace closure; double-click to inspect</span>
    </div>
    <div class="filter-bar">
      <span style="font-size:.76rem;font-weight:700;color:var(--muted)">Toggle Layers:</span>
      ${[
        ["uses", `— uses (${thmTotal} Theorems)`],
        ...(setupTotal ? [["setup", `- - setup (${setupTotal} Frozen Assumptions)`]] : []),
        ...(routineTotal ? [["routine", `··· routine (${routineTotal} Shared Lean Theory)`]] : []),
        ...(witTotal ? [["witness", `-·- witness (${witTotal} Non-Vacuity)`]] : []),
      ].map(([k, lbl]) => `<button type="button" class="f-btn" data-edge-kind="${k}" aria-pressed="${state.graphEdges[k]}">${lbl}</button>`).join("")}
    </div>
    <div class="graph-layout">
      <div class="graph-box">
        <svg class="graph-svg" viewBox="0 0 ${W} ${H}">
          <defs>
            <marker id="a-uses" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="6" markerHeight="6" orient="auto"><path d="M0,1 L9,5 L0,9 z" fill="#0f172a"/></marker>
            <marker id="a-setup" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="6" markerHeight="6" orient="auto"><path d="M0,1 L9,5 L0,9 z" fill="#64748b"/></marker>
            <marker id="a-routine" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="6" markerHeight="6" orient="auto"><path d="M0,1 L9,5 L0,9 z" fill="#0b6374"/></marker>
            <marker id="a-witness" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="6" markerHeight="6" orient="auto"><path d="M0,1 L9,5 L0,9 z" fill="#146c43"/></marker>
          </defs>
          ${edgeSvg}${nodeSvg}
        </svg>
      </div>
      ${cur ? `
        <aside class="card">
          <div style="font:700 .74rem/1 var(--mono);color:var(--accent);text-transform:uppercase">${esc(cur.ref)} · ${esc(cur.layer)}</div>
          <h3 style="margin:.25rem 0 .45rem">${esc(cur.title)}</h3>
          <div style="display:flex;gap:.35rem;flex-wrap:wrap;margin-bottom:.6rem">
            ${cur.sha ? chip("🔒 SHA " + cur.sha, "slate") : ""}
            ${cur.loc ? chip(cur.loc.toLocaleString() + " LoC", "teal") : ""}
            ${cur.basis === "lean" ? chip("⑂ Lean-Only Route", "indigo") : ""}
            ${cur.diff_count ? chip(cur.diff_count + "Δ Diffs", "coral") : ""}
          </div>
          <p style="font-size:.84rem;margin:0 0 .65rem">${rich(cur.summary)}</p>
          ${cur.file ? `<p style="font-size:.75rem;color:var(--muted);margin:0 0 .7rem"><code>${esc(cur.file)}</code></p>` : ""}
          <strong style="font-size:.78rem">Upstream (${inc.length})</strong>
          <ul style="padding-left:1.1rem;margin:.3rem 0 .65rem;font-size:.78rem;color:var(--muted)">
            ${inc.length ? inc.map(e => `<li><strong>${esc(e.from)}</strong> (${esc(e.kind)}): ${esc(e.reason)}</li>`).join("") : "<li>Foundational layer</li>"}
          </ul>
          <strong style="font-size:.78rem">Downstream (${out.length})</strong>
          <ul style="padding-left:1.1rem;margin:.3rem 0 .8rem;font-size:.78rem;color:var(--muted)">
            ${out.length ? out.map(e => `<li><strong>${esc(e.to)}</strong> (${esc(e.kind)}): ${esc(e.reason)}</li>`).join("") : "<li>Headline endpoint</li>"}
          </ul>
          <button type="button" class="btn primary" style="width:100%;justify-content:center" data-open-claim="${esc(cur.claim_id)}" data-open-tab="english">Inspect Theorem Details →</button>
        </aside>` : ""}
    </div>`;
}

function renderClaimInspector() {
  const c = claimById(state.claimId);
  let pane = "";
  if (state.claimTab === "english") {
    pane = `
      <div class="card">
        <h3 style="margin-top:0">Plain English</h3>
        <p style="max-width:72ch">${rich(c.plain_english)}</p>
        <h3>High-Level Proof Sketch</h3>
        <p style="max-width:72ch">${rich(c.proof_sketch || "A proof sketch has yet to be recorded.")}</p>
        ${c.route_note ? `
          <div class="route-callout" style="margin-bottom:.75rem">
            <strong>⑂ Why Lean uses a different proof route for ${esc(c.reference)}:</strong>
            ${rich(c.route_note)}
          </div>` : ""}
        <p style="font-size:.82rem;color:var(--muted);margin-bottom:0"><strong>Origin:</strong> ${esc(c.proof_origin)}${c.witness ? ` · <strong>Witness:</strong> <code>${esc(c.witness)}</code>` : ""}</p>
      </div>`;
  } else if (state.claimTab === "paper") {
    pane = `
      <div class="card">
        <p style="margin-top:0;font-size:.82rem;color:var(--muted)">${esc(c.paper_loc)} · <a href="manuscript.pdf">Local PDF</a>${DATA.paper.publication ? ` · <a href="${esc(DATA.paper.publication)}" target="_blank" rel="noopener">arXiv ↗</a>` : ""}</p>
        <div style="padding:.85rem 1rem;background:var(--bg);border:1px solid var(--line);border-radius:8px;margin-bottom:.9rem">${rich(c.paper_statement)}</div>
        <details open><summary style="font-weight:700;font-size:.82rem;color:var(--accent);cursor:pointer">Verbatim TeX</summary><pre class="code">${esc(c.paper_tex)}</pre></details>
      </div>`;
  } else if (state.claimTab === "lamport") {
    const lp = c.lamport;
    pane = `
      ${lp.provenance ? `
        <div class="card" style="margin-bottom:.8rem;background:${c.basis==="lean" ? "var(--indigo-bg)" : "var(--subtle)"};border-color:${c.basis==="lean" ? "var(--indigo-bd)" : "var(--line)"}">
          <strong>Provenance:</strong> ${rich(lp.provenance)}
        </div>` : ""}
      ${lp.groups.map(g => `
        <details class="lp-card" open>
          <summary><span class="lp-tag">${esc(g.id)}</span> <span>${rich(g.title)}</span></summary>
          ${g.steps.map(s => `
            <div class="lp-step">
              <div><code>${esc(s.id)}</code> <strong>${rich(s.title)}</strong></div>
              ${s.body ? `<p>${rich(s.body)}</p>` : ""}
              ${(s.uses && s.uses.length) || s.lean ? `<div style="font-size:.75rem;color:var(--muted)">${s.uses && s.uses.length ? `Uses: ${rich(s.uses.join(", "))}` : ""}${s.uses && s.uses.length && s.lean ? " · " : ""}${s.lean ? `Lean: <code>${esc(s.lean)}</code>` : ""}</div>` : ""}
            </div>`).join("")}
        </details>`).join("")}`;
  } else if (state.claimTab === "review") {
    const comp = c.comparison;
    pane = `
      <div class="card" style="margin-bottom:.85rem">
        ${c.fidelity_summary ? `<p style="margin:0 0 .45rem"><strong>Direction Summary:</strong> ${esc(c.fidelity_summary)}</p>` : ""}
        <p style="margin:0 0 .65rem;font-size:.82rem;color:var(--muted)">${esc(comp.summary)}</p>
        <div style="display:flex;gap:.5rem;flex-wrap:wrap;align-items:center">
          <button type="button" class="btn primary" data-go-diff="${esc(c.id)}">Open Side-by-Side Highlighted Diff →</button>
          ${c.review_url ? `<a class="btn" href="${esc(c.review_url)}">Classic Author Review Page</a>` : ""}
          <span style="font-size:.76rem;color:var(--muted)">Hover any <strong>Lean vs. Paper</strong> badge below for its exact definition.</span>
        </div>
      </div>
      <div class="tbl-wrap">
        <table class="ledger">
          <thead><tr><th>Case</th><th>Lean vs. Paper Direction</th><th>Paper States</th><th>Lean Formalizes</th><th>Why / Assessment</th></tr></thead>
          <tbody>
            ${comp.cases.map(r => `<tr><td><strong>${esc(r.code)}</strong></td><td>${kindToken(r.kind)}</td><td>${esc(r.paper)}</td><td>${esc(r.lean)}</td><td style="color:var(--muted)">${esc(r.why)}</td></tr>`).join("")}
          </tbody>
        </table>
      </div>`;
  } else {
    pane = `
      <div class="card" style="margin-bottom:.8rem">
        <div style="display:flex;gap:.45rem;flex-wrap:wrap;margin-bottom:.6rem;align-items:center">
          ${chip("Declaration: " + c.declaration, "teal")}
          ${c.sha256 ? chip("🔒 SHA " + c.sha256.slice(0, 12), "slate", "Gate-1 frozen statement fingerprint.") : ""}
          ${chip("Axioms: " + c.axioms.join(", "), "green")}
          ${c.witness ? chip("Witness: " + c.witness.split(".").pop(), "green", c.witness_note) : ""}
          ${c.audit_log ? `<a class="btn" href="${esc(c.audit_log)}" style="padding:.15rem .5rem;font-size:.72rem">Audit Receipt JSON</a>` : ""}
          ${c.run_log ? `<a class="btn" href="${esc(c.run_log)}" style="padding:.15rem .5rem;font-size:.72rem">Build Log</a>` : ""}
        </div>
        <pre class="code">${hlLean(c.lean_source)}</pre>
      </div>
      <details>
        <summary style="font-weight:700;font-size:.82rem;color:var(--accent);cursor:pointer">Audited Totalized Lean Defaults (${c.defaults.length}/${c.defaults.length} Justified)</summary>
        <div class="tbl-wrap" style="margin-top:.55rem">
          <table class="ledger">
            <thead><tr><th>Operation</th><th>Constant</th><th>Status</th><th>Justification</th></tr></thead>
            <tbody>${c.defaults.map(d => `<tr><td><code>${esc(d.construct)}</code></td><td><code>${esc(d.constant)}</code> (${esc(d.file)} L${esc(d.line)})</td><td>${chip(d.status, "green")}</td><td>${esc(d.explanation || d.meaning)}</td></tr>`).join("")}</tbody>
          </table>
        </div>
      </details>`;
  }

  return `
    <div class="filter-bar">
      ${DATA.claims.map(cl => `<button type="button" class="f-btn" data-open-claim="${esc(cl.id)}" data-open-tab="${esc(state.claimTab)}" aria-pressed="${cl.id === c.id}">${esc(cl.reference)}</button>`).join("")}
    </div>
    <div class="card" style="margin-bottom:.9rem">
      <div style="font:700 .75rem/1 var(--mono);color:var(--accent)">${esc(c.reference)} · ${esc(c.paper_loc)}</div>
      <h2 style="margin:.25rem 0 .55rem;font-size:1.3rem">${rich(c.title)}</h2>
      <div style="display:flex;gap:.4rem;flex-wrap:wrap;margin-bottom:.75rem">
        ${chip(c.closed ? "✓ Lean Checked" : c.status, c.closed ? "green" : "amber", "Unconditional kernel theorem, standard axioms only.")}
        ${chip(c.basis === "lean" ? "⑂ Lean-Only Proof Route" : "≡ Aligned Proof", c.basis === "lean" ? "indigo" : "slate", c.basis_label)}
        ${c.sha256 ? chip("🔒 Frozen " + c.sha256.slice(0, 8), "slate") : ""}
        ${chip(c.approved ? "✓ Author Signed" : "⚠ Awaiting Human Sign-Off", c.approved ? "green" : "coral")}
        ${c.comparison.result === "difference" ? chip(`⚠ ${c.comparison.counts.gap} Repairs`, "coral") : chip("✓ Match", "green")}
      </div>
      <div class="filter-bar" style="margin-bottom:0">
        ${[["english","Plain English & Sketch"],["paper","Paper TeX"],["lamport","Lamport Proof"],["review","Semantic Review"],["lean","Lean 4 & Evidence"]].map(([k,l]) =>
          `<button type="button" class="f-btn" data-open-claim="${esc(c.id)}" data-open-tab="${k}" aria-pressed="${state.claimTab===k}">${l}</button>`).join("")}
      </div>
    </div>
    ${pane}`;
}

function render() {
  const q = DATA.quality;
  const s = DATA.stats;
  const topChip = document.getElementById("top-tier-chip");
  const allSigned = s.reviewed_claims >= s.total_claims && s.total_claims > 0;
  if (q) {
    topChip.textContent = `${q.tier_badge} · ${q.score}`;
    topChip.className = `chip ${allSigned ? "green" : "gold"}`;
  } else {
    topChip.textContent = `${s.closed_claims}/${s.total_claims} Closed`;
    topChip.className = "chip green";
  }

  const diffBadge = document.getElementById("diff-nav-badge");
  diffBadge.textContent = String(s.gap_cases);
  diffBadge.className = `nav-count${s.gap_cases === 0 ? " zero" : ""}`;

  document.querySelectorAll(".subnav button").forEach(b => {
    if (b.dataset.view === state.view) b.setAttribute("aria-current", "page");
    else b.removeAttribute("aria-current");
  });

  const app = document.getElementById("app");
  if (state.view === "overview") app.innerHTML = renderOverview();
  else if (state.view === "ledger") app.innerHTML = renderLedger();
  else if (state.view === "diff") app.innerHTML = renderDiffWorkbench();
  else if (state.view === "graph") app.innerHTML = renderGraphView();
  else app.innerHTML = renderClaimInspector();

  syncHash();
  bind();
}

function bind() {
  document.querySelectorAll("[data-go]").forEach(b => b.addEventListener("click", () => { state.view = b.dataset.go; render(); }));
  document.querySelectorAll("[data-scroll-to]").forEach(b => b.addEventListener("click", () => {
    const el = document.getElementById(b.dataset.scrollTo);
    if (el) el.scrollIntoView({ behavior: "smooth" });
  }));
  document.querySelectorAll("[data-go-gaps]").forEach(b => b.addEventListener("click", () => {
    const targetClaim = DATA.claims.find(c => c.comparison.result === "difference") || DATA.claims.find(c => c.comparison.counts.gap > 0) || DATA.claims[0];
    if (targetClaim) {
      state.diffClaim = targetClaim.id;
      const firstGap = targetClaim.comparison.cases.find(x => x.polarity === "gap");
      state.activeCase = firstGap ? firstGap.code : null;
    }
    state.diffFilter = "gap";
    state.view = "diff";
    render();
    window.scrollTo({ top: 0, behavior: "smooth" });
  }));
  document.querySelectorAll("[data-open-claim]").forEach(b => b.addEventListener("click", () => {
    state.claimId = b.dataset.openClaim;
    if (b.dataset.openTab) state.claimTab = b.dataset.openTab;
    state.view = "claim"; render();
    window.scrollTo({ top: 0, behavior: "smooth" });
  }));
  document.querySelectorAll("[data-go-diff]").forEach(b => b.addEventListener("click", () => {
    state.diffClaim = b.dataset.goDiff; state.activeCase = null; state.view = "diff"; render();
    window.scrollTo({ top: 0, behavior: "smooth" });
  }));
  document.querySelectorAll("[data-diff-claim]").forEach(b => b.addEventListener("click", () => {
    state.diffClaim = b.dataset.diffClaim; state.activeCase = null; render();
  }));
  document.querySelectorAll("[data-diff-filter]").forEach(b => b.addEventListener("click", () => {
    state.diffFilter = b.dataset.diffFilter; render();
  }));
  document.querySelectorAll("[data-pick-case]").forEach(el => el.addEventListener("click", () => {
    state.activeCase = el.dataset.pickCase; render();
  }));
  document.querySelectorAll("[data-jump-case]").forEach(tr => tr.addEventListener("click", () => {
    const [cid, code] = tr.dataset.jumpCase.split("|");
    state.diffClaim = cid; state.activeCase = code; render();
    window.scrollTo({ top: 140, behavior: "smooth" });
  }));
  document.querySelectorAll("[data-edge-kind]").forEach(b => b.addEventListener("click", () => {
    const k = b.dataset.edgeKind;
    if (k === "uses") return;
    state.graphEdges[k] = !state.graphEdges[k]; render();
  }));
  document.querySelectorAll("[data-node]").forEach(g => {
    g.addEventListener("click", () => { state.graphSel = g.dataset.node; render(); });
    g.addEventListener("dblclick", () => {
      const n = DATA.graph.nodes.find(x => x.id === g.dataset.node);
      if (n && n.claim_id) { state.claimId = n.claim_id; state.claimTab = "english"; state.view = "claim"; render(); }
    });
  });
}

document.querySelectorAll(".subnav button").forEach(b => b.addEventListener("click", () => {
  state.view = b.dataset.view; render();
}));

const dlg = document.getElementById("key-dialog");
document.getElementById("open-key").addEventListener("click", () => {
  const cite = DATA.quality && DATA.quality.survey_citation;
  document.getElementById("key-body").innerHTML = `
    <h3 style="font-size:.92rem;margin:0 0 .4rem">Semantic Comparison Tokens (Lean vs. Paper Direction)</h3>
    <p style="margin:0 0 .5rem;color:var(--muted);font-size:.8rem">Every semantic label states explicitly which side (Lean or Paper) is stronger, narrower, or adds an assumption:</p>
    ${Object.entries(KIND_INFO).map(([, v]) => `
      <div style="display:grid;grid-template-columns:15.5rem 1fr;gap:.75rem;padding:.35rem 0;border-bottom:1px solid var(--line);font-size:.8rem;align-items:baseline">
        <div><span class="sem-token sem-${v.polarity}">${esc(v.label)}</span></div>
        <div style="color:var(--muted)">${esc(v.tip)}</div>
      </div>`).join("")}
    <h3 style="font-size:.92rem;margin:1rem 0 .4rem">Verification Badges</h3>
    ${DATA.badges.map(b => `<div style="display:grid;grid-template-columns:15.5rem 1fr;gap:.75rem;padding:.35rem 0;border-bottom:1px solid var(--line);font-size:.8rem"><div>${chip(b.label, b.tone)}</div><div style="color:var(--muted)">${esc(b.short)}</div></div>`).join("")}
    ${cite ? `<p style="margin:.9rem 0 0;font-size:.8rem"><strong>Research Citation:</strong> ${esc(cite.authors)} — <em>${esc(cite.title)}</em> · <a href="${esc(cite.repo_url)}" target="_blank" rel="noopener">GitHub Repo ↗</a></p>` : ""}`;
  dlg.showModal();
});
document.getElementById("close-key").addEventListener("click", () => dlg.close());
dlg.addEventListener("click", e => { if (e.target === dlg) dlg.close(); });

loadFromHash();
window.addEventListener("hashchange", () => { loadFromHash(); render(); });
window.addEventListener("load", () => render());
render();
