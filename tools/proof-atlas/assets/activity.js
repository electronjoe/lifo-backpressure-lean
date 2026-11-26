"use strict";
(() => {
  const inventory = document.querySelector("#claim-inventory");
  if (!inventory || !location.protocol.startsWith("http")) return;
  const local = ["localhost", "127.0.0.1", "[::1]"].includes(location.hostname);
  const feed = (!local && inventory.dataset.feed) || "activity.json";
  const github = new URL(feed, location.href).hostname === "api.github.com";
  const interval = github ? 75000 : 5000;
  const rows = Array.from(inventory.querySelectorAll("li[data-claim]"));
  const phases = {writing:"Writing Lean proof", checking:"Lean check running",
    finished:"Lean check finished", failed:"Lean check failed", paused:"Proof work paused"};
  async function update() {
    try {
      const url = new URL(feed, location.href);
      url.searchParams.set("poll", Math.floor(Date.now()/interval));
      const headers = github ? {Accept:"application/vnd.github.raw+json"} : {};
      const res = await fetch(url, {cache:"no-store", headers});
      if (!res.ok) throw Error(res.status);
      const {runs} = await res.json();
      const now = Date.now()/1000;
      for (const row of rows) {
        const events = runs.filter(r => r.claim === row.dataset.claim && Object.hasOwn(phases, r.phase))
          .sort((a,b) => b.updated-a.updated);
        const active = events.filter(r => ["writing","checking"].includes(r.phase) && r.expires > now);
        const shown = active.length ? active : events.slice(0,1);
        const parts = shown.map(r => {
          const expired = ["writing","checking"].includes(r.phase) && r.expires <= now;
          const label = expired ? "Activity update expired" : phases[r.phase];
          return label + " · " + r.task + " · " + new Date(1000*r.updated).toLocaleString();
        });
        row.classList.toggle("working", active.length > 0);
        row.querySelector(".claim-activity").textContent = parts.join("\n");
      }
    } catch {
      for (const row of rows) {
        const hadActivity = row.classList.contains("working");
        row.classList.remove("working");
        const span = row.querySelector(".claim-activity");
        if (hadActivity || row.querySelector(".proof-target")) span.textContent = "Live activity unavailable";
      }
    } finally {
      setTimeout(update, interval);
    }
  }
  update();
})();
