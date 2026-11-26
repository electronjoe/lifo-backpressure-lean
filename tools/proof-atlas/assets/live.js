"use strict";
if (location.protocol.startsWith("http")) {
  const revision = document.currentScript.dataset.revision;
  const message = document.createElement("p");
  message.setAttribute("role","alert");
  message.hidden=true;
  document.body.prepend(message);
  async function refresh() {
    try {
      const [run, status] = await Promise.all(["checkpoint.json","preview-status.json"].map(path=>fetch(path,{cache:"no-store"})));
      if (status.ok) {
        const state=await status.json();
        message.hidden=!state.error;
        message.textContent=state.error ? "Preview shows the last successful build. "+state.error : "";
      }
      if(run.ok && (await run.json()).revision!==revision) location.reload();
    } catch { /* The last readable snapshot remains available. */ }
  }
  setInterval(refresh,2400);
}
