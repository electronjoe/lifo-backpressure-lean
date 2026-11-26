"use strict";

document.addEventListener("click", event => {
  const trigger = event.target.closest("a[data-artifact-record]");
  if (!trigger || event.defaultPrevented || event.button !== 0 ||
      event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
  const dialog = document.createElement("dialog");
  if (typeof dialog.showModal !== "function") return;

  event.preventDefault();
  dialog.className = "artifact-notice";
  dialog.setAttribute("aria-labelledby", "artifact-title");
  dialog.setAttribute("aria-describedby", "artifact-message");
  dialog.innerHTML = `<h2 id="artifact-title">GitHub sign-in required</h2>
    <p id="artifact-message">Sign in to GitHub to download the artifact ZIP. You can read the same verification record here without an account.</p>
    <div><a class="public-record">Open public verification record</a>
    <a class="github-download">Continue to GitHub</a>
    <form method="dialog"><button>Cancel</button></form></div>`;
  dialog.querySelector(".public-record").href = trigger.dataset.artifactRecord;
  dialog.querySelector(".github-download").href = trigger.href;
  dialog.addEventListener("close", () => {
    dialog.remove();
    trigger.focus();
  }, {once:true});
  document.body.append(dialog);
  dialog.showModal();
});
