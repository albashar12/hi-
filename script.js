/* AppVault — a private, end-to-end encrypted file vault that uses a Telegram bot as its
 * storage backend.
 *
 * How data is protected:
 *  - A random AES-256 "master key" is generated once, the first time this vault is created.
 *    Every file is encrypted with that key (AES-GCM, random IV per file) *in the browser*
 *    before it is ever sent to Telegram — so Telegram, and anyone who only has the bot
 *    token, only ever sees opaque ciphertext under a randomised, masked filename
 *    (.vdat / .vimg / .vvid). There is nothing on Telegram's side that reveals what a file is.
 *  - The master key itself is never stored in the open. It's "wrapped" (encrypted) with a
 *    key derived from your password via PBKDF2, and that wrapped copy is what's kept in a
 *    pinned JSON message in the chat. Your password never leaves the browser and Telegram
 *    never sees it. Changing your password just re-wraps the same master key — no files
 *    need to be re-uploaded.
 *  - There is no password recovery. If you forget your password, the master key — and every
 *    file it protects — cannot be recovered. That's the trade-off of real end-to-end
 *    encryption: there is no backdoor, not even for us.
 *  - The bot token and chat ID you enter are stored only in this browser's localStorage —
 *    never written into these files. Anyone with both can still see *that* files exist and
 *    delete them, so use a bot made just for this and keep the token private.
 */

(() => {
  const LS_TOKEN = "appvault_bot_token";
  const LS_CHATID = "appvault_chat_id";
  const LS_THEME = "appvault_theme";
  const DEFAULT_PASSWORD = "1234";
  const EXT_MAP = { image: ".vimg", video: ".vvid", file: ".vdat" };
  const MANIFEST_LIMIT = 3900; // stay under Telegram's 4096-char message limit
  const PBKDF2_ITERATIONS = 250000;
  const LOCK_AFTER_MS = 5 * 60 * 1000; // auto-lock after 5 minutes of inactivity
  const POLL_INTERVAL_MS = 5000; // re-check Telegram for changes from other devices

  const state = {
    token: null,
    chatId: null,
    manifest: { salt: null, wrappedKey: null, files: [] },
    manifestMessageId: null,
    masterKey: null,     // CryptoKey, only ever held in memory, cleared on lock
  };

  const objectUrlCache = new Map(); // fileId -> { url, mime }
  let failStreak = 0;
  let inactivityTimer = null;
  let pollTimer = null;
  let manifestBusy = false; // true while this tab is writing the manifest — polling backs off
  let currentIndex = -1;

  // ---------------------------------------------------------------- helpers

  const $ = (id) => document.getElementById(id);

  function showScreen(name) {
    document.querySelectorAll(".screen").forEach((s) => s.classList.remove("active"));
    $(name).classList.add("active");
  }

  function isDashboardActive() {
    return $("dashboard-screen").classList.contains("active");
  }

  function randomId(len = 14) {
    if (crypto.randomUUID) return crypto.randomUUID().replace(/-/g, "").slice(0, len);
    return (Date.now().toString(36) + Math.random().toString(36).slice(2)).slice(0, len);
  }

  function classify(mime) {
    if (mime && mime.startsWith("image/")) return "image";
    if (mime && mime.startsWith("video/")) return "video";
    return "file";
  }

  function humanSize(bytes) {
    if (bytes < 1024) return bytes + " B";
    const units = ["KB", "MB", "GB"];
    let val = bytes / 1024, i = 0;
    while (val >= 1024 && i < units.length - 1) { val /= 1024; i++; }
    return val.toFixed(1) + " " + units[i];
  }

  function toast(message, kind = "") {
    const el = $("upload-status");
    el.textContent = message;
    el.className = "upload-status" + (kind ? " " + kind : "");
    el.classList.remove("hidden");
    clearTimeout(toast._t);
    toast._t = setTimeout(() => el.classList.add("hidden"), 3200);
  }

  function bytesToBase64(bytes) {
    let binary = "";
    for (const b of bytes) binary += String.fromCharCode(b);
    return btoa(binary);
  }
  function base64ToBytes(b64) {
    const binary = atob(b64);
    const bytes = new Uint8Array(binary.length);
    for (let i = 0; i < binary.length; i++) bytes[i] = binary.charCodeAt(i);
    return bytes;
  }
  function bytesToHex(bytes) {
    return Array.from(bytes).map((b) => b.toString(16).padStart(2, "0")).join("");
  }
  function hexToBytes(hex) {
    const arr = new Uint8Array(hex.length / 2);
    for (let i = 0; i < arr.length; i++) arr[i] = parseInt(hex.substr(i * 2, 2), 16);
    return arr;
  }
  function concatBytes(a, b) {
    const out = new Uint8Array(a.length + b.length);
    out.set(a, 0); out.set(b, a.length);
    return out;
  }

  // ---------------------------------------------------------------- crypto

  async function deriveKEK(password, saltHex) {
    const keyMaterial = await crypto.subtle.importKey(
      "raw", new TextEncoder().encode(password), "PBKDF2", false, ["deriveKey"]
    );
    return crypto.subtle.deriveKey(
      { name: "PBKDF2", salt: hexToBytes(saltHex), iterations: PBKDF2_ITERATIONS, hash: "SHA-256" },
      keyMaterial,
      { name: "AES-GCM", length: 256 },
      false,
      ["wrapKey", "unwrapKey"]
    );
  }

  async function createVaultKey(password) {
    const salt = crypto.getRandomValues(new Uint8Array(16));
    const saltHex = bytesToHex(salt);
    const kek = await deriveKEK(password, saltHex);
    const masterKey = await crypto.subtle.generateKey({ name: "AES-GCM", length: 256 }, true, ["encrypt", "decrypt"]);
    const iv = crypto.getRandomValues(new Uint8Array(12));
    const wrapped = await crypto.subtle.wrapKey("raw", masterKey, kek, { name: "AES-GCM", iv });
    return {
      salt: saltHex,
      wrappedKey: bytesToBase64(concatBytes(iv, new Uint8Array(wrapped))),
      masterKey,
    };
  }

  // Throws if the password is wrong (AES-GCM auth tag won't verify).
  async function unwrapVaultKey(password, saltHex, wrappedKeyB64) {
    const kek = await deriveKEK(password, saltHex);
    const combined = base64ToBytes(wrappedKeyB64);
    const iv = combined.slice(0, 12);
    const wrapped = combined.slice(12);
    return crypto.subtle.unwrapKey(
      "raw", wrapped, kek, { name: "AES-GCM", iv },
      { name: "AES-GCM", length: 256 }, true, ["encrypt", "decrypt"]
    );
  }

  async function rewrapVaultKey(masterKey, newPassword) {
    const salt = crypto.getRandomValues(new Uint8Array(16));
    const saltHex = bytesToHex(salt);
    const kek = await deriveKEK(newPassword, saltHex);
    const iv = crypto.getRandomValues(new Uint8Array(12));
    const wrapped = await crypto.subtle.wrapKey("raw", masterKey, kek, { name: "AES-GCM", iv });
    return { salt: saltHex, wrappedKey: bytesToBase64(concatBytes(iv, new Uint8Array(wrapped))) };
  }

  async function encryptBytes(arrayBuffer, key) {
    const iv = crypto.getRandomValues(new Uint8Array(12));
    const ciphertext = await crypto.subtle.encrypt({ name: "AES-GCM", iv }, key, arrayBuffer);
    return concatBytes(iv, new Uint8Array(ciphertext));
  }

  async function decryptBytes(arrayBuffer, key) {
    const bytes = new Uint8Array(arrayBuffer);
    const iv = bytes.slice(0, 12);
    const data = bytes.slice(12);
    return crypto.subtle.decrypt({ name: "AES-GCM", iv }, key, data);
  }

  // ---------------------------------------------------------- Telegram API

  function apiBase() { return `https://api.telegram.org/bot${state.token}`; }
  function fileBase() { return `https://api.telegram.org/file/bot${state.token}`; }

  async function tg(method, body, isForm = false) {
    const opts = isForm
      ? { method: "POST", body }
      : { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(body || {}) };
    let res;
    try {
      res = await fetch(`${apiBase()}/${method}`, opts);
    } catch (e) {
      throw new Error("Couldn't reach Telegram. Check your connection.");
    }
    const data = await res.json();
    if (!data.ok) throw new Error(data.description || `Telegram rejected ${method}`);
    return data.result;
  }

  async function loadManifest() {
    const chat = await tg("getChat", { chat_id: state.chatId });
    const pinned = chat.pinned_message;
    if (pinned && typeof pinned.text === "string") {
      try {
        const parsed = JSON.parse(pinned.text);
        if (parsed && parsed.salt && parsed.wrappedKey) {
          state.manifest = {
            salt: parsed.salt,
            wrappedKey: parsed.wrappedKey,
            files: Array.isArray(parsed.files) ? parsed.files : [],
          };
          state.manifestMessageId = pinned.message_id;
          return;
        }
      } catch (e) { /* not our manifest — fall through and treat as fresh */ }
    }
    state.manifest = { salt: null, wrappedKey: null, files: [] };
    state.manifestMessageId = null;
  }

  async function saveManifest() {
    const text = JSON.stringify(state.manifest);
    if (text.length > MANIFEST_LIMIT) {
      throw new Error("Vault index is full — delete a few files so changes keep syncing across devices.");
    }
    if (state.manifestMessageId) {
      await tg("editMessageText", { chat_id: state.chatId, message_id: state.manifestMessageId, text });
    } else {
      const msg = await tg("sendMessage", { chat_id: state.chatId, text, disable_notification: true });
      await tg("pinChatMessage", { chat_id: state.chatId, message_id: msg.message_id, disable_notification: true });
      state.manifestMessageId = msg.message_id;
    }
  }

  async function fetchEncryptedBytes(fileId) {
    const f = await tg("getFile", { file_id: fileId });
    const res = await fetch(`${fileBase()}/${f.file_path}`);
    if (!res.ok) throw new Error("Couldn't download this file.");
    return res.arrayBuffer();
  }

  // Returns a decrypted, in-memory object URL for a file entry. Cached for the session.
  async function resolveObjectUrl(entry) {
    if (objectUrlCache.has(entry.fileId)) return objectUrlCache.get(entry.fileId).url;
    const encrypted = await fetchEncryptedBytes(entry.fileId);
    const plainBuf = await decryptBytes(encrypted, state.masterKey);
    const blob = new Blob([plainBuf], { type: entry.mime || "application/octet-stream" });
    const url = URL.createObjectURL(blob);
    objectUrlCache.set(entry.fileId, { url, mime: entry.mime });
    return url;
  }

  function clearObjectUrlCache() {
    for (const { url } of objectUrlCache.values()) URL.revokeObjectURL(url);
    objectUrlCache.clear();
  }

  // -------------------------------------------------------------- upload

  async function uploadOne(file) {
    const kind = classify(file.type);
    const maskedName = randomId(16) + EXT_MAP[kind];
    const raw = await file.arrayBuffer();
    const encrypted = await encryptBytes(raw, state.masterKey);
    const blob = new Blob([encrypted], { type: "application/octet-stream" });
    const form = new FormData();
    form.append("chat_id", state.chatId);
    form.append("disable_notification", "true");
    form.append("document", blob, maskedName);
    const msg = await tg("sendDocument", form, true);
    const entry = {
      id: randomId(10),
      name: file.name,
      maskedName,
      kind,
      mime: file.type || "application/octet-stream",
      size: file.size,
      fileId: msg.document.file_id,
      messageId: msg.message_id,
      date: new Date().toISOString(),
    };
    state.manifest.files.unshift(entry);
    return entry;
  }

  async function uploadFiles(fileList) {
    const files = Array.from(fileList);
    if (!files.length) return;
    manifestBusy = true;
    try {
      for (let i = 0; i < files.length; i++) {
        toast(`Encrypting & uploading ${i + 1} of ${files.length}…`);
        try {
          await uploadOne(files[i]);
          renderGallery();
        } catch (e) {
          toast(e.message, "error");
        }
      }
      await saveManifest();
      toast(files.length > 1 ? "Files added" : "File added", "success");
    } catch (e) {
      toast(e.message, "error");
    } finally {
      manifestBusy = false;
    }
  }

  async function deleteEntry(entry) {
    manifestBusy = true;
    try {
      try { await tg("deleteMessage", { chat_id: state.chatId, message_id: entry.messageId }); }
      catch (e) { /* message may already be gone — still remove it locally */ }
      if (objectUrlCache.has(entry.fileId)) {
        URL.revokeObjectURL(objectUrlCache.get(entry.fileId).url);
        objectUrlCache.delete(entry.fileId);
      }
      state.manifest.files = state.manifest.files.filter((f) => f.id !== entry.id);
      await saveManifest();
    } catch (e) {
      toast(e.message, "error");
    } finally {
      manifestBusy = false;
    }
    renderGallery();
  }

  // -------------------------------------------------------------- gallery

  const ICON = {
    video: '<svg viewBox="0 0 24 24" width="16" height="16" fill="none"><path d="M4 6a2 2 0 012-2h9a2 2 0 012 2v12a2 2 0 01-2 2H6a2 2 0 01-2-2V6z" stroke="currentColor" stroke-width="1.5"/><path d="M20 9l3-1.6v9.2L20 15" stroke="currentColor" stroke-width="1.5" stroke-linejoin="round"/></svg>',
    file: '<svg viewBox="0 0 24 24" width="16" height="16" fill="none"><path d="M7 3h7l5 5v13a1 1 0 01-1 1H7a1 1 0 01-1-1V4a1 1 0 011-1z" stroke="currentColor" stroke-width="1.5" stroke-linejoin="round"/><path d="M14 3v5h5" stroke="currentColor" stroke-width="1.5" stroke-linejoin="round"/></svg>',
  };

  let galleryObserver = null;

  function renderGallery() {
    const grid = $("gallery-grid");
    const empty = $("gallery-empty");
    const countEl = $("file-count");
    const files = state.manifest.files;

    if (!files.length) {
      grid.innerHTML = "";
      empty.classList.remove("hidden");
      countEl.classList.add("hidden");
      return;
    }
    empty.classList.add("hidden");
    countEl.textContent = `${files.length} file${files.length === 1 ? "" : "s"} stored`;
    countEl.classList.remove("hidden");

    if (galleryObserver) galleryObserver.disconnect();
    galleryObserver = new IntersectionObserver(onCardVisible, { rootMargin: "200px" });

    grid.innerHTML = "";
    for (const entry of files) {
      const card = document.createElement("div");
      card.className = "file-card";
      card.dataset.id = entry.id;

      const label = document.createElement("div");
      label.className = "file-label";
      label.textContent = entry.name;

      const placeholder = document.createElement("div");
      placeholder.className = "placeholder";
      placeholder.innerHTML = entry.kind === "video" ? ICON.video : ICON.file;

      card.appendChild(placeholder);
      if (entry.kind === "video") {
        const badge = document.createElement("div");
        badge.className = "kind-badge";
        badge.innerHTML = ICON.video;
        card.appendChild(badge);
      }
      card.appendChild(label);

      card.addEventListener("click", () => openPreview(entry.id));
      grid.appendChild(card);
      galleryObserver.observe(card);
    }
  }

  async function onCardVisible(entries, obs) {
    for (const ie of entries) {
      if (!ie.isIntersecting) continue;
      const card = ie.target;
      obs.unobserve(card);
      const entry = state.manifest.files.find((f) => f.id === card.dataset.id);
      if (!entry || entry.kind !== "image") continue;
      try {
        const url = await resolveObjectUrl(entry);
        const img = document.createElement("img");
        img.loading = "lazy";
        img.src = url;
        img.alt = entry.name;
        card.querySelector(".placeholder")?.replaceWith(img);
      } catch (e) { /* leave placeholder if the thumbnail can't load */ }
    }
  }

  // -------------------------------------------------------------- preview

  async function openPreview(entryId) {
    currentIndex = state.manifest.files.findIndex((f) => f.id === entryId);
    if (currentIndex === -1) return;
    $("preview-modal").classList.remove("hidden");
    await renderPreview();
  }

  async function renderPreview() {
    const files = state.manifest.files;
    const entry = files[currentIndex];
    if (!entry) return;

    $("preview-name").textContent = entry.name;
    const multi = files.length > 1;
    $("preview-prev").classList.toggle("hidden", !multi);
    $("preview-next").classList.toggle("hidden", !multi);

    const content = $("preview-content");
    content.innerHTML = '<div class="placeholder">Decrypting…</div>';

    try {
      const url = await resolveObjectUrl(entry);
      if (entry.kind === "image") {
        content.innerHTML = `<div class="zoom-frame" id="zoom-frame"><img src="${url}" alt=""></div>`;
        $("zoom-frame").addEventListener("click", (e) => e.currentTarget.classList.toggle("zoomed"));
      } else if (entry.kind === "video") {
        content.innerHTML = `<video src="${url}" controls playsinline autoplay></video>`;
      } else {
        content.innerHTML = `<div class="placeholder">${humanSize(entry.size)} · no preview available, use download</div>`;
      }
    } catch (e) {
      content.innerHTML = `<div class="placeholder">Couldn't decrypt this file</div>`;
    }
  }

  function navigatePreview(delta) {
    const files = state.manifest.files;
    if (files.length < 2) return;
    currentIndex = (currentIndex + delta + files.length) % files.length;
    renderPreview();
  }

  function closePreview() {
    $("preview-modal").classList.add("hidden");
    $("preview-content").innerHTML = "";
    currentIndex = -1;
  }

  // -------------------------------------------------------------- auth flow

  function haveCredentials() {
    state.token = localStorage.getItem(LS_TOKEN);
    state.chatId = localStorage.getItem(LS_CHATID);
    return !!(state.token && state.chatId);
  }

  async function handleSetupSubmit(ev) {
    ev.preventDefault();
    const token = $("setup-token").value.trim();
    const chatId = $("setup-chatid").value.trim();
    const errEl = $("setup-error");
    errEl.classList.add("hidden");
    if (!token || !chatId) {
      errEl.textContent = "Enter both the bot token and chat ID.";
      errEl.classList.remove("hidden");
      return;
    }
    state.token = token;
    state.chatId = chatId;
    const btn = ev.target.querySelector("button[type=submit]");
    btn.disabled = true;
    btn.textContent = "Connecting…";
    try {
      await tg("getChat", { chat_id: chatId });
      await loadManifest();
      if (!state.manifest.wrappedKey) {
        // Brand-new vault: create the master key now, protected by the default password.
        const { salt, wrappedKey } = await createVaultKey(DEFAULT_PASSWORD);
        state.manifest.salt = salt;
        state.manifest.wrappedKey = wrappedKey;
        await saveManifest();
      }
      localStorage.setItem(LS_TOKEN, token);
      localStorage.setItem(LS_CHATID, chatId);
      showLoginScreen();
    } catch (e) {
      errEl.textContent = e.message || "Couldn't connect. Check the token and chat ID.";
      errEl.classList.remove("hidden");
    } finally {
      btn.disabled = false;
      btn.textContent = "Connect vault";
    }
  }

  function showLoginScreen() {
    showScreen("login-screen");
    $("login-lede").textContent = state.manifest.files.length || state.manifestMessageId
      ? "Enter your password to open the vault."
      : "Enter your password to open the vault. Default password is 1234 — change it in Settings once you're in.";
    $("login-password").value = "";
    $("login-password").focus();
  }

  async function handleLoginSubmit(ev) {
    ev.preventDefault();
    const btn = ev.target.querySelector("button[type=submit]");
    const pw = $("login-password").value;
    const errEl = $("login-error");
    errEl.classList.add("hidden");
    btn.disabled = true;
    btn.textContent = "Unlocking…";
    try {
      state.masterKey = await unwrapVaultKey(pw, state.manifest.salt, state.manifest.wrappedKey);
      failStreak = 0;
      $("login-password").value = "";
      $("settings-chatid").textContent = state.chatId;
      showScreen("dashboard-screen");
      renderGallery();
      resetInactivityTimer();
      startPolling();
    } catch (e) {
      failStreak++;
      errEl.textContent = "Wrong password.";
      errEl.classList.remove("hidden");
      const card = document.querySelector("#login-screen .auth-card");
      card.classList.remove("shake"); void card.offsetWidth; card.classList.add("shake");
      const delay = Math.min(failStreak * 500, 3000);
      await new Promise((r) => setTimeout(r, delay));
    } finally {
      btn.disabled = false;
      btn.textContent = "Unlock";
    }
  }

  async function handlePasswordChange(ev) {
    ev.preventDefault();
    const current = $("pw-current").value;
    const next = $("pw-new").value;
    const confirm = $("pw-confirm").value;
    const errEl = $("pw-error");
    const okEl = $("pw-success");
    errEl.classList.add("hidden");
    okEl.classList.add("hidden");

    try {
      await unwrapVaultKey(current, state.manifest.salt, state.manifest.wrappedKey);
    } catch (e) {
      errEl.textContent = "Current password is incorrect.";
      errEl.classList.remove("hidden");
      return;
    }
    if (next.length < 4) {
      errEl.textContent = "New password must be at least 4 characters.";
      errEl.classList.remove("hidden");
      return;
    }
    if (next !== confirm) {
      errEl.textContent = "New passwords don't match.";
      errEl.classList.remove("hidden");
      return;
    }
    manifestBusy = true;
    try {
      const { salt, wrappedKey } = await rewrapVaultKey(state.masterKey, next);
      state.manifest.salt = salt;
      state.manifest.wrappedKey = wrappedKey;
      await saveManifest();
      okEl.textContent = "Password updated.";
      okEl.classList.remove("hidden");
      ev.target.reset();
    } catch (e) {
      errEl.textContent = e.message;
      errEl.classList.remove("hidden");
    } finally {
      manifestBusy = false;
    }
  }

  function lockVault() {
    state.masterKey = null;
    clearObjectUrlCache();
    clearTimeout(inactivityTimer);
    stopPolling();
    $("settings-modal").classList.add("hidden");
    $("preview-modal").classList.add("hidden");
    $("preview-content").innerHTML = "";
    showLoginScreen();
  }

  function disconnectDevice() {
    localStorage.removeItem(LS_TOKEN);
    localStorage.removeItem(LS_CHATID);
    state.token = null;
    state.chatId = null;
    state.masterKey = null;
    state.manifest = { salt: null, wrappedKey: null, files: [] };
    state.manifestMessageId = null;
    clearObjectUrlCache();
    clearTimeout(inactivityTimer);
    stopPolling();
    $("settings-modal").classList.add("hidden");
    $("setup-token").value = "";
    $("setup-chatid").value = "";
    showScreen("setup-screen");
  }

  // ------------------------------------------------------------ inactivity

  function resetInactivityTimer() {
    clearTimeout(inactivityTimer);
    if (!isDashboardActive()) return;
    inactivityTimer = setTimeout(lockVault, LOCK_AFTER_MS);
  }

  // ---------------------------------------------------------------- syncing

  // Every 5s, quietly re-check the pinned manifest so uploads/deletes/password
  // changes made from another device show up here without a manual reload.
  function startPolling() {
    stopPolling();
    pollTimer = setInterval(pollManifest, POLL_INTERVAL_MS);
  }

  function stopPolling() {
    clearInterval(pollTimer);
    pollTimer = null;
  }

  async function pollManifest() {
    if (!isDashboardActive() || !state.masterKey || manifestBusy || document.hidden) return;
    try {
      const chat = await tg("getChat", { chat_id: state.chatId });
      const pinned = chat.pinned_message;
      if (!pinned || typeof pinned.text !== "string") return;
      const parsed = JSON.parse(pinned.text);
      if (!parsed || !parsed.wrappedKey) return;

      const newFiles = Array.isArray(parsed.files) ? parsed.files : [];
      const changed =
        JSON.stringify(newFiles) !== JSON.stringify(state.manifest.files) ||
        parsed.salt !== state.manifest.salt ||
        parsed.wrappedKey !== state.manifest.wrappedKey;
      if (!changed) return;

      // Drop cached previews for anything that no longer exists remotely.
      const newIds = new Set(newFiles.map((f) => f.fileId));
      for (const [fileId, cached] of objectUrlCache) {
        if (!newIds.has(fileId)) {
          URL.revokeObjectURL(cached.url);
          objectUrlCache.delete(fileId);
        }
      }

      state.manifest = { salt: parsed.salt, wrappedKey: parsed.wrappedKey, files: newFiles };
      state.manifestMessageId = pinned.message_id;
      renderGallery();
      toast("Vault synced", "success");
    } catch (e) {
      // Silent — a transient network hiccup every 5s shouldn't interrupt anyone.
    }
  }

  // ------------------------------------------------------------------ theme

  function applyTheme(theme) {
    document.documentElement.dataset.theme = theme;
    const icon = $("theme-toggle");
    icon.innerHTML = theme === "light" ? ICON_SUN : ICON_MOON;
  }
  const ICON_MOON = '<svg viewBox="0 0 24 24" width="18" height="18" fill="none"><path d="M20 14.5A8.5 8.5 0 019.5 4a8.5 8.5 0 1010.5 10.5z" stroke="currentColor" stroke-width="1.6" stroke-linejoin="round"/></svg>';
  const ICON_SUN = '<svg viewBox="0 0 24 24" width="18" height="18" fill="none"><circle cx="12" cy="12" r="4.2" stroke="currentColor" stroke-width="1.6"/><path d="M12 2.5v2.4M12 19v2.5M4.2 4.2l1.7 1.7M18 18l1.7 1.7M2.5 12h2.4M19 12h2.5M4.2 19.7l1.7-1.7M18 6l1.7-1.7" stroke="currentColor" stroke-width="1.6" stroke-linecap="round"/></svg>';

  function initTheme() {
    const saved = localStorage.getItem(LS_THEME);
    const preferred = saved || (window.matchMedia?.("(prefers-color-scheme: light)").matches ? "light" : "dark");
    applyTheme(preferred);
    $("theme-toggle").addEventListener("click", () => {
      const next = document.documentElement.dataset.theme === "light" ? "dark" : "light";
      localStorage.setItem(LS_THEME, next);
      applyTheme(next);
    });
  }

  // -------------------------------------------------------------- wiring

  function wireEvents() {
    $("setup-form").addEventListener("submit", handleSetupSubmit);
    $("login-form").addEventListener("submit", handleLoginSubmit);
    $("login-forget").addEventListener("click", disconnectDevice);
    $("password-form").addEventListener("submit", handlePasswordChange);

    $("btn-lock").addEventListener("click", lockVault);
    $("btn-settings").addEventListener("click", () => $("settings-modal").classList.remove("hidden"));
    $("settings-close").addEventListener("click", () => $("settings-modal").classList.add("hidden"));
    $("btn-disconnect").addEventListener("click", disconnectDevice);

    $("btn-upload").addEventListener("click", () => $("file-input").click());
    $("file-input").addEventListener("change", (e) => {
      uploadFiles(e.target.files);
      e.target.value = "";
    });

    $("preview-close").addEventListener("click", closePreview);
    $("preview-prev").addEventListener("click", () => navigatePreview(-1));
    $("preview-next").addEventListener("click", () => navigatePreview(1));
    $("preview-modal").addEventListener("click", (e) => { if (e.target.id === "preview-modal") closePreview(); });
    $("preview-download").addEventListener("click", async () => {
      const entry = state.manifest.files[currentIndex];
      if (!entry) return;
      try {
        const url = await resolveObjectUrl(entry);
        const a = document.createElement("a");
        a.href = url;
        a.download = entry.name;
        document.body.appendChild(a);
        a.click();
        a.remove();
      } catch (e) { toast("Couldn't prepare download", "error"); }
    });
    $("preview-delete").addEventListener("click", () => {
      const entry = state.manifest.files[currentIndex];
      if (!entry) return;
      closePreview();
      deleteEntry(entry);
    });

    document.addEventListener("keydown", (e) => {
      if (["INPUT", "TEXTAREA"].includes(e.target.tagName)) return;
      if (!$("preview-modal").classList.contains("hidden")) {
        if (e.key === "Escape") closePreview();
        if (e.key === "ArrowLeft") navigatePreview(-1);
        if (e.key === "ArrowRight") navigatePreview(1);
      } else if (e.key === "Escape") {
        $("settings-modal").classList.add("hidden");
      }
    });

    ["mousemove", "keydown", "click", "touchstart"].forEach((evt) =>
      document.addEventListener(evt, resetInactivityTimer, { passive: true })
    );
    document.addEventListener("visibilitychange", () => {
      if (document.hidden) {
        stopPolling();
      } else {
        resetInactivityTimer();
        if (isDashboardActive() && state.masterKey) {
          pollManifest();
          startPolling();
        }
      }
    });

    const dz = $("dropzone");
    let dragDepth = 0;
    window.addEventListener("dragenter", (e) => {
      if (!isDashboardActive() || !e.dataTransfer?.types?.includes("Files")) return;
      dragDepth++;
      dz.classList.remove("hidden");
    });
    window.addEventListener("dragleave", () => {
      dragDepth = Math.max(0, dragDepth - 1);
      if (dragDepth === 0) dz.classList.add("hidden");
    });
    window.addEventListener("dragover", (e) => e.preventDefault());
    window.addEventListener("drop", (e) => {
      e.preventDefault();
      dragDepth = 0;
      dz.classList.add("hidden");
      if (isDashboardActive() && e.dataTransfer?.files?.length) uploadFiles(e.dataTransfer.files);
    });
  }

  // -------------------------------------------------------------- init

  async function init() {
    initTheme();
    wireEvents();
    if (haveCredentials()) {
      showScreen("login-screen");
      $("login-lede").textContent = "Loading your vault…";
      $("login-form").querySelector("button").disabled = true;
      try {
        await loadManifest();
        if (!state.manifest.wrappedKey) {
          const { salt, wrappedKey } = await createVaultKey(DEFAULT_PASSWORD);
          state.manifest.salt = salt;
          state.manifest.wrappedKey = wrappedKey;
          await saveManifest();
        }
        showLoginScreen();
      } catch (e) {
        $("login-lede").textContent = e.message || "Couldn't reach the vault. Check your connection and try again.";
      } finally {
        $("login-form").querySelector("button").disabled = false;
      }
    } else {
      showScreen("setup-screen");
    }
  }

  document.addEventListener("DOMContentLoaded", init);
})();