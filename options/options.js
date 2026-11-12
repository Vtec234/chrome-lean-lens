/**
 * Options Page Controller
 */

document.addEventListener('DOMContentLoaded', () => {
  const hoverDelayInput = document.getElementById('hover-delay');
  const hoverDelayVal = document.getElementById('hover-delay-val');
  const themeSelect = document.getElementById('theme-select');
  const enablePRScanner = document.getElementById('enable-pr-scanner');
  const enableBuiltins = document.getElementById('enable-builtins');
  const enableLoogle = document.getElementById('enable-loogle');
  const enableLocalVerso = document.getElementById('enable-local-verso');
  const localVersoUrl = document.getElementById('local-verso-url');
  const testServerBtn = document.getElementById('test-server-btn');
  const serverTestResult = document.getElementById('server-test-result');
  const clearCacheBtn = document.getElementById('clear-cache-btn');
  const saveStatus = document.getElementById('save-status');

  const statTotal = document.getElementById('stat-total');
  const statCache = document.getElementById('stat-cache');
  const statLoogle = document.getElementById('stat-loogle');

  let currentSettings = {};

  // Load existing settings and stats
  chrome.runtime.sendMessage({ action: "GET_SETTINGS" }, (res) => {
    if (res && res.settings) {
      currentSettings = res.settings;
      hoverDelayInput.value = currentSettings.hoverDelay || 250;
      hoverDelayVal.textContent = `${hoverDelayInput.value}ms`;
      themeSelect.value = currentSettings.theme || 'auto';
      enablePRScanner.checked = currentSettings.enablePRScanner !== false;
      enableBuiltins.checked = currentSettings.enableBuiltins !== false;
      enableLoogle.checked = currentSettings.enableLoogle !== false;
      enableLocalVerso.checked = Boolean(currentSettings.enableLocalVerso);
      localVersoUrl.value = currentSettings.localVersoUrl || 'http://127.0.0.1:8000';
    }

    if (res && res.stats) {
      statTotal.textContent = res.stats.totalQueries || 0;
      statCache.textContent = res.stats.cacheHits || 0;
      statLoogle.textContent = res.stats.loogleHits || 0;
    }
  });

  // Save Settings Function
  function saveSettings() {
    currentSettings = {
      ...currentSettings,
      hoverDelay: parseInt(hoverDelayInput.value, 10),
      theme: themeSelect.value,
      enablePRScanner: enablePRScanner.checked,
      enableBuiltins: enableBuiltins.checked,
      enableLoogle: enableLoogle.checked,
      enableLocalVerso: enableLocalVerso.checked,
      localVersoUrl: localVersoUrl.value.trim()
    };

    chrome.runtime.sendMessage({ action: "SET_SETTINGS", settings: currentSettings }, () => {
      saveStatus.classList.add('visible');
      setTimeout(() => saveStatus.classList.remove('visible'), 1500);

      // Notify all tabs
      chrome.tabs.query({}, (tabs) => {
        tabs.forEach((tab) => {
          if (tab.id) {
            chrome.tabs.sendMessage(tab.id, { action: "SETTINGS_UPDATED" });
          }
        });
      });
    });
  }

  // Event Listeners for Live Updating
  hoverDelayInput.addEventListener('input', () => {
    hoverDelayVal.textContent = `${hoverDelayInput.value}ms`;
    saveSettings();
  });

  themeSelect.addEventListener('change', saveSettings);
  enablePRScanner.addEventListener('change', saveSettings);
  enableBuiltins.addEventListener('change', saveSettings);
  enableLoogle.addEventListener('change', saveSettings);
  enableLocalVerso.addEventListener('change', saveSettings);
  localVersoUrl.addEventListener('change', saveSettings);

  // Test Local Server Connection
  testServerBtn.addEventListener('click', () => {
    serverTestResult.textContent = 'Testing connection...';
    serverTestResult.style.color = '#8b949e';

    chrome.runtime.sendMessage(
      { action: "TEST_LOCAL_SERVER", url: localVersoUrl.value.trim() },
      (res) => {
        if (res && res.success) {
          serverTestResult.textContent = '✓ Connected! The local companion server is responding.';
          serverTestResult.style.color = '#3fb950';
        } else {
          serverTestResult.textContent = '✗ Could not connect to local server. Make sure companion server is running.';
          serverTestResult.style.color = '#f85149';
        }
      }
    );
  });

  // Clear Cache Button
  clearCacheBtn.addEventListener('click', () => {
    if (confirm('Are you sure you want to clear all cached definition data?')) {
      chrome.runtime.sendMessage({ action: "CLEAR_CACHE" }, () => {
        statCache.textContent = '0';
        alert('Cache cleared successfully.');
      });
    }
  });
});
