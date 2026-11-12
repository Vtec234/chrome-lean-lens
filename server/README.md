# Verso Local Companion Server

The Verso Local Companion Server is an optional lightweight helper script designed for users reviewing pull requests or code involving private Lean repositories or offline development environments.

## Features
- Runs with zero external dependencies (pure standard library Python 3).
- Exposes `http://127.0.0.1:8000/lookup?name=<symbol>`.
- Cross-Origin Resource Sharing (CORS) enabled for direct communication with the Chrome extension.
- Integrates with local Lean source trees and Lake builds.

## How to Run

1. Navigate to your local Lean 4 project:
   ```bash
   cd /path/to/my-lean-project
   ```

2. Start the companion server:
   ```bash
   python3 /path/to/chrome-verso/server/companion_server.py --port 8000
   ```

3. In the Chrome extension options page:
   - Check **"Enable Local Verso Companion Server"**
   - Click **"Test Connection"** to verify that `http://127.0.0.1:8000` is active.
