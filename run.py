# ─── Force console output to UTF-8 (Windows: cp1252 cannot encode Persian) ───
import sys
import io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')
sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding='utf-8', errors='replace')

import os
# app.py is the monolith (Flask + SocketIO app for the class-schedule dashboard)
from app import app, socketio

if __name__ == '__main__':
    port = int(os.environ.get('PORT', 5001))
    debug = os.environ.get('FLASK_DEBUG', 'false').lower() == 'true'
    host = os.environ.get('HOST', '127.0.0.1')
    print(f"\n{'='*50}")
    print(f"  UniNet Dashboard — local run")
    print(f"  Address: http://{host}:{port}")
    print(f"{'='*50}\n")
    socketio.run(app, host=host, port=port, debug=debug)
