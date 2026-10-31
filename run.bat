@echo off
rem UniNet Dashboard — first run creates the virtualenv, installs requirements, starts the app
cd /d "%~dp0"

if not exist ".venv\Scripts\python.exe" (
    echo Creating virtualenv...
    python -m venv .venv || py -3 -m venv .venv || (echo Python 3.10+ required & pause & exit /b 1)
)

call ".venv\Scripts\activate.bat"

echo Installing requirements...
python -m pip install --quiet --upgrade pip
python -m pip install --quiet -r requirements.txt

echo Starting UniNet Dashboard on http://127.0.0.1:5001 ...
python run.py
pause
