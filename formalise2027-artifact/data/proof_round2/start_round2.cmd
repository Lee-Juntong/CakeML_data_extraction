@echo off
echo Proof round 2 starts. Do not close this window. It runs for many hours.
powershell -NoProfile -ExecutionPolicy Bypass -File "%~dp0start_round2.ps1"
echo.
echo Finished. Read the messages above. Press any key to close.
pause >nul
