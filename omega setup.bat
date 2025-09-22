@echo off
echo Installing common Python packages...

REM Upgrade pip
python -m pip install --upgrade pip

REM Install packages
pip install ^
    virtualenv ^
    ipython ^
    jupyter ^
    requests ^
    beautifulsoup4 ^
    pandas ^
    numpy ^
    matplotlib ^
    scipy ^
    scikit-learn ^
    openpyxl ^
    pillow ^
    pyinstaller ^
    pytest ^
    black ^
    flask ^
    django ^
    python-dotenv ^
    rich

echo.
echo All packages installed successfully.
pause
