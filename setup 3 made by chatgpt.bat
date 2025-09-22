@echo off
echo Installing a massive list of Python packages...
python -m pip install --upgrade pip

pip install ^
    virtualenv ipython jupyter pip-tools python-dotenv rich typer loguru ^
    pandas numpy matplotlib seaborn plotly openpyxl xlrd tabulate pyarrow polars ^
    scikit-learn xgboost lightgbm tensorflow keras torch transformers sentence-transformers opencv-python pytorch-lightning ^
    flask django fastapi gunicorn uvicorn httpx requests aiohttp jinja2 ^
    beautifulsoup4 lxml selenium playwright scrapy pyppeteer mechanize ^
    setuptools wheel pyinstaller build twine ^
    paramiko cryptography pycryptodome scapy "requests[socks]" ^
    schedule apscheduler watchdog ^
    pytest pytest-cov tox coverage hypothesis ^
    pillow tqdm colorama faker pyyaml json5 markdown click pyautogui keyboard pynput pathlib toml

echo.
echo MASSIVE package installation complete.
pause
