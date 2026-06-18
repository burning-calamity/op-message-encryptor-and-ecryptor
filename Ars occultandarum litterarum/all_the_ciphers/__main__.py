from __future__ import annotations

import sys
from .core import cli_main

if __name__ == "__main__":
    raise SystemExit(cli_main(sys.argv[1:]))
