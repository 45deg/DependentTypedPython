import sys
from pathlib import Path

DOCS = Path(__file__).resolve().parent
sys.path.insert(0, str(DOCS / "_ext"))

project = "DepPy"
author = "DepPy contributors"
extensions = ["sphinx.ext.mathjax", "deppy_api"]
exclude_patterns = ["_build"]
html_theme = "alabaster"
root_doc = "index"
