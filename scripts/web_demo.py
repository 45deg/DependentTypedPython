"""Serve the built client-only DepPy demo as static files on localhost."""

import argparse
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
STATIC = ROOT / "web-demo"


class Handler(SimpleHTTPRequestHandler):
    def __init__(self, *args: object, **kwargs: object) -> None:
        super().__init__(*args, directory=str(STATIC), **kwargs)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--port", type=int, default=8000)
    args = parser.parse_args()
    if any(not (STATIC / name).is_file() for name in ("checker.wasm", "examples.json", "deppy-runtime.zip")):
        parser.error("先に python3 scripts/build_web_demo.py を実行してください。")
    server = ThreadingHTTPServer(("127.0.0.1", args.port), Handler)
    print(f"DepPy web demo: http://127.0.0.1:{server.server_port}/", flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()


if __name__ == "__main__":
    main()
