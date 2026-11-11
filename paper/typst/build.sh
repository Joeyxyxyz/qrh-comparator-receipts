#!/usr/bin/env bash
# Build the paper. Either with the Typst command line tool (0.15):
#     typst compile --root . main.typ main.pdf
# or, as the deposited PDF was built, with the Python wheel `typst` 0.15.2 from PyPI unpacked into a folder:
#     ./build.sh /path/to/unpacked-wheel     (the folder that contains typst/__init__.py)
# The fonts New Computer Modern and DejaVu Sans Mono ship with Typst; the two figures use DejaVu Sans, which must be installed.
set -eu
cd "$(dirname "$0")"
if [ $# -ge 1 ]; then
  python3 -I -c "import sys; sys.path.insert(0, sys.argv[1]); import typst; typst.compile('main.typ', output='main.pdf')" "$1"
else
  typst compile --root . main.typ main.pdf
fi
echo "built main.pdf"
