#!/usr/bin/env bash
__doc__='
Installs packages to build the tex on ubuntu
'
set -euo pipefail

if ! command -v apt-get >/dev/null 2>&1; then
    echo "This installer currently supports Ubuntu/Debian systems with apt-get." >&2
    exit 1
fi

export DEBIAN_FRONTEND="${DEBIAN_FRONTEND:-noninteractive}"

sudo apt-get update
sudo apt-get install -y --no-install-recommends \
    latexmk \
    texlive-latex-base \
    texlive-latex-recommended \
    texlive-latex-extra \
    texlive-bibtex-extra \
    texlive-fonts-recommended \
    lmodern
