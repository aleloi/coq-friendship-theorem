#!/bin/bash

TMP=$(mktemp -d); git clone https://github.com/coq-community/templates.git $TMP
$TMP/generate.sh
pandoc -s -o resources/index.html resources/index.md
make coqdoc

