#!/bin/sh
set -eu
cd "$(dirname "$0")"
luajit emit.lua -o editor.c editor.let
"${CC:-cc}" -std=c11 -Wall -Wextra -Werror -O2 -o editor editor.c host.c
