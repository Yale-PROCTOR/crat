#!/bin/bash

set -e

script_dir="$(dirname "$0")"
. "$script_dir/prepare"

mkdir "$1/$name/mod"
cp "$2/$name/target/$dir/mod_mod_main" "$1/$name/mod/mod" || \
cp "$2/$name/target/$dir/rmod_rmod_main" "$1/$name/mod/mod"

cd "$1/$name"
make check-TESTS
