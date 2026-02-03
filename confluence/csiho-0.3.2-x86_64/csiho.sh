#!/bin/sh

DIR=$(dirname "$(readlink -f "$0")")

OCAMLRUNPARAM="${OCAMLRUNPARAM} s=96k" \
  "$DIR"/csiho -c "$DIR"/ho.conf -s COMP -C HOCR "$@"
