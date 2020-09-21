#!/bin/sh

DIR="./lprolog/"
FILE=$1
BASENAME="$(basename ${FILE})"

mkdir -p $DIR

dune exec bin/lprolog_sig.exe $FILE > "${DIR}${BASENAME%%.lan}.sig"
dune exec bin/lprolog_mod.exe $FILE > "${DIR}${BASENAME%%.lan}.mod"
