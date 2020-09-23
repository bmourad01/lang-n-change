#!/bin/sh

BASEDIR="./lprolog/"
FILE=$1
BASENAME="$(basename ${FILE})"
MODNAME="${BASENAME%%.lan}"
DIR="${BASEDIR}${MODNAME}/"

# create the directories
mkdir -p $BASEDIR
mkdir -p $DIR

# compile the signature and module
dune exec bin/lprolog_sig.exe $FILE > "${DIR}${MODNAME}.sig"
dune exec bin/lprolog_mod.exe $FILE > "${DIR}${MODNAME}.mod"

CWD=$(pwd)
cd $DIR
# compile the actual program with Teyjus
(tjcc $MODNAME && tjlink $MODNAME); cd $CWD
