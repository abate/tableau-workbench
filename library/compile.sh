#!/bin/bash 

. ../Makefile.conf

STDLIB=`ocamlfind printconf stdlib`

if [ -f $STDLIB/extlib/extLib.cma ]; then
    DESTDIR=$STDLIB
else
    DESTDIR=`ocamlfind printconf destdir`
fi

camlp4o $STDLIB/str.cma $DESTDIR/extlib/extLib.cma ../syntax/tableau.cmo pr_o.cmo $1 > ${1//.ml}-pp.ml

ocamlfind ocamlc -package twb.core -g -c -o ${1//.ml} ${1//.ml}-pp.ml
