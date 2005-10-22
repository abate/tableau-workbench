#!/bin/bash 

. ../Makefile.conf

STDLIB=`ocamlfind printconf stdlib`

if [ -f $STDLIB/extlib/extLib.cma ]; then
    DESTDIR=$STDLIB
else
    DESTDIR=`ocamlfind printconf destdir`
fi

rm ${1//.ml}-pp.ml

camlp4o $STDLIB/str.cma $DESTDIR/extlib/extLib.cma ../syntax/tableau.cmo pr_o.cmo $1 > ${1//.ml}-pp.ml

ocamlfind ocamlc -package twb.core -g -c -o ${1//.ml} ${1//.ml}-pp.ml

ocamlfind ocamlopt -package unix,str,twb.core,twb.types,twb.sequent,twb.syntax -linkpkg -o ${1//.ml} -p ../cli/timer.cmx ../cli/logic.cmx ${1//.ml}-pp.ml ../cli/twb.cmx
