#!/bin/bash 
#set -x
. ../Makefile.conf

#STRLIB=`ocamlfind query str`/str.cma
#EXTLIB=`ocamlfind query extlib`/extLib.cma
#camlp4o $STRLIB $EXTLIB ../syntax/tableau.cmo pr_o.cmo $1 > /tmp/${1//.ml}_pp.ml
#ocamlfind ocamlopt -package twb.tableau,twb.thelot,twb.cli -syntax camlp4o -linkpkg -p -o ${1//.ml} $1
#ocamlfind ocamlopt -package twb.thelot,twb.cli -linkpkg -p -o ${1//.ml} /tmp/${1//.ml}_pp.ml
#../twb/twb.cmx
#ocamlfind ocamlmktop -o toploop -package twb.tableau,findlib -syntax camlp4o -linkpkg -o ${1//.ml}top $1

./compile $@
