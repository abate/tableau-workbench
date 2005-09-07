#!/bin/bash 

. ../Makefile.conf

ocamlfind ocamlc -package dynlink,unix,extlib,str,twb.core,twb.types,twb.sequent,twb.syntax -linkpkg -o twb-$1 timer.cmo loader.cmo ../library/$1.cmo twb.ml
