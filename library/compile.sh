#!/bin/bash 

. ../Makefile.conf

camlp4o /usr/lib/ocaml/3.08.3/str.cma /usr/lib/ocaml/3.08.3/extlib/extLib.cma ../syntax/tableau.cmo pr_o.cmo $1 > ${1//.ml}-pp.ml

ocamlfind ocamlc -package twb.core -c -o ${1//.ml} ${1//.ml}-pp.ml
