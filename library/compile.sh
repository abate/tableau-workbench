#!/bin/bash 

ocamlfind ocamlc -package twb.core -c -pp "camlp4o /usr/lib/ocaml/3.08.3/str.cma /usr/lib/ocaml/3.08.3/extlib/extLib.cma ../syntax/tableau.cmo pr_o.cmo" $1
