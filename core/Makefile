OCAMLMAKEFILE = /usr/share/ocaml-tools/OCamlMakefile

SOURCES := \
	llist.ml \
	data.ml \
	node.ml \
	tree.ml \
	rule.ml \
	strategy.ml \
	visit.ml \
	
RESULT := twbcore

PACKS := extlib

OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all: byte-code-library

include $(OCAMLMAKEFILE)
