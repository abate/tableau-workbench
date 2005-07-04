OCAMLMAKEFILE = /usr/share/ocaml-tools/OCamlMakefile

SOURCES := \
	llist.ml \
	data.ml \
	store.ml \
	node.ml \
	tree.ml \
	rule.ml \
	zipper.ml \
	strategy.ml \
	visit.ml \
	
RESULT := twblib

PACKS := extlib

OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all: byte-code-library

include $(OCAMLMAKEFILE)
