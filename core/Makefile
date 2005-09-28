include ../Makefile.conf

SOURCES := \
	llist.mli \
	llist.ml \
	data.mli \
	data.ml \
	node.mli \
	node.ml \
	tree.mli \
	tree.ml \
	rule.mli \
	rule.ml \
	strategy.mli \
	strategy.ml \
	visit.mli \
	visit.ml \
	
RESULT := twbcore

PACKS := extlib

OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all: byte-code-library

include $(OCAMLMAKEFILE)
