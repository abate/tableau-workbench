OCAMLMAKEFILE = /usr/share/ocaml-tools/OCamlMakefile

SOURCES := \
	llist.ml \
	data.ml \
	pattern.ml \
	store.ml \
	node.ml \
	matchnode.ml \
	tree.ml \
	rule.ml \
	zipper.ml \
	strategy.ml \
	visit.ml \
	
#	builder.ml backtrack.ml partition.ml	
	
# extdata/mixtype.ml extdata/listobjV.ml extdata/listobj.ml extdata/listobjSubtype.ml extdata/sets.ml extdata/setofsets.ml extdata/setoftupleset.ml 
RESULT := twb3lib

PACKS := extlib

OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all: byte-code-library

include $(OCAMLMAKEFILE)
