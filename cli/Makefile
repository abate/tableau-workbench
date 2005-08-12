include ../Makefile.conf

SOURCES := \
	timer.ml \
	loader.ml \
	twb.ml
	
RESULT := twb
PACKS := twb.core twb.types twb.sequent twb.syntax dynlink unix extlib str camlp4

OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all: byte-code

include $(OCAMLMAKEFILE)
