include ../Makefile.conf

SOURCES := \
	twb.ml
	
RESULT := twb
PACKS := twb.core twb.types twb.sequent twb.syntax dynlink unix extlib

OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all: byte-code

include $(OCAMLMAKEFILE)
