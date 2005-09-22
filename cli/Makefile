include ../Makefile.conf

SOURCES := \
	logic.ml \
	timer.ml \
	loader.ml \
	twb.ml
	
RESULT := twb
PACKS := dynlink unix extlib str twb.core twb.types twb.sequent twb.syntax
OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all:	byte-code
	
#nc:	native-code

-include $(OCAMLMAKEFILE)
