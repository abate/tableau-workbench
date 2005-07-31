include ../Makefile.conf

SOURCES := \
	datatype.ml \
	aa.ml \
	
RESULT := twbusr
PACKS := twb.core twb.types twb.sequent twb.syntax camlp4

OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all: byte-code

include $(OCAMLMAKEFILE)
