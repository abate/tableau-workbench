-include ../Makefile.conf

SOURCES := \
	datatype.ml \
	user.ml \
	
RESULT := twbusr
PACKS := twb.core twb.types twb.sequent

OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all: byte-code

-include $(OCAMLMAKEFILE)
