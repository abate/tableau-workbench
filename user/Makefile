include ../Makefile.conf

SOURCES := 
	
RESULT := twbusr
PACKS := twb.core twb.types twb.sequent twb.syntax 

OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all: byte-code

include $(OCAMLMAKEFILE)
