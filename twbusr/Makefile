-include ../Makefile.conf

SOURCES := \
	datatype.ml \
	user.ml
	
RESULT := twbusr
PACKS := twblib twbdata

OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all: byte-code-library

-include $(OCAMLMAKEFILE)
