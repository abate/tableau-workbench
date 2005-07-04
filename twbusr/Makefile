-include ../Makefile.conf

SOURCES := \
	nodePattern.ml \
	partition.ml \
	build.ml \
	datatype.ml \
	user.ml \
	
RESULT := twbusr
PACKS := twblib twbdata

OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all: byte-code

-include $(OCAMLMAKEFILE)
