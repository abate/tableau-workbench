-include ../Makefile.conf

SOURCES := \
	basictype.ml \
      	listobj.ml \
	sets.ml \
	comptypes.ml \
	fmap.ml \

RESULT := twbdata
PACKS := twblib

OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all: byte-code-library

-include $(OCAMLMAKEFILE)
