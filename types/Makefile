include ../Makefile.conf

SOURCES := \
	basictype.ml \
	sets.ml \
      	listobj.ml \
	comptypes.ml \
	gmap.ml \
	hmap.ml \

RESULT := twbtypes
LIBDIRS := ../twb

OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all: byte-code-library

include $(OCAMLMAKEFILE)
