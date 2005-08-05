-include ../Makefile.conf

# ONLY __CMO__ FILES HERE !!!!!!!!!!!!!!
# everything listed in pretargets gets removed by make clean!!!!!!!!!!!!
#PRE_TARGETS := \
#	tableau.cmo tableau.cmi inputParser.cmo inputParser.cmi \
#

USE_CAMLP4 := yes
PACKS := str extlib twb.types

SOURCES= tableau.ml inputParser.ml

RESULT := twbintf
TRASJ := *.annot *.cm*

OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all: byte-code-library
	
-include $(OCAMLMAKEFILE)
