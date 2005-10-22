include ../Makefile.conf

SOURCES := \
	nodePattern.ml \
	build.ml \
	partition.ml \
	ruleContext.ml \
	sbl.ml \
	datatype.ml \
	outputBroker.ml \
	userRule.ml \
	
RESULT := twbseq
PACKS := twb.core twb.types

OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all: byte-code-library

include $(OCAMLMAKEFILE)
