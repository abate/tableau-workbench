include ../Makefile.conf

SOURCES := \
	sbl.ml \
	nodePattern.ml \
	build.ml \
	partition.ml \
	ruleContext.ml \
	userData.ml \
	datatype.ml \
	outputBroker.ml \
	userRule.ml \
	
#	userStrategy.ml

RESULT := twbseq
PACKS := twb.core twb.types

OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all: ncl

include $(OCAMLMAKEFILE)
