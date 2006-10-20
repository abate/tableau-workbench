
USE_CAMLP4 = yes
SOURCES := \
	logic.ml \
	timer.ml \
	twb.ml
RESULT := twbcli
export PACKS := unix extlib str twb.parser twb.core twb.types twb.sequent

OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all: ncl

include $(OCAMLMAKEFILE)

