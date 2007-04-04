
USE_CAMLP4 = yes
SOURCES := \
	timer.ml \
	twbMain.ml
RESULT := twbcli
export PACKS := unix str twb.parser twb.core twb.types twb.sequent

#	logic.ml

OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all: ncl

include $(OCAMLMAKEFILE)

