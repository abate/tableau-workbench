include ../Makefile.conf

define PROJ_twbncl
USE_CAMLP4 = yes
PPFLAGS = -DNATIVE
SOURCES := \
	logic.ml \
	timer.ml \
	twb.ml
RESULT := twbcli
export PACKS := unix extlib str twb.parser twb.core twb.types twb.sequent
endef
export PROJ_twbncl

OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all: twbncl

twbncl:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=ncl SUBPROJS=twbncl
		
clean:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=clean SUBPROJS="twbnc twbbc"
		
