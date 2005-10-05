include ../Makefile.conf

define PROJ_twbbc
USE_CAMLP4 = yes
SOURCES := \
	logic.ml \
	timer.ml \
	loader.ml \
	twb.ml
RESULT := twb
export PACKS := dynlink unix extlib str twb.core twb.types twb.sequent twb.syntax
endef
export PROJ_twbbc

define PROJ_twbnc
USE_CAMLP4 = yes
PPFLAGS = -DNATIVE
SOURCES := \
	logic.ml \
	timer.ml \
	twb.ml
RESULT := .empty
export PACKS := unix extlib str twb.core twb.types twb.sequent twb.syntax
endef
export PROJ_twbnc

OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all: twbbc twbnc

twbbc:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=bc SUBPROJS=twbbc

twbnc:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=nc SUBPROJS=twbnc
		
twbpbc:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=pbc SUBPROJS=twbbc

twbpnc:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=pnc SUBPROJS=twbnc
	
clean:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=clean SUBPROJS="twbnc twbbc"
		
