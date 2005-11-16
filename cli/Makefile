include ../Makefile.conf

define PROJ_twbbc
USE_CAMLP4 = yes
SOURCES := \
	logic.ml \
	timer.ml \
	loader.ml \
	twb.ml
RESULT := twb
export PACKS := dynlink unix extlib str twb.parser twb.core twb.types twb.sequent 
endef
export PROJ_twbbc

define PROJ_twbbcl
USE_CAMLP4 = yes
SOURCES := \
	logic.ml \
	timer.ml 
RESULT := twbcli
export PACKS := unix extlib str twb.parser twb.core twb.types twb.sequent
endef
export PROJ_twbbcl

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

all: twbbcl twbncl

twbbc:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=bc SUBPROJS=twbbc

twbbcl:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=bcl SUBPROJS=twbbcl

twbncl:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=ncl SUBPROJS=twbncl
		
twbpbc:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=pbc SUBPROJS=twbbc

twbpnc:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=pncl SUBPROJS=twbncl
	
clean:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=clean SUBPROJS="twbnc twbbc"
		
