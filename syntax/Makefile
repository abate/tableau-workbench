-include ../Makefile.conf

define PROJ_tableau
  USE_CAMLP4 = yes
  SOURCES := tableau.ml
  RESULT := tableau
  export PACKS := str extlib twb.types
endef
export PROJ_tableau

define PROJ_sequent
  USE_CAMLP4 = yes
  SOURCES := sequent.ml
  RESULT := sequent
  export PACKS := str extlib twb.types
endef
export PROJ_sequent

define PROJ_input
  USE_CAMLP4 = yes
  SOURCES := inputParser.ml
  RESULT := inputParser
  export PACKS := camlp4.gramlib str extlib twb.types
endef
export PROJ_input

ifndef SUBPROJS
  export SUBPROJS = tableau sequent input
endif

all: bcl inputncl

inputncl:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=ncl SUBPROJS=input

# Catch-all target will be applied to all subprojects automatically
%:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=$@
