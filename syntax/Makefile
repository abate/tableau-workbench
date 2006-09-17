-include ../Makefile.conf

define PROJ_tableau
  USE_CAMLP4 = yes
  SOURCES := ast.ml parselib.ml tablib.ml extCommon.ml extTab.ml
  RESULT := pa_tableau
  export PACKS := str twb.types
endef
export PROJ_tableau

define PROJ_input
  USE_CAMLP4 = yes
  SOURCES := inputParser.ml
  RESULT := inputParser
  export PACKS := camlp4.gramlib str extlib twb.types
endef
export PROJ_input

ifndef SUBPROJS
  export SUBPROJS = tableau input
endif

all: bcl inputncl

inputncl:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=ncl SUBPROJS=input OCAMLFLAGS=

# Catch-all target will be applied to all subprojects automatically
%:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=$@ OCAMLFLAGS=
