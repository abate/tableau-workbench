
USE_CAMLP4 = yes
SOURCES := \
        prover.ml \
        twbCgi.ml
RESULT := twbcgi
export PACKS := unix str twb.parser twb.core twb.types twb.sequent xmlrpc

OCAMLDOC := ocamlfind ocamldoc -package $(PACKS)
DOC_FILES := $(SOURCES)

all: prover ncl

prover: prover.idl
	oxridl prover.idl


include $(OCAMLMAKEFILE)

