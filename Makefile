-include Makefile.conf

ifndef NOEXTLIB
all: nc utils
endif

ifdef NOEXTLIB
all: extlib nc utils
endif

extlib:
	cd extlib && make && make opt

utils: 
	cd utils && make && cp twbcompile ../library

bc:
	cd core && make bcl && cp twbcore.* *.cmi ../twb/
	cd types && make bcl && cp twbtypes* *.cmi ../twb/
	cd sequent && make bcl && cp twbseq* *.cmi ../twb/
	cd syntax && make bcl && cp *.cm* *.a  ../twb/
	cd cli && make twbbc && cp *.cmi *.cmxa *.a ../twb/
	ranlib twb/*.a

nc:
	cd core && make ncl && cp twbcore.* *.cmi ../twb/
	cd types && make ncl && cp twbtypes.* *.cmi ../twb/
	cd sequent && make ncl && cp twbseq* *.cmi ../twb/
	cd syntax && make bcl ncl && cp *.cm* *.a ../twb/
	cd cli && make twbncl && cp *.cm* *.a *.o ../twb/
	cd utils && make && cp twbcompile ../library
	ranlib twb/*.a

pnc:
	cd core && make pncl && cp twbcore.* *.cmi ../twb/
	cd types && make pncl && cp twbtypes.* *.cmi ../twb/
	cd sequent && make pncl && cp twbseq* *.cmi ../twb/
	cd syntax && make pncl && cp *.cmxa *.cmi ../twb/
	cd cli && make twbpnc && cp logic.* ../twb/
	ranlib twb/*.a

pbc:
	cd core && make pbcl && cp twbcore.* *.cmi ../twb/
	cd types && make pbcl && cp twbtypes.* *.cmi ../twb/
	cd sequent && make pbcl && cp twbseq* *.cmi ../twb/
	cd syntax && make pbcl && cp *.cma *.cmi ../twb/
	cd cli && make twbpbc && cp logic.* ../twb/
	ranlib twb/*.a

dc:
	cd core && make dcl && cp twbcore.* *.cmi ../twb/
	cd types && make dcl && cp twbtypes.* *.cmi ../twb/
	cd sequent && make dcl && cp twbseq* *.cmi ../twb/
	cd syntax && make dcl && cp *.cma *.cmi ../twb/
	cd cli && make dc && cp logic.* ../twb/
	ranlib twb/*.a

clean:
	cd core && make clean
	cd types && make clean
	cd sequent && make clean
	cd syntax && make clean
	cd cli && make clean
	cd utils && make clean
	cd twb && rm *.cm* *.a twb*

OCAMLLIBDIR=$(DESTDIR)`ocamlc -where`
INSTALLDIR=$(OCAMLLIBDIR)/twb

install:
	mkdir -p $(INSTALLDIR)
	cp twb/* $(INSTALLDIR)
	cp utils/twbcompile $(DESTDIR)/usr/bin/twbcompile

