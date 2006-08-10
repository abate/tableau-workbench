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

nc:
	cd core && make ncl && cp twbcore.* *.cmi ../twb/
	cd types && make ncl && cp twbtypes.* *.cmi ../twb/
	cd sequent && make ncl && cp twbseq* *.cmi ../twb/
	cd syntax && make bcl ncl && cp *.cm* *.a ../twb/
	cd cli && make twbncl && cp *.cm* *.a *.o ../twb/
	cd utils && make && cp twbcompile ../library
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

