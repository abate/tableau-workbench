-include Makefile.conf

# as fast as we can !
export OCAMLFLAGS=-unsafe -noassert

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
	cd core && make && cp twbcore.* *.cm* ../twb/
	cd types && make && cp twbtypes.* *.cm* ../twb/
	cd sequent && make && cp *.cm* *.a ../twb/
	cd syntax && make && cp *.cm* *.a ../twb/
	cd cli && make && cp *.cm* *.a ../twb/
	cd utils && make && cp twbcompile ../library
	ranlib twb/*.a

clean:
	cd core && make clean
	cd types && make clean
	cd sequent && make clean
	cd syntax && make clean
	cd cli && make clean
	cd utils && make clean
	cd twb && rm -f *.cm* *.a *.o twb*

OCAMLLIBDIR=$(DESTDIR)`ocamlc -where`
INSTALLDIR=$(OCAMLLIBDIR)/twb

install:
	mkdir -p $(INSTALLDIR)
	cp twb/* $(INSTALLDIR)
	cp utils/twbcompile $(DESTDIR)/usr/bin/twbcompile

