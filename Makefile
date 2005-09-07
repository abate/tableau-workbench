-include Makefile.conf

all:
	cd core && make && cp twbcore.* *.cmi ../twb/
	cd types && make && cp twbtypes* *.cmi ../twb/
	cd sequent && make && cp twbseq* *.cmi ../twb/
	cd syntax && make && cp twbintf* *.cmi ../twb/
	cd cli && make

nc:
	cd core && make ncl && cp twbcore.* *.cmi ../twb/
	cd types && make ncl && cp twbtypes.* *.cmi ../twb/
	cd sequent && make ncl && cp twbseq* *.cmi ../twb/
	cd syntax && make ncl && cp twbintf* *.cmi ../twb/
	cd cli && make nc

pnc:
	cd core && make pncl && cp twbcore.* *.cmi ../twb/
	cd types && make pncl && cp twbtypes.* *.cmi ../twb/
	cd sequent && make pncl && cp twbseq* *.cmi ../twb/
	cd cli && make pnc

pbc:
	cd core && make pbcl && cp twbcore.* *.cmi ../twb/
	cd types && make pbcl && cp twbtypes.* *.cmi ../twb/
	cd sequent && make && cp twbseq* *.cmi ../twb/
	cd cli && make pbc

dc:
	cd core && make dcl && cp twbcore.* *.cmi ../twb/
	cd types && make dcl && cp twbtypes.* *.cmi ../twb/
	cd sequent && make dc && cp twbseq* *.cmi ../twb/
	cd cli && make dc

clean:
	cd core && make clean
	cd types && make clean
	cd sequent && make clean
	cd syntax && make clean
	cd twb && rm *.cm*
	cd cli && make clean
