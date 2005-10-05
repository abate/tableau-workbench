-include Makefile.conf

all: bc

bc:
	cd core && make bcl && cp twbcore.* *.cmi ../twb/
	cd types && make bcl && cp twbtypes* *.cmi ../twb/
	cd sequent && make bcl && cp twbseq* *.cmi ../twb/
	cd syntax && make bcl && cp twbintf* *.cmi ../twb/
	cd cli && make twbbc && cp logic.cm* ../twb/

nc:
	cd core && make ncl && cp twbcore.* *.cmi ../twb/
	cd types && make ncl && cp twbtypes.* *.cmi ../twb/
	cd sequent && make ncl && cp twbseq* *.cmi ../twb/
	cd syntax && make ncl && cp twbintf* *.cmi ../twb/
	cd cli && make twbnc && cp *.cmi *.cmx ../twb/

pnc:
	cd core && make pncl && cp twbcore.* *.cmi ../twb/
	cd types && make pncl && cp twbtypes.* *.cmi ../twb/
	cd sequent && make pncl && cp twbseq* *.cmi ../twb/
	cd syntax && make pncl && cp twbintf* *.cmi ../twb/
	cd cli && make twbpnc && cp logic.* ../twb/

pbc:
	cd core && make pbcl && cp twbcore.* *.cmi ../twb/
	cd types && make pbcl && cp twbtypes.* *.cmi ../twb/
	cd sequent && make pbcl && cp twbseq* *.cmi ../twb/
	cd syntax && make pbcl && cp twbintf* *.cmi ../twb/
	cd cli && make twbpbc && cp logic.* ../twb/

dc:
	cd core && make dcl && cp twbcore.* *.cmi ../twb/
	cd types && make dcl && cp twbtypes.* *.cmi ../twb/
	cd sequent && make dcl && cp twbseq* *.cmi ../twb/
	cd syntax && make dcl && cp twbintf* *.cmi ../twb/
	cd cli && make dc && cp logic.* ../twb/

clean:
	cd core && make clean
	cd types && make clean
	cd sequent && make clean
	cd syntax && make clean
	cd cli && make clean
	cd twb && rm *.cm* *.a twb*
