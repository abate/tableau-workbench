-include Makefile.conf

all:
	cd twblib && make
	cd twbdata && make
	cd twbusr && make 

pnc:
	cd twblib && make pncl
	cd twbdata && make pncl
	cd twbusr && make pnc

pbc:
	cd twblib && make pbcl
	cd twbdata && make pbcl
	cd twbusr && make pbc

clean:
	cd twblib && make clean
	cd twbdata && make clean
	cd twbusr && make clean
