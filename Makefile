-include Makefile.conf

all:
	cd twblib && make
	cd twbdata && make
	cd twbusr && make 

nc:
	cd twblib && make ncl 
	cd twbdata && make ncl
	cd twbusr && make nc

pnc:
	cd twblib && make pncl
	cd twbdata && make pncl
	cd twbusr && make pnc

pbc:
	cd twblib && make pbcl
	cd twbdata && make pbcl
	cd twbusr && make pbc

dc:
	cd twblib && make dcl
	cd twbdata && make dcl
	cd twbusr && make dc

clean:
	cd twblib && make clean
	cd twbdata && make clean
	cd twbusr && make clean
