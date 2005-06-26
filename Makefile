-include Makefile.conf

all:
	cd twblib && make
	cd twbdata && make
	cd twbusr && make 

clean:
	cd twblib && make clean
	cd twbdata && make clean
	cd twbusr && make clean
