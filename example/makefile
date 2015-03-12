all:
	gcc ndfs.c -o ndfs -std=c99 -O0 -g -save-temps=obj
	clang -c ndfs.c -emit-llvm -std=c99 -O0 -g
	llvm-dis ndfs.bc

test:
	./test.sh 5000

clean:
	rm -rf ndfs
