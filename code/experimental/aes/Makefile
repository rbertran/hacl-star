HACL_HOME=../../..

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/aes128-bitslice.exe

test: all
	dist/aes128-bitslice.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include ../../../Makefile.local

#BASE_FLAGS+= -funroll-loops 4

CFLAGS += -I../../../../lib/c -march=native -mtune=native -O3
export CFLAGS

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.
dist/libaes.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o libaes.a $(BASE_FLAGS) -bundle 'Hacl.AES_128.BitSlice=*' \
	  -tmpdir dist -dast \
	  -add-include '"libintvector.h"' \
	  -skip-compilation

dist/aes128-bitslice-test.o : dist/Makefile.basic

dist/aes128-bitslice.exe: dist/aes128-bitslice-test.o dist/libaes.a

%.exe:
	$(CC) $(CFLAGS) -flto $^ -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
