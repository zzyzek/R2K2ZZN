# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

CC ?= cc
CFLAGS ?= -O2 -std=c11 -Wall -Wextra
LDLIBS = -lz

# The lookup table of look.c, read on first use unless ZZN_LOOK_DATA names another file.
LOOK_DATA ?= $(abspath ../data/look.json.gz)
LOOK_DEFS = -DZZN_LOOK_DATA_DEFAULT='"$(LOOK_DATA)"'

all: zzn libzzn.a example

libzzn.a: zzn.o look.o
	ar rcs $@ $^

zzn.o: zzn.c zzn.h look.h
	$(CC) $(CFLAGS) -c zzn.c

look.o: look.c look.h zzn.h
	$(CC) $(CFLAGS) $(LOOK_DEFS) -c look.c

zzn: cli.c libzzn.a look.h
	$(CC) $(CFLAGS) -o $@ cli.c libzzn.a $(LDLIBS)

example: example.c libzzn.a
	$(CC) $(CFLAGS) -o $@ example.c libzzn.a $(LDLIBS)

clean:
	rm -f zzn example zzn.o look.o libzzn.a

.PHONY: all clean
