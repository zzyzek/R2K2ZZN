# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

CC ?= cc
CFLAGS ?= -O2 -std=c11 -Wall -Wextra

all: zzn libzzn.a example

libzzn.a: zzn.o
	ar rcs $@ $^

zzn.o: zzn.c zzn.h
	$(CC) $(CFLAGS) -c zzn.c

zzn: cli.c libzzn.a
	$(CC) $(CFLAGS) -o $@ cli.c libzzn.a

example: example.c libzzn.a
	$(CC) $(CFLAGS) -o $@ example.c libzzn.a

clean:
	rm -f zzn example zzn.o libzzn.a

.PHONY: all clean
