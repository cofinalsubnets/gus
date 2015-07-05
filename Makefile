CC := gcc
CFLAGS := -Os -Wall -Werror -s

mus: mus.c
	${CC} -o $@ mus.c ${CFLAGS}
