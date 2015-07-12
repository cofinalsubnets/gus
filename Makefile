CC := gcc
CFLAGS := -std=gnu11 -Os -Wall -Werror -s

gus: gus.c lib.h
	@${CC} -o $@ gus.c ${CFLAGS}

lib.h: lib.gus
	@echo "const char *GUS_LIB =" > $@
	@sed -e 's/"/\\"/g' -e 's/.*/"&"/' lib.gus >> $@
	@echo ";" >> $@

repl: gus
	@./gus

clean:
	@rm lib.h gus

.PHONY: clean repl
