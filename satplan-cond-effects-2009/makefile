#!/bin/sh
#
# Makefile for num2sat
#


####### FLAGS

TYPE	= 
ADDONS	= 

CC      = gcc

CFLAGS	= -O6 -Wall -g -ansi $(TYPE) $(ADDONS)
#CFLAGS	= -O6 -Wall -g -pg -ansi $(TYPE) $(ADDONS)
#CFLAGS	= -Wall -g -ansi $(TYPE) $(ADDONS)
# -g -pg

LIBS    = -lm


####### Files

PDDL_PARSER_SRC	= scan-fct_pddl.tab.c \
	scan-ops_pddl.tab.c \
	scan-probname.tab.c \
	lex.fct_pddl.c \
	lex.ops_pddl.c 

PDDL_PARSER_OBJ = scan-fct_pddl.tab.o \
	scan-ops_pddl.tab.o 


SOURCES 	= main.c \
	memory.c \
	output.c \
	parse.c \
	inst_pre.c \
	inst_easy.c \
	inst_hard.c \
	inst_final.c \
	RPG.c \
	RPGvaluetuples.c \
	CNF.c \
	HCNF.c

OBJECTS 	= $(SOURCES:.c=.o)

####### Implicit rules

.SUFFIXES:

.SUFFIXES: .c .o

.c.o:; $(CC) -c $(CFLAGS) $<

####### Build rules


num2sat: $(OBJECTS) $(PDDL_PARSER_OBJ)
	$(CC) -o num2sat $(OBJECTS) $(PDDL_PARSER_OBJ) $(CFLAGS) $(LIBS)

# pddl syntax
scan-fct_pddl.tab.c: scan-fct_pddl.y lex.fct_pddl.c
	bison -pfct_pddl -bscan-fct_pddl scan-fct_pddl.y

scan-ops_pddl.tab.c: scan-ops_pddl.y lex.ops_pddl.c
	bison -pops_pddl -bscan-ops_pddl scan-ops_pddl.y

lex.fct_pddl.c: lex-fct_pddl.l
	flex -Pfct_pddl lex-fct_pddl.l

lex.ops_pddl.c: lex-ops_pddl.l
	flex -Pops_pddl lex-ops_pddl.l


# misc
clean:
	rm -f *.o *.bak *~ *% core *_pure_p9_c0_400.o.warnings \
        \#*\# $(RES_PARSER_SRC) $(PDDL_PARSER_SRC)

veryclean: clean
	rm -f num2sat L* graph.* *.symbex gmon.out \
	$(PDDL_PARSER_SRC) \
	lex.fct_pddl.c lex.ops_pddl.c lex.probname.c \
	*.output semantic.cache CNF

depend:
	makedepend -- $(SOURCES) $(PDDL_PARSER_SRC)

lint:
	lclint -booltype Bool $(SOURCES) 2> output.lint

# DO NOT DELETE

main.o: num2sat.h /usr/include/stdlib.h /usr/include/features.h
main.o: /usr/include/sys/cdefs.h /usr/include/bits/wordsize.h
main.o: /usr/include/gnu/stubs.h /usr/include/gnu/stubs-32.h
main.o: /usr/include/sys/types.h /usr/include/bits/types.h
main.o: /usr/include/bits/typesizes.h /usr/include/time.h
main.o: /usr/include/endian.h /usr/include/bits/endian.h
main.o: /usr/include/sys/select.h /usr/include/bits/select.h
main.o: /usr/include/bits/sigset.h /usr/include/bits/time.h
main.o: /usr/include/sys/sysmacros.h /usr/include/bits/pthreadtypes.h
main.o: /usr/include/alloca.h /usr/include/stdio.h /usr/include/libio.h
main.o: /usr/include/_G_config.h /usr/include/wchar.h
main.o: /usr/include/bits/stdio_lim.h /usr/include/bits/sys_errlist.h
main.o: /usr/include/strings.h /usr/include/string.h /usr/include/ctype.h
main.o: /usr/include/sys/timeb.h /usr/include/sys/times.h memory.h output.h
main.o: parse.h inst_pre.h inst_easy.h inst_hard.h inst_final.h RPG.h
main.o: RPGvaluetuples.h CNF.h HCNF.h
memory.o: num2sat.h /usr/include/stdlib.h /usr/include/features.h
memory.o: /usr/include/sys/cdefs.h /usr/include/bits/wordsize.h
memory.o: /usr/include/gnu/stubs.h /usr/include/gnu/stubs-32.h
memory.o: /usr/include/sys/types.h /usr/include/bits/types.h
memory.o: /usr/include/bits/typesizes.h /usr/include/time.h
memory.o: /usr/include/endian.h /usr/include/bits/endian.h
memory.o: /usr/include/sys/select.h /usr/include/bits/select.h
memory.o: /usr/include/bits/sigset.h /usr/include/bits/time.h
memory.o: /usr/include/sys/sysmacros.h /usr/include/bits/pthreadtypes.h
memory.o: /usr/include/alloca.h /usr/include/stdio.h /usr/include/libio.h
memory.o: /usr/include/_G_config.h /usr/include/wchar.h
memory.o: /usr/include/bits/stdio_lim.h /usr/include/bits/sys_errlist.h
memory.o: /usr/include/strings.h /usr/include/string.h /usr/include/ctype.h
memory.o: /usr/include/sys/timeb.h /usr/include/sys/times.h memory.h
memory.o: inst_pre.h
output.o: num2sat.h /usr/include/stdlib.h /usr/include/features.h
output.o: /usr/include/sys/cdefs.h /usr/include/bits/wordsize.h
output.o: /usr/include/gnu/stubs.h /usr/include/gnu/stubs-32.h
output.o: /usr/include/sys/types.h /usr/include/bits/types.h
output.o: /usr/include/bits/typesizes.h /usr/include/time.h
output.o: /usr/include/endian.h /usr/include/bits/endian.h
output.o: /usr/include/sys/select.h /usr/include/bits/select.h
output.o: /usr/include/bits/sigset.h /usr/include/bits/time.h
output.o: /usr/include/sys/sysmacros.h /usr/include/bits/pthreadtypes.h
output.o: /usr/include/alloca.h /usr/include/stdio.h /usr/include/libio.h
output.o: /usr/include/_G_config.h /usr/include/wchar.h
output.o: /usr/include/bits/stdio_lim.h /usr/include/bits/sys_errlist.h
output.o: /usr/include/strings.h /usr/include/string.h /usr/include/ctype.h
output.o: /usr/include/sys/timeb.h /usr/include/sys/times.h output.h
parse.o: num2sat.h /usr/include/stdlib.h /usr/include/features.h
parse.o: /usr/include/sys/cdefs.h /usr/include/bits/wordsize.h
parse.o: /usr/include/gnu/stubs.h /usr/include/gnu/stubs-32.h
parse.o: /usr/include/sys/types.h /usr/include/bits/types.h
parse.o: /usr/include/bits/typesizes.h /usr/include/time.h
parse.o: /usr/include/endian.h /usr/include/bits/endian.h
parse.o: /usr/include/sys/select.h /usr/include/bits/select.h
parse.o: /usr/include/bits/sigset.h /usr/include/bits/time.h
parse.o: /usr/include/sys/sysmacros.h /usr/include/bits/pthreadtypes.h
parse.o: /usr/include/alloca.h /usr/include/stdio.h /usr/include/libio.h
parse.o: /usr/include/_G_config.h /usr/include/wchar.h
parse.o: /usr/include/bits/stdio_lim.h /usr/include/bits/sys_errlist.h
parse.o: /usr/include/strings.h /usr/include/string.h /usr/include/ctype.h
parse.o: /usr/include/sys/timeb.h /usr/include/sys/times.h memory.h output.h
parse.o: parse.h
inst_pre.o: num2sat.h /usr/include/stdlib.h /usr/include/features.h
inst_pre.o: /usr/include/sys/cdefs.h /usr/include/bits/wordsize.h
inst_pre.o: /usr/include/gnu/stubs.h /usr/include/gnu/stubs-32.h
inst_pre.o: /usr/include/sys/types.h /usr/include/bits/types.h
inst_pre.o: /usr/include/bits/typesizes.h /usr/include/time.h
inst_pre.o: /usr/include/endian.h /usr/include/bits/endian.h
inst_pre.o: /usr/include/sys/select.h /usr/include/bits/select.h
inst_pre.o: /usr/include/bits/sigset.h /usr/include/bits/time.h
inst_pre.o: /usr/include/sys/sysmacros.h /usr/include/bits/pthreadtypes.h
inst_pre.o: /usr/include/alloca.h /usr/include/stdio.h /usr/include/libio.h
inst_pre.o: /usr/include/_G_config.h /usr/include/wchar.h
inst_pre.o: /usr/include/bits/stdio_lim.h /usr/include/bits/sys_errlist.h
inst_pre.o: /usr/include/strings.h /usr/include/string.h /usr/include/ctype.h
inst_pre.o: /usr/include/sys/timeb.h /usr/include/sys/times.h output.h
inst_pre.o: memory.h inst_pre.h
inst_easy.o: num2sat.h /usr/include/stdlib.h /usr/include/features.h
inst_easy.o: /usr/include/sys/cdefs.h /usr/include/bits/wordsize.h
inst_easy.o: /usr/include/gnu/stubs.h /usr/include/gnu/stubs-32.h
inst_easy.o: /usr/include/sys/types.h /usr/include/bits/types.h
inst_easy.o: /usr/include/bits/typesizes.h /usr/include/time.h
inst_easy.o: /usr/include/endian.h /usr/include/bits/endian.h
inst_easy.o: /usr/include/sys/select.h /usr/include/bits/select.h
inst_easy.o: /usr/include/bits/sigset.h /usr/include/bits/time.h
inst_easy.o: /usr/include/sys/sysmacros.h /usr/include/bits/pthreadtypes.h
inst_easy.o: /usr/include/alloca.h /usr/include/stdio.h /usr/include/libio.h
inst_easy.o: /usr/include/_G_config.h /usr/include/wchar.h
inst_easy.o: /usr/include/bits/stdio_lim.h /usr/include/bits/sys_errlist.h
inst_easy.o: /usr/include/strings.h /usr/include/string.h
inst_easy.o: /usr/include/ctype.h /usr/include/sys/timeb.h
inst_easy.o: /usr/include/sys/times.h output.h memory.h inst_pre.h
inst_easy.o: inst_easy.h
inst_hard.o: num2sat.h /usr/include/stdlib.h /usr/include/features.h
inst_hard.o: /usr/include/sys/cdefs.h /usr/include/bits/wordsize.h
inst_hard.o: /usr/include/gnu/stubs.h /usr/include/gnu/stubs-32.h
inst_hard.o: /usr/include/sys/types.h /usr/include/bits/types.h
inst_hard.o: /usr/include/bits/typesizes.h /usr/include/time.h
inst_hard.o: /usr/include/endian.h /usr/include/bits/endian.h
inst_hard.o: /usr/include/sys/select.h /usr/include/bits/select.h
inst_hard.o: /usr/include/bits/sigset.h /usr/include/bits/time.h
inst_hard.o: /usr/include/sys/sysmacros.h /usr/include/bits/pthreadtypes.h
inst_hard.o: /usr/include/alloca.h /usr/include/stdio.h /usr/include/libio.h
inst_hard.o: /usr/include/_G_config.h /usr/include/wchar.h
inst_hard.o: /usr/include/bits/stdio_lim.h /usr/include/bits/sys_errlist.h
inst_hard.o: /usr/include/strings.h /usr/include/string.h
inst_hard.o: /usr/include/ctype.h /usr/include/sys/timeb.h
inst_hard.o: /usr/include/sys/times.h output.h memory.h inst_pre.h
inst_hard.o: inst_hard.h
inst_final.o: num2sat.h /usr/include/stdlib.h /usr/include/features.h
inst_final.o: /usr/include/sys/cdefs.h /usr/include/bits/wordsize.h
inst_final.o: /usr/include/gnu/stubs.h /usr/include/gnu/stubs-32.h
inst_final.o: /usr/include/sys/types.h /usr/include/bits/types.h
inst_final.o: /usr/include/bits/typesizes.h /usr/include/time.h
inst_final.o: /usr/include/endian.h /usr/include/bits/endian.h
inst_final.o: /usr/include/sys/select.h /usr/include/bits/select.h
inst_final.o: /usr/include/bits/sigset.h /usr/include/bits/time.h
inst_final.o: /usr/include/sys/sysmacros.h /usr/include/bits/pthreadtypes.h
inst_final.o: /usr/include/alloca.h /usr/include/stdio.h /usr/include/libio.h
inst_final.o: /usr/include/_G_config.h /usr/include/wchar.h
inst_final.o: /usr/include/bits/stdio_lim.h /usr/include/bits/sys_errlist.h
inst_final.o: /usr/include/strings.h /usr/include/string.h
inst_final.o: /usr/include/ctype.h /usr/include/sys/timeb.h
inst_final.o: /usr/include/sys/times.h output.h memory.h inst_pre.h
inst_final.o: inst_final.h
RPG.o: num2sat.h /usr/include/stdlib.h /usr/include/features.h
RPG.o: /usr/include/sys/cdefs.h /usr/include/bits/wordsize.h
RPG.o: /usr/include/gnu/stubs.h /usr/include/gnu/stubs-32.h
RPG.o: /usr/include/sys/types.h /usr/include/bits/types.h
RPG.o: /usr/include/bits/typesizes.h /usr/include/time.h
RPG.o: /usr/include/endian.h /usr/include/bits/endian.h
RPG.o: /usr/include/sys/select.h /usr/include/bits/select.h
RPG.o: /usr/include/bits/sigset.h /usr/include/bits/time.h
RPG.o: /usr/include/sys/sysmacros.h /usr/include/bits/pthreadtypes.h
RPG.o: /usr/include/alloca.h /usr/include/stdio.h /usr/include/libio.h
RPG.o: /usr/include/_G_config.h /usr/include/wchar.h
RPG.o: /usr/include/bits/stdio_lim.h /usr/include/bits/sys_errlist.h
RPG.o: /usr/include/strings.h /usr/include/string.h /usr/include/ctype.h
RPG.o: /usr/include/sys/timeb.h /usr/include/sys/times.h output.h memory.h
RPG.o: inst_pre.h RPG.h RPGvaluetuples.h
RPGvaluetuples.o: num2sat.h /usr/include/stdlib.h /usr/include/features.h
RPGvaluetuples.o: /usr/include/sys/cdefs.h /usr/include/bits/wordsize.h
RPGvaluetuples.o: /usr/include/gnu/stubs.h /usr/include/gnu/stubs-32.h
RPGvaluetuples.o: /usr/include/sys/types.h /usr/include/bits/types.h
RPGvaluetuples.o: /usr/include/bits/typesizes.h /usr/include/time.h
RPGvaluetuples.o: /usr/include/endian.h /usr/include/bits/endian.h
RPGvaluetuples.o: /usr/include/sys/select.h /usr/include/bits/select.h
RPGvaluetuples.o: /usr/include/bits/sigset.h /usr/include/bits/time.h
RPGvaluetuples.o: /usr/include/sys/sysmacros.h
RPGvaluetuples.o: /usr/include/bits/pthreadtypes.h /usr/include/alloca.h
RPGvaluetuples.o: /usr/include/stdio.h /usr/include/libio.h
RPGvaluetuples.o: /usr/include/_G_config.h /usr/include/wchar.h
RPGvaluetuples.o: /usr/include/bits/stdio_lim.h
RPGvaluetuples.o: /usr/include/bits/sys_errlist.h /usr/include/strings.h
RPGvaluetuples.o: /usr/include/string.h /usr/include/ctype.h
RPGvaluetuples.o: /usr/include/sys/timeb.h /usr/include/sys/times.h output.h
RPGvaluetuples.o: memory.h inst_pre.h RPG.h RPGvaluetuples.h
CNF.o: num2sat.h /usr/include/stdlib.h /usr/include/features.h
CNF.o: /usr/include/sys/cdefs.h /usr/include/bits/wordsize.h
CNF.o: /usr/include/gnu/stubs.h /usr/include/gnu/stubs-32.h
CNF.o: /usr/include/sys/types.h /usr/include/bits/types.h
CNF.o: /usr/include/bits/typesizes.h /usr/include/time.h
CNF.o: /usr/include/endian.h /usr/include/bits/endian.h
CNF.o: /usr/include/sys/select.h /usr/include/bits/select.h
CNF.o: /usr/include/bits/sigset.h /usr/include/bits/time.h
CNF.o: /usr/include/sys/sysmacros.h /usr/include/bits/pthreadtypes.h
CNF.o: /usr/include/alloca.h /usr/include/stdio.h /usr/include/libio.h
CNF.o: /usr/include/_G_config.h /usr/include/wchar.h
CNF.o: /usr/include/bits/stdio_lim.h /usr/include/bits/sys_errlist.h
CNF.o: /usr/include/strings.h /usr/include/string.h /usr/include/ctype.h
CNF.o: /usr/include/sys/timeb.h /usr/include/sys/times.h output.h memory.h
CNF.o: inst_pre.h RPG.h RPGvaluetuples.h CNF.h
HCNF.o: num2sat.h /usr/include/stdlib.h /usr/include/features.h
HCNF.o: /usr/include/sys/cdefs.h /usr/include/bits/wordsize.h
HCNF.o: /usr/include/gnu/stubs.h /usr/include/gnu/stubs-32.h
HCNF.o: /usr/include/sys/types.h /usr/include/bits/types.h
HCNF.o: /usr/include/bits/typesizes.h /usr/include/time.h
HCNF.o: /usr/include/endian.h /usr/include/bits/endian.h
HCNF.o: /usr/include/sys/select.h /usr/include/bits/select.h
HCNF.o: /usr/include/bits/sigset.h /usr/include/bits/time.h
HCNF.o: /usr/include/sys/sysmacros.h /usr/include/bits/pthreadtypes.h
HCNF.o: /usr/include/alloca.h /usr/include/stdio.h /usr/include/libio.h
HCNF.o: /usr/include/_G_config.h /usr/include/wchar.h
HCNF.o: /usr/include/bits/stdio_lim.h /usr/include/bits/sys_errlist.h
HCNF.o: /usr/include/strings.h /usr/include/string.h /usr/include/ctype.h
HCNF.o: /usr/include/sys/timeb.h /usr/include/sys/times.h output.h memory.h
HCNF.o: inst_pre.h RPG.h RPGvaluetuples.h HCNF.h
scan-fct_pddl.tab.o: /usr/include/stdio.h /usr/include/features.h
scan-fct_pddl.tab.o: /usr/include/sys/cdefs.h /usr/include/bits/wordsize.h
scan-fct_pddl.tab.o: /usr/include/gnu/stubs.h /usr/include/gnu/stubs-32.h
scan-fct_pddl.tab.o: /usr/include/bits/types.h /usr/include/bits/typesizes.h
scan-fct_pddl.tab.o: /usr/include/libio.h /usr/include/_G_config.h
scan-fct_pddl.tab.o: /usr/include/wchar.h /usr/include/bits/stdio_lim.h
scan-fct_pddl.tab.o: /usr/include/bits/sys_errlist.h /usr/include/string.h
scan-fct_pddl.tab.o: num2sat.h /usr/include/stdlib.h /usr/include/sys/types.h
scan-fct_pddl.tab.o: /usr/include/time.h /usr/include/endian.h
scan-fct_pddl.tab.o: /usr/include/bits/endian.h /usr/include/sys/select.h
scan-fct_pddl.tab.o: /usr/include/bits/select.h /usr/include/bits/sigset.h
scan-fct_pddl.tab.o: /usr/include/bits/time.h /usr/include/sys/sysmacros.h
scan-fct_pddl.tab.o: /usr/include/bits/pthreadtypes.h /usr/include/alloca.h
scan-fct_pddl.tab.o: /usr/include/strings.h /usr/include/ctype.h
scan-fct_pddl.tab.o: /usr/include/sys/timeb.h /usr/include/sys/times.h
scan-fct_pddl.tab.o: memory.h parse.h lex.fct_pddl.c /usr/include/errno.h
scan-fct_pddl.tab.o: /usr/include/bits/errno.h /usr/include/linux/errno.h
scan-fct_pddl.tab.o: /usr/include/asm/errno.h
scan-fct_pddl.tab.o: /usr/include/asm-generic/errno.h
scan-fct_pddl.tab.o: /usr/include/asm-generic/errno-base.h
scan-fct_pddl.tab.o: /usr/include/unistd.h /usr/include/bits/posix_opt.h
scan-fct_pddl.tab.o: /usr/include/bits/confname.h /usr/include/getopt.h
scan-ops_pddl.tab.o: /usr/include/stdio.h /usr/include/features.h
scan-ops_pddl.tab.o: /usr/include/sys/cdefs.h /usr/include/bits/wordsize.h
scan-ops_pddl.tab.o: /usr/include/gnu/stubs.h /usr/include/gnu/stubs-32.h
scan-ops_pddl.tab.o: /usr/include/bits/types.h /usr/include/bits/typesizes.h
scan-ops_pddl.tab.o: /usr/include/libio.h /usr/include/_G_config.h
scan-ops_pddl.tab.o: /usr/include/wchar.h /usr/include/bits/stdio_lim.h
scan-ops_pddl.tab.o: /usr/include/bits/sys_errlist.h /usr/include/string.h
scan-ops_pddl.tab.o: num2sat.h /usr/include/stdlib.h /usr/include/sys/types.h
scan-ops_pddl.tab.o: /usr/include/time.h /usr/include/endian.h
scan-ops_pddl.tab.o: /usr/include/bits/endian.h /usr/include/sys/select.h
scan-ops_pddl.tab.o: /usr/include/bits/select.h /usr/include/bits/sigset.h
scan-ops_pddl.tab.o: /usr/include/bits/time.h /usr/include/sys/sysmacros.h
scan-ops_pddl.tab.o: /usr/include/bits/pthreadtypes.h /usr/include/alloca.h
scan-ops_pddl.tab.o: /usr/include/strings.h /usr/include/ctype.h
scan-ops_pddl.tab.o: /usr/include/sys/timeb.h /usr/include/sys/times.h
scan-ops_pddl.tab.o: memory.h parse.h lex.ops_pddl.c /usr/include/errno.h
scan-ops_pddl.tab.o: /usr/include/bits/errno.h /usr/include/linux/errno.h
scan-ops_pddl.tab.o: /usr/include/asm/errno.h
scan-ops_pddl.tab.o: /usr/include/asm-generic/errno.h
scan-ops_pddl.tab.o: /usr/include/asm-generic/errno-base.h
scan-ops_pddl.tab.o: /usr/include/unistd.h /usr/include/bits/posix_opt.h
scan-ops_pddl.tab.o: /usr/include/bits/confname.h /usr/include/getopt.h
lex.fct_pddl.o: /usr/include/stdio.h /usr/include/features.h
lex.fct_pddl.o: /usr/include/sys/cdefs.h /usr/include/bits/wordsize.h
lex.fct_pddl.o: /usr/include/gnu/stubs.h /usr/include/gnu/stubs-32.h
lex.fct_pddl.o: /usr/include/bits/types.h /usr/include/bits/typesizes.h
lex.fct_pddl.o: /usr/include/libio.h /usr/include/_G_config.h
lex.fct_pddl.o: /usr/include/wchar.h /usr/include/bits/stdio_lim.h
lex.fct_pddl.o: /usr/include/bits/sys_errlist.h /usr/include/string.h
lex.fct_pddl.o: /usr/include/errno.h /usr/include/bits/errno.h
lex.fct_pddl.o: /usr/include/linux/errno.h /usr/include/asm/errno.h
lex.fct_pddl.o: /usr/include/asm-generic/errno.h
lex.fct_pddl.o: /usr/include/asm-generic/errno-base.h /usr/include/stdlib.h
lex.fct_pddl.o: /usr/include/sys/types.h /usr/include/time.h
lex.fct_pddl.o: /usr/include/endian.h /usr/include/bits/endian.h
lex.fct_pddl.o: /usr/include/sys/select.h /usr/include/bits/select.h
lex.fct_pddl.o: /usr/include/bits/sigset.h /usr/include/bits/time.h
lex.fct_pddl.o: /usr/include/sys/sysmacros.h /usr/include/bits/pthreadtypes.h
lex.fct_pddl.o: /usr/include/alloca.h num2sat.h /usr/include/strings.h
lex.fct_pddl.o: /usr/include/ctype.h /usr/include/sys/timeb.h
lex.fct_pddl.o: /usr/include/sys/times.h parse.h /usr/include/unistd.h
lex.fct_pddl.o: /usr/include/bits/posix_opt.h /usr/include/bits/confname.h
lex.fct_pddl.o: /usr/include/getopt.h
lex.ops_pddl.o: /usr/include/stdio.h /usr/include/features.h
lex.ops_pddl.o: /usr/include/sys/cdefs.h /usr/include/bits/wordsize.h
lex.ops_pddl.o: /usr/include/gnu/stubs.h /usr/include/gnu/stubs-32.h
lex.ops_pddl.o: /usr/include/bits/types.h /usr/include/bits/typesizes.h
lex.ops_pddl.o: /usr/include/libio.h /usr/include/_G_config.h
lex.ops_pddl.o: /usr/include/wchar.h /usr/include/bits/stdio_lim.h
lex.ops_pddl.o: /usr/include/bits/sys_errlist.h /usr/include/string.h
lex.ops_pddl.o: /usr/include/errno.h /usr/include/bits/errno.h
lex.ops_pddl.o: /usr/include/linux/errno.h /usr/include/asm/errno.h
lex.ops_pddl.o: /usr/include/asm-generic/errno.h
lex.ops_pddl.o: /usr/include/asm-generic/errno-base.h /usr/include/stdlib.h
lex.ops_pddl.o: /usr/include/sys/types.h /usr/include/time.h
lex.ops_pddl.o: /usr/include/endian.h /usr/include/bits/endian.h
lex.ops_pddl.o: /usr/include/sys/select.h /usr/include/bits/select.h
lex.ops_pddl.o: /usr/include/bits/sigset.h /usr/include/bits/time.h
lex.ops_pddl.o: /usr/include/sys/sysmacros.h /usr/include/bits/pthreadtypes.h
lex.ops_pddl.o: /usr/include/alloca.h num2sat.h /usr/include/strings.h
lex.ops_pddl.o: /usr/include/ctype.h /usr/include/sys/timeb.h
lex.ops_pddl.o: /usr/include/sys/times.h parse.h /usr/include/unistd.h
lex.ops_pddl.o: /usr/include/bits/posix_opt.h /usr/include/bits/confname.h
lex.ops_pddl.o: /usr/include/getopt.h
