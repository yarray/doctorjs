PREFIX=/usr/local
INSTALL=install
NODE=node

BIN_SRC=$(addprefix bin/,jsctags.js)
LIB_SRC=$(addprefix lib/jsctags/,getopt.js log.js paperboy.js traits.js \
	underscore.js)
LIB_CTAGS_SRC=$(addprefix lib/jsctags/ctags/,index.js interp.js nativefn.js \
	reader.js writer.js)
LIB_CFA2_SRC=$(addprefix lib/cfa2/,index.js jscfa.js)
LIB_NARCISSUS_SRC=$(addprefix narcissus/lib/,../main.js decompiler.js \
	definitions.js desugaring.js jsbrowser.js jsdecomp.js jsdefs.js \
	jsdesugar.js jsexec.js jslex.js jsparse.js jsresolve.js \
	lexer.js parser.js)

install:
	$(INSTALL) -d $(PREFIX)/bin
	$(INSTALL) $(BIN_SRC) $(BIN_SRC:%.js=$(PREFIX)/%)
	$(INSTALL) -d $(PREFIX)/lib/jsctags
	$(INSTALL) $(LIB_SRC) $(PREFIX)/lib/jsctags
	$(INSTALL) -d $(PREFIX)/lib/jsctags/ctags
	$(INSTALL) $(LIB_CTAGS_SRC) $(PREFIX)/lib/jsctags/ctags
	$(INSTALL) -d $(PREFIX)/lib/cfa2
	$(INSTALL) $(LIB_CFA2_SRC) $(PREFIX)/lib/cfa2
	$(INSTALL) -d $(PREFIX)/narcissus
	$(INSTALL) -d $(PREFIX)/narcissus/lib
	$(INSTALL) $(LIB_NARCISSUS_SRC) $(PREFIX)/narcissus/lib

uninstall:
	rm -rf $(BIN_SRC:%.js=$(PREFIX)/%) $(PREFIX)/lib/jsctags \
	  $(PREFIX)/lib/cfa2 $(PREFIX)/narcissus

serve:
	$(NODE) serve.js

tags:
	$(NODE) bin/jsctags.js -Llib/jsctags js lib/jsctags

.PHONY:	all install uninstall serve tags

