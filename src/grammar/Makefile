lsimplify:	lsimplify.gra gt/gt Makefile
		gt/gt < lsimplify.gra
		$(MAKE) -f most_recent_emitted_Makefile

gt/gt:	gt/Makefile
	cd gt; $(MAKE)

push:	
	cp -v lsimplify_eq.ml lsimplify_lex.ml* lsimplify_parse.ml* lsimplify_pp.ml lsimplify_syntax.ml lsimplify_util.ml ..
	cp -v lsimplify ../../bin

emitted:
	$(MAKE) -f most_recent_emitted_Makefile

clean:	
	rm -f lsimplify lsimplify_* most_recent_emitted_Makefile
	cd gt; make clean
