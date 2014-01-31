.PHONY: coq html src Makefile.coq clean test

coq: Makefile.coq
	touch .depend
	make -f Makefile.coq depend
	make -f Makefile.coq

html: Makefile.coq
	touch .depend
	make -f Makefile.coq depend
	env COQDOCFLAGS='-parse-comments -interpolate -utf8 --toc-depth 3' make -f Makefile.coq html

src:
	make -C src

test:
	make -C test

Makefile.coq:
	coq_makefile *.v > Makefile.coq

clean: Makefile.coq
	make -f Makefile.coq clean
	rm -f Makefile.coq .depend *.vo *.v.d *.glob
