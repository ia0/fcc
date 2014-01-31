.PHONY: all clean

SOURCES=$(wildcard *.lc)
OBJECTS=$(patsubst %.lc,%.lo,$(SOURCES))

all: $(OBJECTS)

%.v: %.lc
	./v.zsh < $*.lc > $*.v

%.w: %.v
	coqc -q -I .. $*.v > $*.w ; rm -f $*.glob $*.vo

%.lo %.lh: %.w
	../src/c2l.native $*.lo $*.lh < $*.w || (cat $*.w ; false)

%: %.lo %.lh
	cat $*.lo
	cat $*.lh

clean:
	rm -f *.w *.v *.lo *.lh *.vo *.glob
