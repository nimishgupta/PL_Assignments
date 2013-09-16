SOURCES=$(wildcard *.ml)
OBJECTS=$(SOURCES:.ml=.d)

.PHONY = all clean


all: .done

.done: $(OBJECTS)
	touch .done

%.d:%.ml
	cs691f compile $* && cs691f test $* && touch $*.d

clean:
	rm -f .done *.d || true
