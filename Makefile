
default: CorgiTactics.vo Query.vo Imp.vo

%.vo: %.v
	coqc -I $(CPDT_HOME) $<

clean:
	rm -f ./*.vo
