
default: Query.vo Imp.vo CrimpTactics.vo 

%.vo: %.v
	coqc -I $(CPDT_HOME) $<

clean:
	rm -f ./*.vo
