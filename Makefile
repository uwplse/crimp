
default: CorgiTactics.vo

%.vo: %.v
	coqc $<
