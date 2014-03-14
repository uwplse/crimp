crimp
=====

Certified Relational to Imperative.

The goal of this project is a verified compiler from SQL-like
queries to imperative code.

The core theorem statement is
```coq
Theorem queryEquivalence:
  forall (q : Query) (p : ImpProgram),
    queryToImp q = Some p ->
      forall (r1 r2 r' : relation), runQuery q r1 r2 = Some r' ->
        runImp' p r1 r2 = Some r'.
```
Or "if the compiler accepts the query, and the query produces successful output, then the Imp program will
succeed and produce the same output"

Inspired by verifying transformations in https://github.com/uwescience/datalogcompiler.

### Dependencies
- Coq 8.4+ (tested at 8.4, may work with down to 8.2)
- [Tactics from Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/cpdtlib.tgz)

### Get Coq dependencies
```bash
wget http://adam.chlipala.net/cpdt/cpdtlib.tgz
tar xf cpdtlib.tgz
cd cpdtlib
coqc CpdtTactics
```

### Build Crimp
```bash
export CPDT_HOME=/path/to/cpdtlib
cd crimp
make
```

### Run Crimp proofs
You can run the query equivalence proofs with
```bash
make QueryEquivalence.vo
```

or you can open QueryEquivalence.v in your favorite/un-favorite Coq environment, like [Proof General](http://proofgeneral.inf.ed.ac.uk).
