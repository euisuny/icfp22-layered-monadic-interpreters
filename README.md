# Formal Reasoning about Layered Monadic Interpreters Artifact

This is the artifact for the paper submission of "Formal Reasoning About Layered Monadic Interpreters".
We have mechanized and proved all claims made in the paper in Coq.

This development is also available via a virtual machine. (Downloadable in Zenodo)

### Documentation

The documentation for this library is available [here](http://euisuny.github.io/icfp22-layered-monadic-interpreters/), which includes the correspondence between statements in the paper and the source code.

### Dependencies

The following are necessary dependencies for the code base.

- coq 8.15
- coq-paco 4.1.2

These packages can be installed via `opam`.

```
 opam switch create 4.12.0
 opam repo add coq-released https://coq.inria.fr/opam/released
 opam pin coq 8.15.0
 opam install coq-paco
```

### Compilation Instructions

#### Building the Metatheory
The project can be built by running `make` in this directory.
```
  cd src; make
```
In order to build the case study, run `make` in each of the subdirectories, 

#### Building the case study
The case study can be built by running `make` in the respective directories.
```
  cd tutorial; make
```
or
```
  cd tutorial_commute; make
```
