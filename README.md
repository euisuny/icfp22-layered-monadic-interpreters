# Formal Reasoning about Layered Monadic Interpreters Artifact

This is the artifact for the paper submission of "Formal Reasoning About Layered Monadic Interpreters".
We have mechanized and proved all claims made in the paper in Coq.

This development is also available via a virtual machine. (Downloadable in Zenodo)

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

The project can be built by running `make` in this directory.
```
  cd src; make coq
```
In order to build the case study, run `make` in each of the subdirectories, 

### Coq Documentation

The coq documentation (which includes the correspondence between statements in the paper and the source code) can be found in `html/index.html`.
