# Simuliris Coq development
This repository contains the Coq development of Simuliris.

## Setup 
This project is known to build with [Coq 8.13.2](https://coq.inria.fr/).
It depends on recent development versions of [std++](https://gitlab.mpi-sws.org/iris/stdpp) and [Iris](https://gitlab.mpi-sws.org/iris/iris), as well as [coq-equations](https://github.com/mattam82/Coq-Equations).


We recommend using [opam](https://opam.ocaml.org/) (version >= 2.0, tested on 2.0.8) for the installation.

Please execute the following instructions in the folder containing this README, replacing `N` with the number of jobs you'd like to use for compilation.
```
opam switch create simuliris 4.11.1
opam switch link simuliris .
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
make -jN builddep
make -jN

```

