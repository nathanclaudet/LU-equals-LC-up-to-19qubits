# LU=LC for graph states up to 19 qubits

This code refers to the work "Deciding Local Unitary Equivalence of Graph States in Quasi-Polynomial Time" which is free to access at *arxiv link coming soon*. The theoretical framework explaining this code can be found in the appendix.

This code is the computer-assisted part of a proof that LU-equivalence and LC-equivalence coincide for graph states defined on up to 19 qubits. This was previously known for graph states up to 8 qubits (see [arxiv.org/abs/0812.4625](arxiv.org/abs/0812.4625)).

## Compilation
To compile, write the following command in a linux terminal:
```sh
g++  main.cpp -o main && ./main
```