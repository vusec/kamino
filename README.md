# Kamino

This is a public release of the system described in the paper "On the effectiveness of code normalization for function identification", published in the IEEE PRDC'18 conference.

The repository mainly contains two tools:

- `trivial-equiv`, which implements the minimal normalization and equivalence algorithm described in the paper and
- `kamino`, which implements the advanced normalization and equivalence checking

Building these tools requires a modified version of BAP 0.x, which is published alongside this repository. As this old version of BAP ties us to OCaml 3.12 (which is several years old), building the software is not as straightforward as it could be. It is highly recommended that you use the [Dockerfile](docker/Dockerfile), which also documents the build procedure.

Some of the functionality which is not relevant to the paper has been cropped from this repository.

## Evaluation

The evaluation described in the paper is implemented by the OCaml programs `eval` and `clustering-eval`. The evaluation set will be published separately.

## Authors
Almost all of the OCaml code in this repository has been written by Angelos Oikonomopoulos and Remco Vermeulen while at the Vrije Universiteit Amsterdam. A small number of files are slightly modified versions of the respective modules in BAP.
