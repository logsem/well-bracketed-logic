Artifact for the paper: The Logical Essence of Well-Bracketed Control Flow
-------------------
## Webpage

[Paper's webpage](https://logsem.github.io/well-bracketed-logic)

## Compiling the development

To compile this project use `make`.
After compiling the project, use the command `make html` to produce the browsable version of the Coq development.
A summary of the development with links into the aforementioned browsable Coq code is included in the `index.html` file.
In addition, the browsable version of the development is also available on project's webpage linked above.

## Prerequisites

The following is a list of the necessary prerequisites produced by opam.
We recommend using opam for installing these prerequisites.
An easy way to install all these prerequisites using opam is to use the command `opam install . --deps-only` --- do note that one needs to have added Coq and Iris Opam repositories first as explained in [https://gitlab.mpi-sws.org/iris/iris/](https://gitlab.mpi-sws.org/iris/iris/).
Instructions for installing Iris (coq-iris, coq-iris-heap-lang, and coq-stdpp) are available on [https://gitlab.mpi-sws.org/iris/iris/](https://gitlab.mpi-sws.org/iris/iris/).
The coq-autosubst package necessary for our development is also available on iris's opam repository available on the link above.
Note that in the version number of iris packages (e.g., dev.2023-10-03.0.70b30af7) the last part, after the last dot, is the hash of the exact commit of iris that is installed.
This might be useful should you want to install Iris by compiling the source code yourself.

```
coq                   8.18.0                    The Coq Proof Assistant
coq-autosubst         dev                       Coq library for parallel de Bruijn substitutions
coq-core              8.18.0                    The Coq Proof Assistant -- Core Binaries and Tools
coq-iris              dev.2023-10-03.0.70b30af7 A Higher-Order Concurrent Separation Logic Framework with support for interactive proofs
coq-iris-heap-lang    dev.2023-10-03.0.70b30af7 The canonical example language for Iris
coq-stdlib            8.18.0                    The Coq Proof Assistant -- Standard Library
coq-stdpp             dev.2023-10-03.0.83c8fcbf An extended "Standard Library" for Coq
ocaml                 5.1.0                     The OCaml compiler (virtual package)
ocaml-base-compiler   5.1.0                     Official release 5.1.0
```

## Overview of he Coq development
The (interesting) files in this development are organized as follows:

```
.
├── Makefile ····························· The make file.
├── README.md ···························· This readme file.
├── _CoqProject ·························· The Coq project file.
└── theories ····························· The Coq source files.
    ├── F_mu_ref ························· Unary and binary logical relations models for F_mu_ref.
    │   ├── base.v ······················· Some basic definitions and tactics.
    │   ├── binary ······················· The binary logical relations model.
    │   │   ├── context_refinement.v ····· The definition of contextual refinement and some lemmas.
    │   │   ├── examples ················· Examples of using our binary logical relations model.
    │   │   │   ├── fact.v ··············· Equivalence of two factorial implementations.
    │   │   │   └── very_awkward.v ······· The contextual equivalence of VAE.
    │   │   ├── fundamental.v ············ The fundamental theorem of binary logical relations.
    │   │   ├── logrel.v ················· The definition of binary logical relations.
    │   │   ├── rules.v ·················· Rules for resources for tracking the specification-side program.
    │   │   └── soundness.v ·············· Soundness theorem of binary logical relations.
    │   ├── lang.v ······················· The definition (syntax & op sem) of F_mu_ref.
    │   ├── typing.v ····················· The typing rules of F_mu_ref.
    │   ├── unary ························ The unary logical relations model.
    │   │   ├── examples ················· Examples of using our unary logical relations model.
    │   │   │   └── very_awkward.v ······· The VAE example using the unary logical relations.
    │   │   ├── fundamental.v ············ The fundamental theorem of the unary logical relations model.
    │   │   ├── logrel.v ················· The definition of the unary logical relations.
    │   │   └── soundness.v ·············· Soundness of the unary logical relations model.
    │   └── wp_rules.v ··················· The (well-bracketed) weakest precondition rules for F_mu_ref.
    ├── heap_lang ························ A copy of heap lang from the Iris development.
    │   ├── adequacy.v ··················· The adequacy theorem.
    │   ├── derived_laws.v ··············· Derived rules for well-bracketed weakest preconditions.
    │   ├── primitive_laws.v ············· Primitive rules for weakest preconditions.
    │   └── proofmode.v ·················· Lemmas and tactics for proofmode support for heap_lang programs.
    ├── heap_lang_examples ··············· Examples on top of heap lang.
    │   ├── awkward.v ···················· The awkward example.
    │   ├── sts ·························· Examples using the STS encoding.
    │   │   └── very_awkward.v ··········· The STS version of VAE.
    │   └── very_awkward.v ··············· VAE proven well-bracketed in heap lang.
    ├── heap_lang_trace ·················· The version of heap lang with intensional traces.
    │   ├── README.txt ··················· Attribution of the development in this sub-folder.
    │   ├── adequacy.v ··················· The adequacy theorem.
    │   ├── class_instances.v ············ Type classes for Iris's proof mode.
    │   ├── derived_laws.v ··············· Derived rules for well-bracketed weakest preconditions.
    │   ├── lang.v ······················· Definition of the language heaplang with added trace primitives.
    │   ├── notation.v ··················· Useful notations for writing programs.
    │   ├── primitive_laws.v ············· Primitive rules for weakest preconditions.
    │   ├── proofmode.v ·················· Lemmas and tactics for proofmode support for heap_lang programs.
    │   ├── tactics.v ···················· Supporting tactics for defining proofmode tactics.
    │   └── trace_resources.v ············ Iris resources for reasoning about program traces.
    ├── heap_lang_trace_examples ········· Examples using intensional trace properties in heap lang.
    │   ├── sequential_trace_alt.v ······· The definition of well-bracketed trace of calls and returns.
    │   └── very_awkward.v ··············· The VAE example proven to produce well-bracketed traces.
    ├── oneshot.v ························ The definition of the one-shot resource algebra
    ├── persistent_pred.v ················ Definition of persistent predicates used in logical relations.
    └── program_logic ···················· The well-bracketed program logic.
        ├── adequacy.v ··················· The adequacy theorem of the well-bracketed program logic.
        ├── ghost_stacks.v ··············· The theory of ghost stacks including resource algebras.
        ├── lib ·························· Developments on top of the well-bracketed program logic.
        │   └── sts.v ···················· The encoding of STSs using ghost stacks.
        ├── lifting.v ···················· A couple of useful lemmas.
        └── weakestpre.v ················· Definition of well-bracketed weakest preconditions.
```
