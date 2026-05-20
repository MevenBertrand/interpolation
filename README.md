# Interpolation-STLC

This is the formalisation accompanying the paper _Bidirectional Interpolation for the Lambda-Calculus_.

## Installation

### Dependencies

The project builds with Rocq version `9.0`, and depends on the [`smpl`](https://github.com/uds-psl/smpl/), [Equations](https://github.com/mattam82/Coq-Equations/) and [`stdpp`](https://gitlab.mpi-sws.org/iris/stdpp/) libraries.

If you do not have Rocq installed already, instructions are available [on its website](https://rocq-prover.org/install).

If you already have an opam setup, the dependencies can be installed from the rood folder with
```
opam install ./code/ --deps-only
```
In a new switch, you need to have invoked
`
opam repo add rocq-released https://rocq-prover.org/opam/released
`
beforehand.

### Building

Once the dependencies have been installed, you can issue `make` in the `code` folder to
build the whole development.

The project uses the [AutoSubst](https://github.com/uds-psl/autosubst-ocaml) tool to generate syntax-related boilerplate, although it is not necessary to install it to build the project, as we directly include the generated files (slightly modified, see the paper for explanation).

## Overview

The definition of typing is in [Typing](./code/theories/Typing.v), that of reduction is in [Reduction](./code/theories/Reduction.v), and that of conversion is in [Equations](./code/theories/Equations.v). Definitions related to atoms and constants are in [Languages](./code/theories/Languages.v). The confluence axiom is in [ReductionConfluence](./code/theories/ReductionConfluence.v).

The main theorems are in [Theorems](./code/theories/Theorems.v). To avoid having to compare terms in languages with different sets of constants, which would be painful (and require its own notion of substitution, etc), we instead phrase them with respect to a unique global language containing all necessary constants, and show the terms only use the appropriate constants.

## Confluence

We include in the `confluence` subfolder the [CSIho](http://cl-informatik.uibk.ac.at/software/csi/ho/) tool and [file](./confluence/comm_cuts.trs) we used to check confluence. The command to invoke is in the [Makefile](./confluence/Makefile) (depending on the way the folder has been downloaded, it might be necessary to make the relevant files executable, eg by using `chmod`).

In the output the relevant line is the one saying
```
  critical peaks: 12, all joinable
```
The tool does not conclude about confluence per se because it is unable to prove termination, which we have proven separately, in [ReductionConfluence](./code/theories/ReductionConfluence.v).
This also means, that sadly, the [online version](http://colo6-c703.uibk.ac.at/csi/index.php?version=csiho) of CSIho does not report interesting information, hence the local setup.

## File structure

All names refer to files in the `code` folder. A [dependency graph](./code/docs/dependency_graph.png) is provided in the `code/docs` subfolder.

File | Content
-----|--------
Utils | Generic utilities
core, unscoped | Autosubst utilities
BasicAst | Definitions on which that of syntax depends: base types, constants, etc.
Notations | Reserves most notations used in the project, can be used as index of notations!
Context | Definition of context and context access
Ast.sig | Signature of the AST of simply-typed lambda-calculus
Ast.v | Syntax and substitution, auto-generated from the above by Autosubst
Syntax | Notations and helpers to deal with the generated syntax
Elim | Operations on eliminators
Reduction | Definition and properties of reduction
ReductionConfluence | A partial proof of confluence of commuting conversion, and the confluence axiom
Typing | Definition and properties of (undirected) typing
Bidir | Definition of bidirectional typing (characterising normal forms)
Equations | Definition and properties of conversion
Languages | Definition and properties of the atoms/constants of a type, context, term
MetaTheory | Meta-theoretic properties of typing, including normalisation
Interpolation | The main inductive proof
Theorems | “Top-level” theorems, putting together normalisation, interpolation, and properties of conversion