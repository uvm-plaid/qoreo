Qoreo is a choreographic programming language for quantum networks and distributed systems.

# Install

Qoreo is written in Rocq and is tested with Rocq 9.0 and 9.1. It may not be compatible with earlier versions e.g. Coq 8.x.

I recommend installing Rocq via opam: https://rocq-prover.org/docs/using-opam

Qoreo uses the QuantumLib library for formalizing quantum computing (https://github.com/inQWIRE/QuantumLib) but the version compatible with Rocq 9.x is currently in a fork here: https://github.com/jpaykin/QuantumLib/tree/jpaykin/v9.1. You can install it via:

```
opam pin coq-quantumlib https://github.com/jpaykin/QuantumLib.git#jpaykin/v9.1
```

Once dependencies have been installed, you can build the Rocq proofs using `make proofs`. The workflow uses CoqMakefile.


# Structure

The repository is organized in 4 main directories.

* `src` - Rocq implementation of Qoreo
    - `src/Base.v` - Definition of common structures used in the formaliztion
        - `FMap` - finite maps
        - `Var` - variables represented as natural numbers
        - `unitary` - data structure of unitary gates
        - `Config` - quantum states represented as QuantumLib density matrices
        - `Actor` - actors in a network, represented as strings
        - `ChorEnv` - specialized finite maps from pairs of actors and variable names.

    - `src/Expr.v` - Definition of the local quantum expression language
        - `Expr.t` - Qoreo AST
        - `Expr.step` - small-step operational semantics
        - `Expr.typ` - Qoreo types
        - `Expr.WellTyped` - typing relation
        - `wt_subst`, `wt_subst_bang` - substitution lemmas for linear and non-linear variables respectively
        - `WellTyped_preservation` - preservation of the typing relation with respect to the step relation
        - `WellScoped_preservation` - preservation of the configuration well-scopedness relation with respect to the step relation
        - `preservation`- conjunction of the previous two lemmas
        - 'progress' - well-typed terms are either values or can take a step
        - `safety` - top-level type safety theorem

    - `src/Choreography.v` - Definition of the choreographic language
        - `Insn.t`, `Expr.t` - Choreographic instructions and choreographies, respectively
        - `step` - small-step operational semantics
        - `WellTyped` - typing relation
        - `wt_subst_lin`, `wt_subst_bang`: substitution lemmas for linear and non-linear variables respectively
        - `WellTyped_preservation`: preservation of the typing relation with respect to the step relation
        - `WellScoped_preservation`: preservation of the configuration well-scopedness relation with respect to the step relation
        - `preservation`: conjunction of the previous two lemmas
        - 'progress': well-typed choreographies are either values or can take a step
        - `safety`: top-level type safety theorem


    - `src/Network.v`: Definition of process language and endpoint projection
        - `Insn.t`, `Process.t`, `Network.t` - Definiton of choreographic instructions, processes, and networks respectively
        - `Process.step`, `Network.step` - small-step operational semantics
        - `epp` - Definition of endpoint projection as a function from choreographies and an actor name to a process.
        - `EPP` - Relational definition of endpoint projection
        - `EPP_N` - Relational definition of when a choreography is projected onto an entire network
        - `soundness` - Soundness of EPP; if a choreography can take a step, then so can the projected choreography
        - `completeness` - Completeness of EPP; if a projected choreography can take a step, then so can the unprojected choreography
        - `safety` - Well-typed choreographies project to safe and deadlock-free networks

    - `src/NetQasm.v` - Render Qoreo processes as NetQASM strings

* `examples/`

    - `examples/Notation.v` - Introduces a Qoreo construction DSL monad that uses higher-order abstract syntax (HOAS) to construct choreographies in a natural style

    - `examples/MeasureSend.v` - trivial examples that measures a qubit and sends it on a channel
    - `examples/Teleportation.v` - choreographic implementation of quantum teleportation
    - `examples/Protocols.v` - a variety of protocols including distributed controlled-unitaries and a distributed VQA pass
    - `examples/b92.v` - implementaiton of B92 quantum key distribution algorithm

        * `test_examples/test_b92.py` - python instrumentation for B91

* `ocaml/` - A directory that instrments the extracted ocaml code for each examples

* `python/ocaml_netqasm_runtime.py` - Implementation of a simple python runtime library using netqasm.


# Contributing to the repository

To add a new Rocq `.v` file, add it to the `src/` subdirectory and add it to the list of filenames in the `_CoqProject` file.

Qoreo uses the OCaml/Rocq concept of modules to define data structures. The variables in `src/Base.v` are a good example: they are defined in a module `Var`, and the type of such variables is `Var.t`. Other helper functions such as decidable equality of variables are also defined in this module (`Var.eq_dec`). Modules can be nested, e.g. `Var.FSet.t` is the type of finite sets of variables.

# Extracting to NetQASM

The `examples` directory includes:

* `examples/MeasureSend.v` - Alice creates a qubit, applies `H`, measures it, and sends the resulting classical bit to Bob
* `examples/Teleportation.v` - a more involved teleportation choreography

To run endpoint projection on the simple measurement example and compile the resulting processes to Python files using the NetQASM API, run:

```
make generate-measure-send-py
```

For the teleportation example, run:

```
make generate-teleportation-py
```

The results are stored in the `generated` directory. The compilation pipeline relies on:

* `src/NetQasm.v` - Renders a `Process` into a string in a NetQASM-like IR
* `ocaml/write_apps.ml` - An OCaml driver to run the renderer and save the results to .py files
* `python/qoreo_netqasm_runtime.py` - A Python runtime that wraps the NetQASM API to make it more similar to the Qoreo expression language
