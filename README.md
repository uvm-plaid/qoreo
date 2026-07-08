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

Qoreo can project example choreographies to per-party processes and render those processes as Python applications that use the NetQASM SDK.

## Dependencies

First install the Rocq dependencies described in the `Install` section above and make sure `rocq`, `ocamlc`, `make`, and `python` are available on your `PATH`. We have tested using Python 3.10. The extraction targets use Rocq extraction to produce OCaml code, compile that OCaml code with `ocamlc`, and then write Python applications.

The generated applications import the NetQASM SDK. Running the included simulation also requires SquidASM:

```
python -m pip install netqasm
python -m pip install squidasm --extra-index-url=https://pypi.netsquid.org
```

SquidASM depends on NetSquid, which requires special credentials to install. You can register and obtain credentials at the [NetSquid website](https://netsquid.org/).

## Extracting the examples

The `examples` directory includes these extractable NetQASM examples:

* `examples/MeasureSend.v` - Alice creates a qubit, applies `H`, measures it, and sends the resulting classical bit to Bob
* `examples/Teleportation.v` - a teleportation choreography
* `examples/b92.v` - a B92 quantum key distribution choreography

To run endpoint projection and generate Python applications for the simple
measurement example:

```
make generate-measure-send-py
```

For teleportation:

```
make generate-teleportation-py
```

For B92:

```
make generate-b92-py
```

Each target builds the corresponding Rocq example, extracts rendered application data into `extracted/`, compiles the OCaml generator, and writes the final Python application directory under `generated/<example>/`. For example, `make generate-b92-py` writes files such as:

```
generated/b92/app_alice.py
generated/b92/app_bob.py
generated/b92/qoreo_netqasm_runtime.py
```

The generated `app_<party>.py` files are the NetQASM SDK applications for each party. `qoreo_netqasm_runtime.py` is copied into the generated directory so the applications can import the Qoreo runtime wrapper directly.

The compilation pipeline relies on:

* `src/NetQasm.v` - Renders a `Process` into a string in a NetQASM-like IR
* `ocaml/write_apps.ml` - An OCaml driver to run the renderer and save the results to .py files
* `python/qoreo_netqasm_runtime.py` - A Python runtime that wraps the NetQASM API to make it more similar to the Qoreo expression language

## Running the simulation

The repository includes a simulation harness for the B92 example. Generate the B92 applications first:

```
make generate-b92-py
```

Then run:

```
python test_examples/test_b92.py
```

The script starts a SquidASM runtime with Alice and Bob, imports the generated applications from `generated/b92`, runs the protocol several times, and checks that Alice's and Bob's conclusive key bits match. It prints the key extracted from each run.

`MeasureSend` and `Teleportation` are generated as NetQASM SDK Python applications in the same way. You can run the simulation for these examples by changing to the directory containing the generated application and running:

```
netqasm simulate
```
