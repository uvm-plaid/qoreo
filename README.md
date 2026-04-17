Qoreo is a choreographic programming language for quantum networks and distributed systems.

# Install

Qoreo is written in Rocq and is tested with Rocq 9.0 and 9.1. It may not be compatible with earlier versions e.g. Coq 8.x.

I recommend installing Rocq via opam: https://rocq-prover.org/docs/using-opam

Qoreo uses the QuantumLib library for formalizing quantum computing (https://github.com/inQWIRE/QuantumLib) but the version compatible with Rocq 9.x is currently in a fork here: https://github.com/jpaykin/QuantumLib/tree/jpaykin/v9.1. You can install it via:

```
opam pin coq-quantumlib https://github.com/jpaykin/QuantumLib.git#jpaykin/v9.1
```

Once dependencies have been installed, build the Qoreo repository using `make`. The workflow uses CoqMakefile.

# Structure

To add a new Rocq `.v` file, add it to the `src/` subdirectory and add it to the list of filenames in the `_CoqProject` file.

Qoreo uses the OCaml/Rocq concept of modules to define data structures. The variables in `src/Base.v` are a good example: they are defined in a module `Var`, and the type of such variables is `Var.t`. Other helper functions such as decidable equality of variables are also defined in this module (`Var.eq_dec`). Modules can be nested, e.g. `Var.FSet.t` is the type of finite sets of variables.

* `src/Base.v` - Variables `Var.t`; quantum references `qref` and unitaries; quantum states `Config.t`; and actors `Actor.t`.
* `src/Expr.v` - The definition of the local quantum language language.
* `src/Choreography.v` - The definition of the choreographic language.
* `src/Network.v` - The definition of the network language.

# Compiling to NetQASM

The file `examples/Teleportation.v` contains a simple example choreography. To run endpoint projection on this choreography and compile the resulting processes to Python files using the NetQASM API, run:

```
make generate-teleportation-py
```

The results are stored in the `generated` directory. The compilation pipeline relies on:

* `src/NetQasm.v` - Renders a `Process` into a string in a NetQASM-like IR
* `ocaml/write_apps.ml` - An OCaml driver to run the renderer and save the results to .py files
* `python/qoreo_netqasm_runtime.py` - A Python runtime that wraps the NetQASM API to make it more similar to the Qoreo expression language
