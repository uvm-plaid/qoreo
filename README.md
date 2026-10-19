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

The repository contains the Rocq formalization, extraction/generation tools, Python runtimes, and example simulations:

```text
.
├── src/
│   ├── Base/             # Shared structures: variables, actors, configs, maps
│   ├── Expr/             # Local quantum expression language and metatheory
│   ├── Choreography/     # Choreographies, semantics, proofs, and notation
│   ├── Network/          # Process/network semantics and endpoint projection
│   ├── Examples/         # Example choreographies
│   ├── NetQasm.v         # Rendering projected processes as Python applications
├── ocaml/                # Drivers that write generated party applications
├── python/               # NetQASM and NetSquid runtime implementations
├── test_examples/        # B92, DQFT, and unitary simulation tests
├── Makefile              # Proof and example-generation targets
└── _CoqProject           # Rocq logical paths and source-file list
```

The main Rocq components are:

* `src/Base/` defines common data types and finite maps, including `Var`, `Actor`, `Config`, and `ChorEnv`.
* `src/Expr/` defines the local quantum expression language, its typing and operational semantics, and related metatheory.
* `src/Choreography/` defines choreographic programs and proves their typing, operational, and safety properties.
* `src/Network/` defines projected processes and networks, endpoint projection, and its correctness properties.
* `src/Examples/` contains B92, measurement/send, teleportation, protocols, distributed QFT, and unitary-gate examples.
* `src/NetQasm.v` renders projected processes as Python source.

The code-generation pipeline uses the shared driver in `ocaml/generate_apps.ml`, the writer in `ocaml/write_apps.ml`, and the runtime modules in `python/`.


# Contributing to the repository

To add a new Rocq `.v` file, place it in the appropriate `src/` subdirectory and add it to `_CoqProject`. Qoreo uses Rocq modules to organize data structures; for example, variables and their operations are defined under `Var` in `src/Base/Var.v`.

## Adding an example

For a new example named `my_example`:

1. Add `src/Examples/MyExample.v` and list it in `_CoqProject`. Use the existing files in `src/Examples/` as a guide for defining the choreography and its parties. Keep Coq source filenames in CamelCase; the extraction and Make target stem can remain `my_example`.
2. If the example should generate Python applications, define an `apps` value using the appropriate renderer. Export it at the top level of the Coq file, then add Rocq extraction at the end:

   ```rocq
   End MyExample.
   Definition example_apps := MyExample.apps.

   Extraction Language OCaml.
   Set Extraction Output Directory "extracted".
   Extraction "MyExample.ml" example_apps.
   ```

   `MyExample.apps` above is the value defined inside the example module; the top-level `example_apps` alias is the common extraction interface. The extraction filename must match the example file stem, including its capitalization.
3. Add `MyExample` to `PYTHON_GENERATION_EXAMPLES` in the `Makefile`. The shared pattern rule infers `src/Examples/MyExample.vo`, uses `ocaml/generate_apps.ml`, and provides `make MyExample`, writing output to `generated/MyExample/`.
4. Verify the example with `make MyExample` (or build all generated examples with `make examples`). If it needs a simulation or behavior test, add one under `test_examples/`.

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

The `src/Examples/` directory contains the extractable examples:

* `MeasureSend.v` - Alice creates a qubit, applies `H`, measures it, and sends the resulting classical bit to Bob
* `Teleportation.v` - a teleportation choreography
* `B92.v` - a B92 quantum key distribution choreography
* `DQFT.v` - a distributed quantum Fourier transform example
* `UnitaryTest.v` - a unitary-gate example
* `ConditionalTest.v` - a conditional choreography example
* `DistributedGrover.v` - a distributed Grover search example

Generate applications with the corresponding Make targets:

```
make MeasureSend
make Teleportation
make B92
make DQFT
make UnitaryTest
make ConditionalTest
make DistributedGrover
```

Each target builds the corresponding Rocq example, extracts rendered application data into `extracted/`, compiles the OCaml generator, and writes party applications under `generated/<Example>/`. The generator also copies the Python runtime modules into that output directory.

The compilation pipeline uses:

* `src/NetQasm.v` - Renders a `Process` into a string in a NetQASM-like IR
* `ocaml/write_apps.ml` - An OCaml driver to run the renderer and save the results to .py files
* `python/qoreo_netqasm_runtime.py` and `python/qoreo_netsquid_runtime.py` - Python runtimes for the generated applications and NetSquid simulations

## Running the examples

The `test_examples/` directory contains simulation tests. B92 uses SquidASM; DQFT and unitary use the Qoreo NetSquid runtime. Generate the applications first:

```
make B92
make DQFT
make UnitaryTest
```

Run the B92 test with the Python environment containing NetSquid and SquidASM dependencies:

```
python test_examples/test_b92.py
```

The B92 test starts Alice and Bob through SquidASM, runs several protocol rounds, and checks that their conclusive key bits match. The DQFT and unitary tests execute the generated party programs against the Qoreo NetSquid runtime.

`MeasureSend` and `Teleportation` generate NetQASM SDK Python applications. Their generated applications can be run with the NetQASM tooling.
