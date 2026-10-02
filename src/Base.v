(**
  This file defines some common structures used in the formaliztion
        - `FMap_fun`/`FMap` - finite maps
        - `Var` - variables represented as natural numbers
        - `unitary` - data structure of unitary gates
        - `Config` - quantum states represented as QuantumLib density matrices
        - `Actor` - actors in a network, represented as strings
        - `ChorEnv` - specialized finite maps from pairs of actors and variable names.
*)


From Stdlib Require FSets.FMapList FSets.FSetList 
                            FSets.FMapFacts
                            FSets.FMapInterface
                            OrderedType OrderedTypeEx.
From QuantumLib Require Import Matrix Pad Quantum.
From Stdlib Require Import String Morphisms (* for Proper *).
Require Import Setoid. (* for setoid_replace with *)

From Stdlib Require Lists.List.
Export List.ListNotations.
Open Scope list_scope.

Declare Scope qoreo.
Create HintDb var_db.
Create HintDb actor_db.
Create HintDb qoreo_db.




(* This could be instantiated in different ways. *)

