(**
  Definition of the local quantum expression language

  Theorems:

  - `wt_subst`, `wt_subst_bang`: substitution lemmas for linear and non-linear variables respectively
  - `WellTyped_preservation`: preservation of the typing relation with respect to the step relation
  - `WellScoped_preservation`: preservation of the configuration well-scopedness relation with respect to the step relation
  - `preservation`: conjunction of the previous two lemmas
  - 'progress': well-typed terms are either values or can take a step
  - `safety`: top-level type safety theorem

  *)


From Stdlib Require Import FSets.FMapList FSets.FSetList FSets.FMapFacts OrderedType OrderedTypeEx.
From QuantumLib Require Import Matrix Pad Quantum.
From Qoreo Require Import Base Expr.
Import Var.Map.Tactics.


Open Scope qoreo.


(** * Well-typedness *)



(* ** Type safety *)
