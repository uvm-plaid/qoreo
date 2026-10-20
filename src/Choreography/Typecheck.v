(* Algorithmic type checking *) 

From Stdlib Require Export FSets.FMapList FSets.FSetList FSets.FMapFacts OrderedType OrderedTypeEx.
From QuantumLib Require Export Matrix Pad Quantum.
From Qoreo Require Export Expr.Expr.
From Qoreo Require Export Expr.Typecheck.
From Qoreo Require Export Choreography.Choreography.
Export Var.Map.Tactics.

Structure ltap := { Df : ChorEnv.t Expr.Typ.t; Tf : ChorEnv.t nat }.

Fixpoint typecheck (G D : ChorEnv.t Expr.Typ.t) (T : ChorEnv.t nat ) (C : Choreography.t) : option ltap :=
  match C with
  | Choreography.Empty => Some {| Df := D; Tf := T |}
  | Choreography.Do (Insn.EPR A x B y) C => None
  | _ => None
  end.

Variant typecheck_result : Type := success | failure.

Definition essentially_empty {A} (m : ChorEnv.t A) : bool :=
  let f := fun _ m' b =>  Var.Map.domain_eqb m' (Var.Map.empty A) && b in
  Actor.Map.M.fold f m true.

Definition toplevel_typecheck (C : Choreography.t) : typecheck_result :=
  match typecheck ChorEnv.empty ChorEnv.empty ChorEnv.empty C with
  | None => failure
  | Some {| Df := D; Tf := T |} =>
      if essentially_empty D && essentially_empty T
      then success else failure
  end.
