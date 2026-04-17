From Stdlib Require Import String.
From Qoreo Require Import Base Expr Choreography.

Open Scope string_scope.

Module ExampleNotation.
  Import Choreography.

  Definition actor (name : string) : Actor.t := name.
  Definition var (n : nat) : Var.t := n.

  Definition ref (x : Var.t) : Expr.t := Expr.Var x.

  Definition measure (x : Var.t) : Expr.t :=
    Expr.Meas (ref x).

  Definition new (b : bool) : Expr.t :=
    Expr.New (Expr.Bit b).

  Definition apply1 (u : unitary) (x : Var.t) : Expr.t :=
    Expr.Unitary u (ref x).

  Definition apply2 (u : unitary) (x y : Var.t) : Expr.t :=
    Expr.Unitary u (Expr.Pair (ref x) (ref y)).

  Definition if_ (cond_ then_ else_ : Expr.t) : Expr.t :=
    Expr.If cond_ then_ else_.

  Notation "'epr{' A ',' x ';' B ',' y '}'" := (Insn.EPR A x B y)
    (at level 0, x at next level, y at next level).

  Notation "'send{' A ',' x '->' B ',' y '}'" := (Insn.Send A (ref x) B y)
    (at level 0, x at next level, y at next level).

  Notation "'let{' A ',' x ':=' e '}'" := (Insn.Let A x e)
    (at level 0, x at next level, e at next level).

  Notation "'let!{' A ',' x ':=' e '}'" := (Insn.LetBang A x e)
    (at level 0, x at next level, e at next level).

  Notation "'letp{' A ',' '(' x ',' y ')' ':=' e '}'" := (Insn.LetPair A x y e)
    (at level 0, x at next level, y at next level, e at next level).

  Notation "'H[' x ']'" := (apply1 H x)
    (at level 0, x at next level).
  Notation "'X[' x ']'" := (apply1 X x)
    (at level 0, x at next level).
  Notation "'Z[' x ']'" := (apply1 Z x)
    (at level 0, x at next level).
  Notation "'CNOT[' x ',' y ']'" := (apply2 CNOT x y)
    (at level 0, x at next level, y at next level).
  Notation "'Measure[' x ']'" := (measure x)
    (at level 0, x at next level).
  Notation "'New[' b ']'" := (new b)
    (at level 0, b at next level).
End ExampleNotation.
