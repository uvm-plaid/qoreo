From Stdlib Require Import String.
From Stdlib Require Lists.List.
Import List.ListNotations.

From Qoreo Require Import Base Expr Choreography Network NetQasm.

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

  Declare Custom Entry qexpr.
  Declare Custom Entry insn.
  Declare Custom Entry choreo.
  Declare Scope choreo_scope.

  Notation "'<{' c '}>'" := c
    (c custom choreo) : choreo_scope.

  Notation "i ; c" := (i :: c)
    (in custom choreo at level 90, right associativity,
     i custom insn at level 0, c custom choreo at level 90) : choreo_scope.
  Notation "i" := (i :: nil)
    (in custom choreo at level 90, i custom insn at level 0) : choreo_scope.

  Notation "x" := (Expr.Var x)
    (in custom qexpr at level 0, x constr at level 0) : choreo_scope.
  Notation "( x )" := x
    (in custom qexpr, x at level 99) : choreo_scope.
  Notation "'true'" := (Expr.Bit true)
    (in custom qexpr at level 0) : choreo_scope.
  Notation "'false'" := (Expr.Bit false)
    (in custom qexpr at level 0) : choreo_scope.
  Notation "'new' b" := (Expr.New b)
    (in custom qexpr at level 30, b custom qexpr at level 0) : choreo_scope.
  Notation "'measure' x" := (Expr.Meas x)
    (in custom qexpr at level 30, x custom qexpr at level 0) : choreo_scope.
  Notation "u x" := (Expr.Unitary u x)
    (in custom qexpr at level 30,
     u constr at level 0,
     x custom qexpr at level 0) : choreo_scope.
  Notation "u x y" := (Expr.Unitary u (Expr.Pair x y))
    (in custom qexpr at level 30,
     u constr at level 0,
     x custom qexpr at level 0,
     y custom qexpr at level 0) : choreo_scope.
  Notation "'if' c 'then' t 'else' f 'end'" := (Expr.If c t f)
    (in custom qexpr at level 89,
     c custom qexpr at level 0,
     t custom qexpr at level 30,
     f custom qexpr at level 0) : choreo_scope.

  Notation "'epr' A ',' x ';' B ',' y" := (Choreography.Insn.EPR A x B y)
    (in custom insn at level 0,
     A constr at level 0,
     x constr at level 0,
     B constr at level 0,
     y constr at level 0) : choreo_scope.
  Notation "A ',' x '->' B ',' y" := (Choreography.Insn.Send A (Expr.Var x) B y)
    (in custom insn at level 0,
     A constr at level 0,
     x constr at level 0,
     B constr at level 0,
     y constr at level 0) : choreo_scope.
  Notation "'let' A ',' x ':=' e" := (Choreography.Insn.Let A x e)
    (in custom insn at level 0,
     A constr at level 0,
     x constr at level 0,
     e custom qexpr at level 99) : choreo_scope.
  Notation "'let!' A ',' x ':=' e" := (Choreography.Insn.LetBang A x e)
    (in custom insn at level 0,
     A constr at level 0,
     x constr at level 0,
     e custom qexpr at level 99) : choreo_scope.
  Notation "'letp' A ',' '(' x ',' y ')' ':=' e" := (Choreography.Insn.LetPair A x y e)
    (in custom insn at level 0,
     A constr at level 0,
     x constr at level 0,
     y constr at level 0,
     e custom qexpr at level 99) : choreo_scope.

End ExampleNotation.

Module ExampleExtraction.
  Definition render_party (choreo : Choreography.t) (p : Actor.t)
    : option AppFile.t :=
    match Network.epp p choreo with
    | Some proc =>
        Some {| AppFile.party := p; AppFile.source := render_app p proc |}
    | None => None
    end.

  Fixpoint render_parties (choreo : Choreography.t) (ps : list Actor.t)
    : option (list AppFile.t) :=
    match ps with
    | [] => Some []
    | p :: ps' =>
        match render_party choreo p, render_parties choreo ps' with
        | Some app, Some apps => Some (app :: apps)
        | _, _ => None
        end
    end.
End ExampleExtraction.
