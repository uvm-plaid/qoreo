From Qoreo Require Quantum.

From Stdlib Require Lists.List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Structures.Equalities.

Module Choreography (Actor : DecidableType).
    Inductive insn : Type :=

    | Send : Actor.t -> Quantum.expr -> Actor.t -> Quantum.var -> insn
    | EPR : Actor.t -> Quantum.var -> Actor.t -> Quantum.var -> insn

    | Let : Actor.t -> Quantum.var -> Quantum.expr -> insn
    | LetBang : Actor.t -> Quantum.var -> Quantum.expr -> insn
    | LetPair : Actor.t -> Quantum.var -> Quantum.var -> Quantum.expr -> insn.
    Definition t := list insn.

    Definition actorsI (I : insn) : list Actor.t :=
        match I with
        | Send A _ B _ => [ A ; B ]
        | EPR A _ B _ => [A;B]
        | Let A _ _ => [A]
        | LetBang A _ _ => [A]
        | LetPair A _ _ _ => [A]
        end.

    Definition actors (C : t) : list Actor.t :=
        List.fold_right (fun I => List.app (actorsI I)) [] C.

    Inductive label :=
    | sendL : Actor.t -> Quantum.expr -> Actor.t -> label
    | eprL  : Actor.t -> Actor.t -> label
    | localL : Actor.t -> label
    .

    Definition actorsL (l : label) : list Actor.t :=
        match l with
        | sendL A _ B => [A;B]
        | eprL A B => [A; B]
        | localL A => [A]
        end.

    Definition disjoint (ls1 ls2 : list Actor.t) : Prop :=
        List.Forall (fun a => ~ List.In a ls2) ls1.




(** Semantics **)

(* substitute the value v for A.x in I *)
    Definition substI (A : Actor.t) (x : Quantum.var) (v : Quantum.expr)  (I : insn) : insn :=
    match I with
    | Send B1 e B2 y => 
        (* Assume x <> y *)
        let e' := if Actor.eq_dec A B1 then Quantum.subst x v e else e in
        Send B1 e' B2 y : insn
    | EPR B1 y1 B2 y2 => EPR B1 y1 B2 y2
    | Let B y e =>
        let e' := if Actor.eq_dec A B then Quantum.subst x v e else e in
        Let B y e'
    | LetBang B y e =>
        let e' := if Actor.eq_dec A B then Quantum.subst x v e else e in
        LetBang B y e'
    | LetPair B y1 y2 e =>
        let e' := if Actor.eq_dec A B then Quantum.subst x v e else e in
        LetPair B y1 y2 e'
    end.

    Definition subst    (A : Actor.t) (x : Quantum.var) (v : Quantum.expr)
                        (C : t) : t :=
        List.map (substI A x v) C.


Inductive step : t * Quantum.Config.t -> label -> t * Quantum.Config.t -> Prop :=

| SendC : forall A e B x C cfg e' cfg',
    Quantum.step (e, cfg) (e', cfg') ->
    step (Send A e B x :: C, cfg) (localL A) (Send A e' B x :: C, cfg')

| SendB : forall A v B x C cfg C',
    Quantum.Val v ->
    C' = subst B x v C ->
    step (Send A v B x :: C, cfg) (sendL A v B) (C', cfg)

| EPRB : forall q1 q2 A x B y C cfg C' cfg',
    Quantum.Config.epr cfg = (q1,q2,cfg') ->
    C' = subst A x (Quantum.QRef q1) (subst B y (Quantum.QRef q2) C) ->
    step (EPR A x B y :: C, cfg) (eprL A B) (C', cfg')

| LetC : forall A x e C cfg e' cfg',
    Quantum.step (e,cfg) (e',cfg') ->
    step (Let A x e :: C, cfg) (localL A) (Let A x e' :: C, cfg')
| LetB : forall A x v C cfg C',
    Quantum.Val v ->
    C' = subst A x v C ->
    step (Let A x v :: C, cfg) (localL A) (C', cfg)

| LetBangC : forall A x e C cfg e' cfg',
    Quantum.step (e,cfg) (e',cfg') ->
    step (LetBang A x e :: C, cfg) (localL A) (LetBang A x e' :: C, cfg')
| LetBangB : forall A x e0 C cfg C',
    C' = subst A x e0 C ->
    step (LetBang A x (Quantum.Bang e0) :: C, cfg) (localL A) (C', cfg)

| LetPairC : forall A x1 x2 e C cfg e' cfg',
    Quantum.step (e,cfg) (e',cfg') ->
    step (LetPair A x1 x2 e :: C, cfg) (localL A) (LetPair A x1 x2 e' :: C, cfg')
| LetPairB : forall A x1 x2 v1 v2 C cfg C',
    Quantum.Val v1 -> Quantum.Val v2 ->
    C' = subst A x1 v1 (subst A x2 v2 C) ->
    step (LetPair A x1 x2 (Quantum.Pair v1 v2) :: C, cfg) (localL A) (C', cfg)

(* delay *)
| Delay : forall I C cfg C' cfg' l,
    step (C, cfg) l (C', cfg') ->
    disjoint (actorsL l) (actorsI I) ->
    step (I::C, cfg) l (I::C', cfg')
.

End Choreography.
