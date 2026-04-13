From Qoreo Require Import Base.
From Qoreo Require Expr Choreography.

Module Label := Choreography.Label.

From Stdlib Require Lists.List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Stdlib.Structures.Equalities.

Module Insn.
    Inductive t :=
    | Let : Var.t -> Expr.t -> t
    | LetBang : Var.t -> Expr.t -> t
    | LetPair : Var.t -> Var.t -> Expr.t -> t
    | Send : Expr.t -> Actor.t -> t
    | Receive : Var.t -> Actor.t ->  t
    | EPR : Var.t -> Actor.t -> t
    .

    Definition subst (x : Var.t) (v : Expr.t) (I : t) : t :=
        match I with
        | Let y e => Let y (Expr.subst x v e)
        | LetBang y e => LetBang y (Expr.subst x v e)
        | LetPair y1 y2 e => LetPair y1 y2 (Expr.subst x v e)
        | Send e A => Send (Expr.subst x v e) A
        | Receive y A => Receive y A
        | EPR y A => EPR y A
        end.

    Definition binders (I : t) : Var.FSet.t :=
        match I with
        | Let y _ | LetBang y _ | Receive y _ | EPR y _ => Var.FSet.singleton y
        | LetPair y1 y2 _ => Var.FSet.add y1 (Var.FSet.singleton y2)
        | Send _ _ => Var.FSet.empty
        end.
End Insn.

Module Process.
    Definition t := list Insn.t.

    Fixpoint subst (x : Var.t) (v : Expr.t) (P : t) : t :=
    match P with
    | [] => []
    | (I0 :: P') =>
      let P'' := if Var.FSet.mem x (Insn.binders I0)
                 then P'
                 else subst x v P'
      in
      (Insn.subst x v I0) :: P''
    end.


    (* Semantics *)

    Inductive step : Process.t * Config.t -> Process.t * Config.t -> Prop :=
    | LetC : forall x e P ρ e' ρ',
        Expr.step (e, ρ) (e', ρ') ->
        step (Insn.Let x e :: P, ρ) (Insn.Let x e' :: P, ρ')
    | LetB : forall x v P ρ P',
        Expr.Val v ->
        P' = Process.subst x v P ->
        step (Insn.Let x v :: P, ρ) (P', ρ)

    | LetBangC : forall x e P ρ e' ρ',
        Expr.step (e, ρ) (e', ρ') ->
        step (Insn.LetBang x e :: P, ρ) (Insn.LetBang x e' :: P, ρ')
    | LetBangB : forall x e P ρ P',
        P' = Process.subst x e P ->
        step (Insn.LetBang x (Expr.Bang e) :: P, ρ) (P', ρ)

    | LetPairC : forall x1 x2 e P ρ e' ρ',
        Expr.step (e, ρ) (e', ρ') ->
        step (Insn.LetPair x1 x2 e :: P, ρ) (Insn.LetPair x1 x2 e' :: P, ρ')
    | LetPairP : forall x1 x2 v1 v2 P ρ P',
        Expr.Val v1 -> Expr.Val v2 ->
        P' = Process.subst x2 v2 (Process.subst x1 v1 P) ->
        step (Insn.LetPair x1 x2 (Expr.Pair v1 v2) :: P, ρ) (P', ρ)

    | SendC : forall e B P ρ e' ρ',
        Expr.step (e, ρ) (e', ρ') ->
        step (Insn.Send e B :: P, ρ) (Insn.Send e' B :: P, ρ')
    .

End Process.

Module Network.
    Definition t := Actor.Map.t (Process.t).

    Inductive step : Network.t * Config.t -> Label.t -> Network.t * Config.t -> Prop :=

    | Loc : forall P P' N cfg A N' cfg',
      Actor.Map.MapsTo A P N ->
      Process.step (P, cfg) (P', cfg') ->
      N' = Actor.Map.add A P' N ->
      step (N, cfg) (Label.Loc A) (N', cfg')

    | Send : forall PA PB y N cfg A v B N',
      A <> B ->
      Actor.Map.MapsTo A (Insn.Send v B :: PA) N ->
      Actor.Map.MapsTo B (Insn.Receive y A :: PB) N ->
      Expr.Val v ->
      N' = Actor.Map.add A PA (Actor.Map.add B (Process.subst y v PB) N) ->
      
      step (N, cfg) (Label.Send A v B) (N', cfg)

    | EPR : forall x y PA PB qA qB N cfg A B N' cfg',
      A <> B ->
      Actor.Map.MapsTo A (Insn.EPR x B :: PA) N ->
      Actor.Map.MapsTo B (Insn.EPR y A :: PB) N ->
      Config.epr cfg = (qA, qB, cfg') ->
      N' = Actor.Map.add A (Process.subst x (Expr.QRef qA) PA) (
            Actor.Map.add B (Process.subst y (Expr.QRef qB) PB) N) ->

      step (N, cfg) (Label.EPR A B) (N', cfg')
    .
    
End Network.

Definition epp_insn (p : Actor.t) (c : Choreography.Insn.t): option Insn.t :=
  match c with
  | Choreography.Insn.Send A1 e A2 x =>
      if Actor.eq_dec A1 p then
        Some (Insn.Send e A2)
      else if Actor.eq_dec A2 p then
             Some (Insn.Receive x A1)
           else
             None
  | Choreography.Insn.EPR A1 x1 A2 x2 =>
      if Actor.eq_dec A1 p then
        Some (Insn.EPR x1 A2)
      else if Actor.eq_dec A2 p then
             Some (Insn.EPR x2 A1)
           else
             None
  | _ => None
end.

Fixpoint map_option {A B : Type} (f : A -> option B) (xs : list A)
  : option (list B) :=
  match xs with
  | [] => Some []
  | x :: xs' =>
      match f x, map_option f xs' with
      | Some y, Some ys => Some (y :: ys)
      | _, _ => None
      end
  end.

Definition epp (p : Actor.t) (c : Choreography.Choreography.t): option Process.t :=
  map_option (epp_insn p) c.
