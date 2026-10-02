(**
  Definition of the local quantum expression language

  Data structures:

  - `Expr.t` - Qoreo AST
  - `Expr.step` - small-step operational semantics
  - `Expr.typ` - Qoreo types
  - `Expr.WellTyped` - typing relation

  *)

From Stdlib Require Import FSets.FMapList FSets.FSetList FSets.FMapFacts OrderedType OrderedTypeEx.
From QuantumLib Require Import Matrix Pad Quantum.
From Qoreo.Base Require Var Config.
Import Config.Unitary.
Import Var.Map.Tactics.


Open Scope qoreo.

Inductive t :=
| Var : Var.t -> t
| LetIn : Var.t -> t -> t -> t
| Bang : t -> t
| LetBang : Var.t -> t -> t -> t
| Bit : bool -> t
| If : t -> t -> t -> t
| Pair : t -> t -> t
| LetPair : Var.t -> Var.t -> t -> t -> t
| Meas : t -> t
| QRef : Var.t -> t
| New : t -> t
| Unitary : unitary -> t -> t
| Lambda : Var.t -> t -> t
| Fix : Var.t -> Var.t -> t -> t
| App : t -> t -> t
.

Inductive Val : t -> Prop :=
| QRefVal : forall q,
  Val (QRef q)
(*| VarVal : forall x, Val x*)
| BangVal : forall e,
  Val (Bang e)
| BitVal  : forall b,
  Val (Bit b)
| PairVal : forall v1 v2,
  Val v1 -> Val v2 ->
  Val (Pair v1 v2)
| LambdaVal : forall x e,
  Val (Lambda x e)
| FixVal    : forall f x e,
  Val (Fix f x e)
.
#[global] Hint Constructors Val : var_db.


(* Return the set of variables that occur (anywhere, not necessarily free) in the expression *)
Fixpoint vars (e : t) : Var.FSet.t :=
  match e with
  | Var x | QRef x => Var.FSet.singleton x 

  | LetIn x e1 e2 | LetBang x e1 e2 =>
    Var.FSet.add x (Var.FSet.union (vars e1) (vars e2))

  | Bit _ => Var.FSet.empty
  | Bang e | Meas e | New e | Unitary _ e =>
    vars e
  | Pair e1 e2 | App e1 e2 =>
    Var.FSet.union (vars e1) (vars e2)
  | If e0 e1 e2 =>
    Var.FSet.union (vars e0) (Var.FSet.union (vars e1) (vars e2))
  
  | LetPair x1 x2 e1 e2 =>
    Var.FSet.add x1 (Var.FSet.add x2 (Var.FSet.union (vars e1) (vars e2)))
  
  | Lambda x e' => Var.FSet.add x (vars e')
  | Fix f x e' => Var.FSet.add f (Var.FSet.add x (vars e'))
  
  end.


(**************************)
(** Operational Semantics *)
(**************************)

Inductive Fresh x : Expr.t -> Prop :=
| FVar : forall y, ~ Var.V.eq x y -> Fresh x (Var y)
| FLetIn : forall y e1 e2,
  Fresh x e1 ->
  ~ Var.V.eq x y ->
  Fresh x e2 ->
  Fresh x (LetIn y e1 e2)
| FBang : forall e, Fresh x e -> Fresh x (Bang e)
| FLetBang : forall y e1 e2,
  Fresh x e1 ->
  ~ Var.V.eq x y ->
  Fresh x e2 ->
  Fresh x (LetBang y e1 e2)
| FBit : forall b, Fresh x (Bit b)
| FIf : forall e e1 e2,
  Fresh x e -> Fresh x e1 -> Fresh x e2 ->
  Fresh x (If e e1 e2)
| FPair : forall e1 e2,
  Fresh x e1 -> Fresh x e2 ->
  Fresh x (Pair e1 e2)
| FLetPair : forall y1 y2 e1 e2,
  Fresh x e1 ->
  ~ Var.V.eq x y1 ->
  ~ Var.V.eq x y2 ->
  Fresh x e2 ->
  Fresh x (LetPair y1 y2 e1 e2)
| FMeas : forall e, Fresh x e -> Fresh x (Meas e)
| FQRef : forall q, Fresh x (QRef q)
| FNew : forall e, Fresh x e -> Fresh x (New e)
| FUnitary : forall u e, Fresh x e -> Fresh x (Unitary u e)
| FLambda : forall y e,
  ~ Var.V.eq x y ->
  Fresh x e ->
  Fresh x (Lambda y e)
| FFix : forall f y e,
  ~ Var.V.eq x f ->
  ~ Var.V.eq x y ->
  Fresh x e ->
  Fresh x (Fix f y e)
| FApp : forall e1 e2,
  Fresh x e1 -> Fresh x e2 ->
  Fresh x (App e1 e2)
.

(* Assume x is fresh in e, and v is closed *)
Fixpoint subst x v e :=
  match e with
  | Var y => if Var.eq_dec x y then v else Var y
  | LetIn y e1 e2 =>
    LetIn y (subst x v e1) (if Var.eq_dec x y then e2 else subst x v e2)
  | Bang e => Bang (subst x v e)
  | LetBang y e1 e2 =>
    LetBang y (subst x v e1) (if Var.eq_dec x y then e2 else subst x v e2)
  | Bit b => Bit b
  | If e e1 e2 => If (subst x v e) (subst x v e1) (subst x v e2)
  | Pair e1 e2 => Pair (subst x v e1) (subst x v e2)
  | LetPair y1 y2 e1 e2 =>
    LetPair y1 y2 (subst x v e1)
      (if Var.eq_dec x y1 then e2
       else if Var.eq_dec x y2 then e2
       else subst x v e2)
  | Meas e => Meas (subst x v e)
  | QRef q => QRef q
  | New e => New (subst x v e)
  | Unitary u e => Unitary u (subst x v e)
  | Lambda y e =>
    Lambda y (if Var.eq_dec x y then e else subst x v e)
  | Fix f y e =>
    Fix f y (if Var.eq_dec x f then e
             else if Var.eq_dec x y then e
             else subst x v e)
  | App e1 e2 => App (subst x v e1) (subst x v e2)
  end.



Inductive step : Expr.t -> Var.Map.t nat -> Config.t -> Expr.t -> Var.Map.t nat -> Config.t -> Prop :=

(* Let *)
| LetC :
  forall x e1 e2 refs cfg e1' refs' cfg',
  
  step e1 refs cfg e1' refs' cfg' ->
  step (LetIn x e1 e2) refs cfg (LetIn x e1' e2) refs' cfg'

| LetB : forall x v1 e2 refs cfg e2' refs',
  Val v1 ->
  e2' = subst x v1 e2 ->
  Var.Map.Equal refs' refs ->
  step (LetIn x v1 e2) refs cfg e2' refs' cfg

(* Bang *)
(* no reduction under Bang *)

(* LetBang *)
| LetBangC :
  forall x e1 e2 refs cfg e1' refs' cfg',

  step e1 refs cfg e1' refs' cfg' ->

  step (LetBang x e1  e2) refs cfg
       (LetBang x e1' e2) refs' cfg'

| LetBangB : forall x e1 e2 refs cfg e2' refs',
  e2' = subst x e1 e2 ->
  Var.Map.Equal refs refs' ->

  step (LetBang x (Bang e1) e2) refs cfg
       e2' refs' cfg

(* If *)
| IfC : forall e1 e2 e3 refs cfg e1' refs' cfg',
  step e1 refs cfg e1' refs' cfg' ->

  step (If e1  e2 e3) refs cfg
       (If e1' e2 e3) refs' cfg'
  

| IfB : forall (b : bool) e2 e3 refs cfg e' refs',

  (e' = if b then e2 else e3) ->
  Var.Map.Equal refs refs' ->
  
  step (If (Bit b) e2 e3) refs cfg
       e' refs' cfg

(* Pair *)
| PairC1 : forall e1 e2 refs cfg e1' refs' cfg',
  step e1 refs cfg e1' refs' cfg' ->

  step (Pair e1 e2) refs cfg (Pair e1' e2) refs' cfg'

| PairC2 : forall e1 e2 refs cfg e2' refs' cfg',

  Val e1 ->
  step e2 refs cfg e2' refs' cfg' ->

  step (Pair e1 e2) refs cfg (Pair e1 e2') refs' cfg'

(* LetPair *)
| LetPairC : forall x1 x2 e1 e2 refs cfg e1' refs' cfg',

  step e1 refs cfg e1' refs' cfg' ->

  step (LetPair x1 x2 e1 e2) refs cfg
       (LetPair x1 x2 e1' e2) refs' cfg'

| LetPairB : forall x1 x2 v1 v2 e' refs cfg e'' refs',
  Val (Pair v1 v2) ->
  e'' = subst x2 v2 (subst x1 v1 e') ->
  Var.Map.Equal refs refs' ->

  step (LetPair x1 x2 (Pair v1 v2) e') refs cfg 
        e'' refs' cfg

| AppC1 : forall e1 e2 refs cfg e1' refs' cfg',

  step e1 refs cfg e1' refs' cfg' ->

  step (App e1 e2) refs cfg
        (App e1' e2) refs' cfg'

| AppC2 : forall e1 e2 refs cfg e2' refs' cfg',

  Val e1 ->
  step e2 refs cfg e2' refs' cfg' ->

  step (App e1 e2) refs cfg
        (App e1 e2') refs' cfg'

| AppB : forall x e v refs cfg e' refs',

  Val v ->
  e' = subst x v e ->
  Var.Map.Equal refs refs' ->

  step (App (Lambda x e) v) refs cfg
        e' refs' cfg

| AppFixB : forall f x e e0 refs cfg e' refs',

  e' = subst x e0 (subst f (Fix f x e) e) ->
  Var.Map.Equal refs refs' ->

  step (App (Fix f x e) (Bang e0)) refs cfg e' refs' cfg

(* New *)
| NewC : forall e refs cfg e' refs' cfg',

  step e refs cfg e' refs' cfg' ->

  step (New e) refs cfg (New e') refs' cfg'

| NewB : forall refs0 b refs cfg x refs' cfg',

  (x, refs0, cfg') = Config.new b refs cfg ->
  Var.Map.Equal refs0 refs' ->

  step (New (Bit b)) refs cfg
        (QRef x) refs' cfg'

(* Meas *)
| MeasC : forall e refs cfg e' refs' cfg',

  step e refs cfg e' refs' cfg' ->

  step (Meas e)  refs  cfg
       (Meas e') refs' cfg'

| MeasB : forall refs0 b x refs cfg refs' cfg',
  Var.Map.In x refs ->
  (refs0, cfg') = Config.measure b x refs cfg ->
  Var.Map.Equal refs0 refs' ->

  step (Meas (QRef x)) refs cfg (Bang (Bit b)) refs' cfg'


(* Unitary *)
| UnitaryC : forall u e refs cfg e' refs' cfg',

  step e refs cfg e' refs' cfg' ->

  step (Unitary u e) refs cfg
       (Unitary u e') refs' cfg'

| UnitaryB1 : forall g q refs refs' cfg cfg',
  Var.Map.In q refs ->
  cfg' = Config.apply_gate g [q] refs cfg ->
  Var.Map.Equal refs refs' ->

  step (Unitary g (QRef q)) refs cfg
       (QRef q) refs' cfg'

| UnitaryB2 : forall g q1 q2 refs refs' cfg cfg',
  Var.Map.In q1 refs ->
  Var.Map.In q2 refs ->
  q1 <> q2 ->
  cfg' = Config.apply_gate g [q1;q2] refs cfg ->
  Var.Map.Equal refs refs' ->

  step (Unitary g (Pair (QRef q1) (QRef q2))) refs cfg
       (Pair (QRef q1) (QRef q2)) refs' cfg'
.


(**********)
(** Types *)
(**********)

Inductive typ :=
| BIT | QUBIT
| Tensor : typ -> typ -> typ
| Lolli : typ -> typ -> typ
| BANG : typ -> typ.

Definition type_of_unitary (U : unitary) : typ :=
match U with
| CNOT => Tensor QUBIT QUBIT
| _ => QUBIT
end.


(* Typing judgment: Γ; Δ; Θ ⊢ t : τ 
 *  Γ : a finite map of non-linear variables to types
 *  Δ : a finite map of linear variables to types
 *  Θ : a finite map of qref variables to natural number indices
 *)
Inductive WellTyped : Var.Map.t typ -> Var.Map.t typ -> Var.Map.t nat -> Expr.t -> typ -> Prop :=

| WTQVar : forall Γ Δ Θ x τ,
  ~ Var.Map.In x Γ ->
  Var.Map.Singleton x τ Δ ->
  Var.Map.Empty Θ ->
  WellTyped Γ Δ Θ (Var x) τ

| WTCVar : forall Γ Δ Θ x τ,
  Var.Map.Empty Δ ->
  Var.Map.Empty Θ ->
  Var.Map.MapsTo x τ Γ ->
  WellTyped Γ Δ Θ (Var x) τ

| WTLetIn : forall Δ1 Δ2 Θ1 Θ2 τ Γ Δ Θ x e1 e2 τ',
  WellTyped Γ Δ1 Θ1 e1 τ ->

  WellTyped (Var.Map.remove x Γ) (Var.Map.add x τ Δ2) Θ2 e2 τ' ->
  
  Var.Map.Partition Δ Δ1 Δ2 ->
  ~ Var.Map.In x Δ2 ->
  Var.Map.Partition Θ Θ1 Θ2 ->

  WellTyped Γ Δ Θ (LetIn x e1 e2) τ'

| WTBang : forall Γ Δ Θ e τ,
  WellTyped Γ Δ Θ e τ ->

  Var.Map.Empty Δ ->
  Var.Map.Empty Θ ->

  WellTyped Γ Δ Θ (Bang e) (BANG τ)

| WTLetBang : forall τ Δ1 Δ2 Θ1 Θ2 Γ Δ Θ x e1 e2 τ',
  WellTyped Γ Δ1 Θ1 e1 (BANG τ) ->
  WellTyped (Var.Map.add x τ Γ) Δ2 Θ2 e2 τ' ->

  Var.Map.Partition Δ Δ1 Δ2 ->
  Var.Map.Partition Θ Θ1 Θ2 ->
  ~ Var.Map.In x Δ2 ->

  WellTyped Γ Δ Θ (LetBang x e1 e2) τ'

| WTBit : forall Γ Δ Θ b,
  Var.Map.Empty Δ ->
  Var.Map.Empty Θ ->
  WellTyped Γ Δ Θ (Bit b) BIT

| WTIf : forall Δ1 Δ2 Θ1 Θ2 Γ Δ Θ e eT eF τ,

  WellTyped Γ Δ1 Θ1 e BIT ->
  WellTyped Γ Δ2 Θ2 eT τ ->
  WellTyped Γ Δ2 Θ2 eF τ ->

  Var.Map.Partition Δ Δ1 Δ2 ->
  Var.Map.Partition Θ Θ1 Θ2 ->

  WellTyped Γ Δ Θ (If e eT eF) τ

| WTPair : forall Δ1 Δ2 Θ1 Θ2 Γ Δ Θ e1 e2 τ1 τ2,
  WellTyped Γ Δ1 Θ1 e1 τ1 ->
  WellTyped Γ Δ2 Θ2 e2 τ2 ->

  Var.Map.Partition Δ Δ1 Δ2 ->
  Var.Map.Partition Θ Θ1 Θ2 ->

  WellTyped Γ Δ Θ (Pair e1 e2) (Tensor τ1 τ2)

| WTLetPair : forall Δ1 Δ2 Θ1 Θ2 τ1 τ2 Γ Δ Θ x1 x2 e e' τ',

  WellTyped Γ Δ1 Θ1 e (Tensor τ1 τ2) ->
  WellTyped (Var.Map.remove x1 (Var.Map.remove x2 Γ))
            (Var.Map.add x1 τ1 (Var.Map.add x2 τ2 Δ2))
            Θ2 e' τ' ->
  
  Var.Map.Partition Δ Δ1 Δ2 ->
  ~ Var.Map.In x1 Δ2 ->
  ~ Var.Map.In x2 Δ2 ->
  x1 <> x2 ->
  Var.Map.Partition Θ Θ1 Θ2 ->

  WellTyped Γ Δ Θ (LetPair x1 x2 e e') τ'

| WTMeas : forall Γ Δ Θ e,
  WellTyped Γ Δ Θ e QUBIT ->
  WellTyped Γ Δ Θ (Meas e) (BANG BIT)

| WTQRef : forall Γ Δ Θ q idx,

  Var.Map.Empty Δ ->
  Var.Map.Singleton q idx Θ ->

  WellTyped Γ Δ Θ (QRef q) QUBIT

| WTNew : forall Γ Δ Θ e,
  WellTyped Γ Δ Θ e BIT ->
  WellTyped Γ Δ Θ (New e) QUBIT

| WTUnitary : forall Γ Δ Θ U e τ,
  type_of_unitary U = τ ->
  WellTyped Γ Δ Θ e τ ->
  WellTyped Γ Δ Θ (Unitary U e) τ

| WTLambda : forall Γ Δ Θ x e τ1 τ2,
  ~ Var.Map.In x Δ ->
  WellTyped (Var.Map.remove x Γ) (Var.Map.add x τ1 Δ) Θ e τ2 ->
  WellTyped Γ Δ Θ (Lambda x e) (Lolli τ1 τ2)

| WTFix : forall Γ Δ Θ f x e τ1 τ2,

  WellTyped (Var.Map.add f (Lolli (BANG τ1) τ2) (Var.Map.add x τ1 Γ)) Δ Θ e τ2 ->

  Var.Map.Empty Δ ->
  Var.Map.Empty Θ  ->
  f <> x ->

  WellTyped Γ Δ Θ (Fix f x e) (Lolli (BANG τ1) τ2)

| WTApp : forall Δ1 Δ2 Θ1 Θ2 τ Γ Δ Θ e1 e2 τ',
  WellTyped Γ Δ1 Θ1 e1 (Lolli τ τ') ->
  WellTyped Γ Δ2 Θ2 e2 τ ->

  Var.Map.Partition Δ Δ1 Δ2 ->
  Var.Map.Partition Θ Θ1 Θ2 ->

  WellTyped Γ Δ Θ (App e1 e2) τ'
.

Hint Constructors WellTyped : qoreo_db.


Definition WellTypedConfig (refs : Var.Map.t nat) e tau : Prop :=
  WellTyped (Var.Map.empty _) (Var.Map.empty _) refs e tau.



(** ** Type safety *)

Inductive multi_step : t -> Var.Map.t nat -> Config.t -> t -> Var.Map.t nat -> Config.t -> Prop :=
| Step0 : forall e Θ cfg, multi_step e Θ cfg e Θ cfg
| Step1 : forall e1 e2 e3 Θ1 Θ2 Θ3 cfg1 cfg2 cfg3,
  step e1 Θ1 cfg1 e2 Θ2 cfg2 ->
  multi_step e2 Θ2 cfg2 e3 Θ3 cfg3 ->
  multi_step e1 Θ1 cfg1 e3 Θ3 cfg3.

Definition can_step e Θ cfg :=
  exists e' Θ' cfg', step e Θ cfg e' Θ' cfg'.
