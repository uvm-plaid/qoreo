From Stdlib Require Import FSets.FMapList FSets.FSetList FSets.FMapFacts OrderedType OrderedTypeEx.
From QuantumLib Require Import Matrix Pad Quantum.
From Qoreo Require Import Base.
Import Base.Var.Tactics.

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
(*| QRef : Var.t -> t*)
| New : t -> t
| Unitary : unitary -> t -> t
| Lambda : Var.t -> t -> t
| Fix : Var.t -> Var.t -> t -> t
| App : t -> t -> t
.

(*
Inductive WFRefs : Var.Map.t nat -> Expr.t -> Prop :=
| WFVar : forall refs x,
  Var.Map.Empty refs ->
  WFRefs refs (Var x)
| WFLetIn : forall refs x e1 e2 refs1 refs2,
  WFRefs refs1 e1 ->
  WFRefs refs2 e2 ->
  Var.MapFacts.Partition refs refs1 refs2 ->
  WFRefs refs (LetIn x e1 e2)
| WFBang : forall refs e,
  WFRefs refs e ->
  WFRefs refs (Bang e)
| WFLetBang : forall refs x e1 e2 refs1 refs2,
  WFRefs refs1 e1 ->
  WFRefs refs2 e2 ->
  Var.MapFacts.Partition refs refs1 refs2 ->
  WFRefs refs (LetBang x e1 e2)
| WFBit : forall refs b,
  Var.Map.Empty refs ->
  WFRefs refs (Bit b)

| WFIf : forall refs' refs'' refs e e1 e2,

  WFRefs refs' e ->
  WFRefs refs'' e1 ->
  WFRefs refs'' e2 ->

  Var.MapFacts.Partition refs refs' refs'' ->
  WFRefs refs (If e e1 e2)

| WFPair : forall refs e1 e2 refs1 refs2,
  WFRefs refs1 e1 ->
  WFRefs refs2 e2 ->
  Var.MapFacts.Partition refs refs1 refs2 ->
  WFRefs refs (Pair e1 e2)
| WFLetPair : forall refs x1 x2 e1 e2 refs1 refs2,
  WFRefs refs1 e1 ->
  WFRefs refs2 e2 ->
  Var.MapFacts.Partition refs refs1 refs2 ->
  WFRefs refs (LetPair x1 x2 e1 e2)
| WFMeas : forall refs e,
  WFRefs refs e ->
  WFRefs refs (Meas e)
(*| WFQRef : forall refs x q,
  Var.Singleton x q refs ->
  WFRefs refs (QRef x)
  *)
| WFNew : forall refs e,
  WFRefs refs e ->
  WFRefs refs (New e)
| WFUnitary : forall refs u e,
  WFRefs refs e ->
  WFRefs refs (Unitary u e)
| WFLambda : forall refs x e,
  WFRefs refs e ->
  WFRefs refs (Lambda x e)
| WFFix : forall refs f x e,
  WFRefs refs e ->
  WFRefs refs (Fix f x e)
| WFApp : forall refs e1 e2 refs1 refs2,
  WFRefs refs1 e1 ->
  WFRefs refs2 e2 ->
  Var.MapFacts.Partition refs refs1 refs2 ->
  WFRefs refs (App e1 e2)
.
*)

Inductive Val : t -> Prop :=
| QRefVal : forall q,
  Val (Var q)
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

(*************************)
(* Operational Semantics *)
(*************************)

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
(*| FQRef : forall q, Fresh x (QRef q)*)
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
  (*| QRef q => QRef q*)
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

| LetB : forall x v1 e2 refs cfg e2',
  Val v1 ->
  e2' = subst x v1 e2 ->
  step (LetIn x v1 e2) refs cfg e2' refs cfg

(* Bang *)
(* no reduction under Bang *)

(* LetBang *)
| LetBangC :
  forall x e1 e2 refs cfg e1' refs' cfg',

  step e1 refs cfg e1' refs' cfg' ->

  step (LetBang x e1  e2) refs cfg
       (LetBang x e1' e2) refs' cfg'

| LetBangB : forall x e1 e2 refs cfg e2',
  e2' = subst x (Bang e1) e2 ->

  step (LetBang x (Bang e1) e2) refs cfg
       e2' refs cfg

(* If *)
| IfC : forall e1 e2 e3 refs cfg e1' refs' cfg',
  step e1 refs cfg e1' refs' cfg' ->

  step (If e1  e2 e3) refs cfg
       (If e1' e2 e3) refs' cfg'
  

| IfB : forall (b : bool) e2 e3 refs cfg e',

  (e' = if b then e2 else e3) ->
  
  step (If (Bit b) e2 e3) refs cfg
       e' refs cfg

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

| LetPairB : forall x1 x2 v1 v2 e' refs cfg e'',
  Val (Pair v1 v2) ->
  e'' = subst x2 v2 (subst x1 v1 e') ->

  step (LetPair x1 x2 (Pair v1 v2) e') refs cfg 
        e'' refs cfg

| AppC1 : forall e1 e2 refs cfg e1' refs' cfg',

  step e1 refs cfg e1' refs' cfg' ->

  step (App e1 e2) refs cfg
        (App e1' e2) refs' cfg'

| AppC2 : forall e1 e2 refs cfg e2' refs' cfg',

  Val e1 ->
  step e2 refs cfg e2' refs' cfg' ->

  step (App e1 e2) refs cfg
        (App e1 e2') refs' cfg'

| AppB : forall x e v refs cfg e',

  Val v ->
  e' = subst x v e ->

  step (App (Lambda x e) v) refs cfg
        e' refs cfg

| AppFixB : forall f x e v refs cfg e',

  Val v ->
  e' = subst x v (subst f (Fix f x e) e) ->

  step (App (Fix f x e) v) refs cfg e' refs cfg


(* New *)
| NewC : forall e refs cfg e' refs' cfg',

  step e refs cfg e' refs' cfg' ->

  step (New e) refs cfg (New e') refs' cfg'

| New0 : forall b refs cfg x refs' cfg',

  (x, refs', cfg') = Config.new b refs cfg ->

  step (New (Bit b)) refs cfg
        (Var x) refs' cfg'

(* Meas *)
| MeasC : forall e refs cfg e' refs' cfg',

  step e refs cfg e' refs' cfg' ->

  step (Meas e)  refs  cfg
       (Meas e') refs' cfg'

| MeasB : forall i b x refs cfg refs' cfg',
  Var.Singleton x i refs ->
  (refs', cfg') = Config.measure b x refs cfg ->

  step (Meas (Var x)) refs cfg (Bit b) refs' cfg'


(* Unitary *)
| UnitaryC : forall u e refs cfg e' refs' cfg',

  step e refs cfg e' refs' cfg' ->

  step (Unitary u e) refs cfg
       (Unitary u e') refs' cfg'

| UnitaryB1 : forall i g q refs cfg cfg',
  Var.Singleton q i refs ->
  cfg' = Config.apply_gate g [q] refs cfg ->

  step (Unitary g (Var q)) refs cfg
       (Var q) refs cfg'

| UnitaryB2 : forall i1 i2 g q1 q2 refs cfg cfg',
  Var.Map.Equal refs (Var.Map.add q1 i1 (Var.Map.add q2 i2 (Var.Map.empty _))) ->
  cfg' = Config.apply_gate g [q1;q2] refs cfg ->

  step (Unitary g (Pair (Var q1) (Var q2))) refs cfg
       (Pair (Var q1) (Var q2)) refs cfg'
.

(*
Lemma wfrefs_val : forall refs v,
  Val refs v ->
  WFRefs refs v.
Proof.
  intros ? ? Hval.
  induction Hval; econstructor; eauto.
Qed.
Hint Resolve wfrefs_val : qoreo_db.
Hint Constructors WFRefs : qoreo_db.
*)
(*
*)

(*
Lemma wfrefs_step : forall e refs cfg e' refs' cfg',
  step e refs cfg e' refs' cfg' ->
  WFRefs refs e.
Proof.
  intros ? ? ? ? ? ? Hstep.
  induction Hstep;
    eauto with qoreo_db var_db.
  * econstructor.
    econstructor; eauto with qoreo_db var_db.
    rewrite H.
    auto with var_db.
Qed.

(* need to add the typing judgment to this to make sure it actually gets substituted correctly....... this lemma is not correct as stated 
and then what about the bang substitution.... it should indeed be the case that there are no qrefs in bang...*)
Lemma wfrefs_subst : forall refs1 refs2 refs x v1 e2,
  Val refs1 v1 ->
  WFRefs refs2 e2 ->
  Var.MapFacts.Partition refs refs1 refs2 ->
  WFRefs refs (subst x v1 e2).
Admitted.
*)








(*Hint Rewrite var_remove_map : var_db.*)


(* If map _ refs == Δ1 + Δ2 
  Then there exist refs1 and refs2 such that
    Δ1=map _ refs1 /\ Δ2 = map _ refs2
  such that refs == refs1 + refs2
*)


    

(*
Lemma wfrefs_step_r : forall e refs cfg e' refs' cfg',
  step e refs cfg e' refs' cfg' ->
  WFRefs refs' e'.
Proof.
  intros ? ? ? ? ? ? Hstep.
  induction Hstep; subst; eauto with qoreo_db var_db.
  * eapply wfrefs_subst; eauto.
  * eapply wfrefs_subst; eauto.
    constructor; auto.
  * destruct b; auto.
  * inversion H; subst; clear H.
    eapply wfrefs_subst; eauto.
    eapply wfrefs_subst; eauto.
    admit (* true *) .
    admit (* true *).
  * eapply wfrefs_subst; eauto. admit (* symmetry *).
  * eapply wfrefs_subst; eauto.
    eapply wfrefs_subst; eauto.
    { constructor; eauto. }
    admit (* wrong? *).
    admit (* symmetry *).
  * unfold Config.new in *.
    inversion H0; subst; clear H0.
    econstructor.
    unfold Var.Singleton.
    assert (Var.Map.Equal refs (Var.Map.empty nat))
      by (vsimpl; reflexivity).
    admit (* not sure why this isn't going through *).
    
  * inversion H0; subst; clear H0.
    constructor. constructor.
    unfold Var.Singleton in *.
    rewrite H.
    autorewrite with var_db.
    vsimpl.
  * econstructor.
    { econstructor. unfold Var.Singleton. reflexivity. }
    { econstructor. unfold Var.Singleton. reflexivity. }
    rewrite H. eauto with var_db.
  Unshelve.
  + apply Var.Map.empty.
  + apply Var.Map.empty.
  + exact 0%nat.
Admitted. 
*)

(*
Fixpoint qrefs (e : Expr.t) : Var.FSet.t :=
  match e with
  | Var _ => Var.FSet.empty
  | LetIn _ e1 e2 => Var.FSet.union (qrefs e1) (qrefs e2)
  | Bang e => qrefs e
  | LetBang _ e1 e2 => Var.FSet.union (qrefs e1) (qrefs e2)
  | Bit _ => Var.FSet.empty
  | If e e1 e2 => Var.FSet.union (Var.FSet.union (qrefs e) (qrefs e1)) (qrefs e2)
  | Pair e1 e2 => Var.FSet.union (qrefs e1) (qrefs e2)
  | LetPair _ _ e1 e2 => Var.FSet.union (qrefs e1) (qrefs e2)
  | Meas e => qrefs e
  | QRef x => Var.FSet.singleton x
  | New e => qrefs e
  | Unitary _ e => qrefs e
  | Lambda _ e => qrefs e
  | Fix _ _ e => qrefs e
  | App e1 e2 => Var.FSet.union (qrefs e1) (qrefs e2)
  end.
*)

(*
Lemma scope_preservation : forall e refs cfg e' refs' cfg',
  step e refs cfg e' refs' cfg' ->
  WFRefs refs cfg e ->
  WFRefs refs' cfg' e'.
Proof.
  intros ? ? ? ? ? ? Hstep.
  induction Hstep; inversion 1; subst.
  * econstructor; eauto.
    apply IHHstep; auto. 


(* WFConfig S e: the set of all QRefs in expression e is exactly S *)
Inductive WFConfig : Config.t -> Expr.t -> Prop :=
| QRVar : forall cfg x,
  Config.Refs.Empty cfg ->
  WFConfig cfg (Var x)

| QRQRef : forall cfg x,
  Config.Refs.Singleton x cfg ->
  WFConfig cfg (QRef x)

| QRLetIn : forall x e1 e2 cfg cfg1 cfg2,
  WFConfig cfg1 e1 ->
  WFConfig cfg2 e2 ->
  Config.Refs.Partition cfg cfg1 cfg2 ->
  WFConfig cfg (LetIn x e1 e2)

| QRBang : forall e cfg,
  WFConfig cfg e ->
  WFConfig cfg (Bang e)

| QRLetBang : forall x e1 e2 cfg cfg1 cfg2,
  WFConfig cfg1 e1 ->
  WFConfig cfg2 e2 ->
  Config.Refs.Partition cfg cfg1 cfg2 ->
  WFConfig cfg (LetBang x e1 e2)

| QRBit : forall b cfg,
  Config.Refs.Empty cfg ->
  WFConfig cfg (Bit b)

| QRIf : forall e e1 e2 cfg cfg' cfg'',
  WFConfig cfg' e ->
  WFConfig cfg'' e1 ->
  WFConfig cfg'' e2 ->
  Config.Refs.Partition cfg cfg' cfg'' ->
  WFConfig cfg (If e e1 e2)

| QRPair : forall e1 e2 cfg cfg1 cfg2,
  WFConfig cfg1 e1 ->
  WFConfig cfg2 e2 ->
  Config.Refs.Partition cfg cfg1 cfg2 ->
  WFConfig cfg (Pair e1 e2)

| QRLetPair : forall x1 x2 e1 e2 cfg cfg1 cfg2,
  WFConfig cfg1 e1 ->
  WFConfig cfg2 e2 ->
  Config.Refs.Partition cfg cfg1 cfg2 ->
  WFConfig cfg (LetPair x1 x2 e1 e2)

| QRMeas : forall e cfg,
  WFConfig cfg e ->
  WFConfig cfg (Meas e)

| QRNew : forall e cfg,
  WFConfig cfg e ->
  WFConfig cfg (New e)

| QRUnitary : forall u e cfg,
  WFConfig cfg e ->
  WFConfig cfg (Unitary u e)

| QRLambda : forall x e cfg,
  WFConfig cfg e ->
  WFConfig cfg (Lambda x e)

| QRFix : forall f x e cfg,
  WFConfig cfg e ->
  WFConfig cfg (Fix f x e)

| QRApp : forall e1 e2 cfg cfg1 cfg2,
  WFConfig cfg1 e1 ->
  WFConfig cfg2 e2 ->
  Config.Refs.Partition cfg cfg1 cfg2 ->
  WFConfig cfg (App e1 e2)
.

*)
  


(*********)
(* Types *)
(*********)

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


(* Typing judgment: Γ; Δ ⊢ t : τ 
 *  Γ : a finite map of non-linear variables to types
 *  Δ : a finite map of linear variables to types
 *)
Inductive WellTyped : Var.Map.t typ -> Var.Map.t typ -> Expr.t -> typ -> Prop :=

| WTQVar : forall Γ Δ x τ,
  Var.Singleton x τ Δ ->
  WellTyped Γ Δ (Var x) τ

| WTCVar : forall Γ Δ x τ,
  Var.Map.Empty Δ ->
  Var.Map.MapsTo x τ Γ ->
  WellTyped Γ Δ (Var x) τ

| WTLetIn : forall τ Δ1 Δ2 Γ Δ x e1 e2 τ',
  WellTyped Γ Δ1 e1 τ ->

  WellTyped Γ (Var.Map.add x τ Δ2) e2 τ' ->
  
  Var.MapFacts.Partition Δ Δ1 Δ2 ->
  ~ Var.Map.In x Δ2 ->

  WellTyped Γ Δ (LetIn x e1 e2) τ'

| WTBang : forall Γ Δ e τ,
  Var.Map.Empty Δ ->
  WellTyped Γ Δ e τ ->
  WellTyped Γ Δ (Bang e) (BANG τ)

| WTLetBang : forall τ Δ1 Δ2 Γ Δ x e1 e2 τ',
  WellTyped Γ Δ1 e1 (BANG τ) ->
  WellTyped (Var.Map.add x τ Γ) Δ2 e2 τ' ->

  Var.MapFacts.Partition Δ Δ1 Δ2 ->

  WellTyped Γ Δ (LetBang x e1 e2) τ'

| WTBit : forall Γ Δ b,
  Var.Map.Empty Δ ->
  WellTyped Γ Δ (Bit b) BIT

| WTIf : forall Δ' Δ'' Γ Δ e e1 e2 τ,

  WellTyped Γ Δ' e BIT ->
  WellTyped Γ Δ'' e1 τ ->
  WellTyped Γ Δ'' e2 τ ->

  Var.MapFacts.Partition Δ Δ' Δ'' ->

  WellTyped Γ Δ (If e e1 e2) τ

| WTPair : forall Δ1 Δ2 Γ Δ e1 e2 τ1 τ2,
  WellTyped Γ Δ1 e1 τ1 ->
  WellTyped Γ Δ2 e2 τ2 ->

  Var.MapFacts.Partition Δ Δ1 Δ2 ->

  WellTyped Γ Δ (Pair e1 e2) (Tensor τ1 τ2)

| WTLetPair : forall τ1 τ2 Δ1 Δ2 Γ Δ x1 x2 e e' τ',

  WellTyped Γ Δ1 e (Tensor τ1 τ2) ->
  WellTyped Γ (Var.Map.add x1 τ1 (Var.Map.add x2 τ2 Δ2)) e' τ' ->
  
  Var.MapFacts.Partition Δ Δ1 Δ2 ->
  ~ Var.Map.In x1 Δ2 ->
  ~ Var.Map.In x2 Δ2 ->
  x1 <> x2 ->

  WellTyped Γ Δ (LetPair x1 x2 e e') τ'

| WTMeas : forall Γ Δ e,
  WellTyped Γ Δ e QUBIT ->
  WellTyped Γ Δ (Meas e) BIT

(*
| WTQRef : forall Γ Δ q,
  Var.Map.Empty Δ ->
  WellTyped Γ Δ (QRef q) QUBIT
*)

| WTNew : forall Γ Δ e,
  WellTyped Γ Δ e BIT ->
  WellTyped Γ Δ (New e) QUBIT

| WTUnitary : forall Γ Δ U e τ,
  type_of_unitary U = τ ->
  WellTyped Γ Δ e τ ->
  WellTyped Γ Δ (Unitary U e) τ

| WTLambda : forall Γ Δ x e τ1 τ2,
  ~ Var.Map.In x Δ ->
  WellTyped Γ (Var.Map.add x τ1 Δ) e τ2 ->
  WellTyped Γ Δ (Lambda x e) (Lolli τ1 τ2)

| WTFix : forall Γ Δ f x e τ1 τ2,

  Var.Map.Empty Δ ->
  ~ Var.V.eq f x ->
  WellTyped (Var.Map.add f (Lolli τ1 τ2) (Var.Map.add x τ1 Γ)) Δ e τ2 ->

  WellTyped Γ Δ (Fix f x e) (Lolli (BANG τ1) τ2)
.

Hint Constructors WellTyped : qoreo_db.

Definition WellTypedConfig (refs : Var.Map.t nat) e tau : Prop :=
  WellTyped (Var.Map.empty _) (Var.Map.map (fun _ => QUBIT) refs) e tau.


(* TODO: The stronger statement would be 
to define alpha equivalence for Expr.tessions
and then to prove this with respect to
    Var.Map.Equiv alpha_equiv
*)
Lemma WellTyped_context_equal :
  forall Γ Δ e τ,
    WellTyped Γ Δ e τ ->
  forall Γ' Δ',
    Var.Map.Equal Γ Γ' ->
    Var.Map.Equal Δ Δ' ->
    WellTyped Γ' Δ' e τ.
Proof.
  intros Γ Δ e τ He.
  induction He; intros Γ' Δ0 HΓ HΔ;
    try (econstructor; eauto;
      try apply IHHe;
      try apply IHHe1;
      try apply IHHe2;
      try apply IHHe3;
      try rewrite <- HΔ;
      try rewrite <- HΓ;
      try reflexivity;
      auto; fail).
Qed.
    

Global Instance WellTypedProper : Proper (Var.Map.Equal ==> Var.Map.Equal ==> eq ==> eq ==> iff) WellTyped.
Proof.
  intros Γ1 Γ2 HΓ
    Δ1 Δ2 HΔ e1 e2 He
    τ1 τ2 Hτ; subst.
  split; intros; eapply WellTyped_context_equal; eauto.
  * rewrite HΓ; reflexivity.
  * rewrite HΔ; reflexivity. 
Qed.



(***************)
(* Type safety *)
(***************)

Lemma weakening_gen : forall Γ Δ e τ,
  WellTyped Γ Δ e τ ->
  forall Γ',
  (forall x τ, Var.Map.MapsTo x τ Γ -> Var.Map.MapsTo x τ Γ') ->
  WellTyped Γ' Δ e τ.
Proof.
  intros Γ Δ e τ HWT.
  induction HWT; intros Γ' Hsub;
    try (econstructor; eauto; fail).
  * eapply WTLetBang; eauto.
    apply IHHWT2.
    intros y σ Hy.
    autorewrite with var_db in *.
    destruct Hy as [[Heq Hmaps] | [Hneq Hmaps]].
    + left; auto.
    + right; split; auto.

  * eapply WTFix; eauto.
    apply IHHWT.
    intros y τ Hy.
    autorewrite with var_db in *.
    destruct Hy as [[Heqf Hmaps] | [Hneqf Hy]].
    + left; auto.
    + right; split; auto.
      destruct Hy as [[Heqx Hmaps] | [Hneqx Hmaps]].
      - left; auto.
      - right; split; auto.
Qed.

Lemma weakening : forall Γ Δ e τ,
  WellTyped (Var.Map.empty _) Δ e τ ->
  WellTyped Γ Δ e τ.
Proof.
  intros Γ Δ e τ HWT.
  eapply weakening_gen; eauto.
  intros x τ' Hmaps.
  exfalso.
  autorewrite with var_db in Hmaps.
  contradiction.
Qed.



Lemma wt_subst_bang : forall τ Γ Δ x v e τ',
  Val v ->
  WellTyped Γ (Var.Map.empty _) v (BANG τ) ->
  WellTyped (Var.Map.add x τ Γ) Δ e τ' ->
  WellTyped Γ Δ (subst x v e) τ'.
Proof.
Admitted.

Lemma wt_subst : forall Δ1 Δ2 τ Γ Δ' x v e τ',
  Val v ->
  WellTyped Γ Δ1 v τ ->
  WellTyped Γ (Var.Map.add x τ Δ2) e τ' ->
  Var.MapFacts.Partition Δ' Δ1 Δ2 ->
  WellTyped Γ Δ' (subst x v e) τ'.
Proof.
Admitted.

Lemma wt_subst2 : forall Δ1 Δ2 τ1 τ2 Γ Δ Δ' x1 v1 x2 v2 e τ',
  Val v1 ->
  Val v2 ->
  WellTyped Γ Δ1 v1 τ1 ->
  WellTyped Γ Δ2 v2 τ2 ->
  WellTyped Γ (Var.Map.add x1 τ1 (Var.Map.add x2 τ2 Δ')) e τ' ->
  Var.MapFacts.Disjoint Δ1 Δ2 ->
  Var.MapFacts.Partition Δ (Var.concat Δ1 Δ2) Δ' ->
  ~ Var.Map.In x1 Δ' ->
  ~ Var.Map.In x2 Δ' ->
  WellTyped Γ Δ (subst x2 v2 (subst x1 v1 e)) τ'.
Proof.
Admitted. 


Lemma step_weakening : forall e refs ρ e' refs' ρ',
  
  step e refs ρ e' refs' ρ' ->

  forall Γ refs1 refs2 τ,
  WellTyped Γ (Var.Map.map (fun _ => QUBIT) refs1) e τ ->
  Var.MapFacts.Partition refs refs1 refs2 ->
  exists refs1', 
    step e refs1 ρ e' refs1' ρ'
    /\
    Var.MapFacts.Partition refs' refs1' refs2.
Proof.
Admitted.


Ltac step_weakening_tac :=
  match goal with
  | [ Hstep : step ?e ?refs ?ρ ?e' ?refs' ?ρ',
      HTyped : WellTyped ?Γ ?Δ ?e ?τ
      |- _ ] =>
      let refs1 := fresh "refs1" in
      let Hstep1 := fresh "Hstep1" in
      let Hpart1 := fresh "Hpart1" in
      edestruct (step_weakening _ _ _ _ _ _ Hstep) as [refs1 [Hstep1 Hpart1]]; eauto
  end.



Lemma well_typed_qubit : forall {A} (refs : Var.Map.t A) q τ,
  WellTyped (Var.Map.empty typ) (Var.Map.map (fun _ => QUBIT) refs) (Var q) τ ->
  τ = QUBIT.
Proof.
    intros ? ? ? ? HWT.
    inversion HWT; subst; clear HWT.
    2:{ autorewrite with var_db in *. contradiction. }
    unfold Var.Singleton in *.
    specialize (H2 q).
    autorewrite with var_db in *.
    destruct (Var.Map.find q refs); inversion H2; auto.
Qed.

Lemma preservation : forall Γ Δ e τ,
  WellTyped Γ Δ e τ ->

  forall refs ρ e' refs' ρ' Δ',
  Var.Map.Empty Γ ->
  Var.Map.Equal Δ (Var.Map.map (fun _ => QUBIT) refs) ->
  
  step e refs ρ e' refs' ρ' ->
  Var.Map.Equal Δ' (Var.Map.map (fun _ => QUBIT) refs') ->
  
  WellTyped Γ Δ' e' τ.
Proof.
  intros ? ? ? ? HWT.
  induction HWT; intros ? ? ? ? ? ? Hempty HΔ Hstep HΔ';
    unfold Var.Singleton in *;
    try (rewrite HΔ in *; clear Δ HΔ);
    try (rewrite HΔ' in *; clear Δ' HΔ');
    try (inversion Hstep; auto; fail).
  *
    vsimpl.
    inversion Hstep; subst; clear Hstep.
    + (* e1 -> e1' *) 

      (* We are given: (e1,refs) ~> (e1',refs') *)
      (* By weakening, we know that (e1,refs1) ~> (e1',refs1') where refs'=refs1' + refs2 *)
      step_weakening_tac.

      (* So by the IH, Γ;refs1' |- e1' : τ *)
      eapply (IHHWT1) in Hstep1; eauto with var_db;
        try reflexivity.
      econstructor; eauto with var_db. 
      vsimpl; auto.

    + eapply wt_subst; eauto;
      autorewrite with var_db; auto.
      vsimpl; auto.

  * (* Let!*)
    vsimpl.
    inversion Hstep; subst; clear Hstep.
    + (* e1 -> e1' *) 

      (* We are given: (e1,refs) ~> (e1',refs') *)
      (* By weakening, we know that (e1,refs1) ~> (e1',refs1') where refs'=refs1' + refs2 *)
      step_weakening_tac.

      (* So by the IH, Γ;refs1' |- e1' : τ *)
      eapply IHHWT1 in Hstep1; eauto with var_db;
        try vsimpl;
        try reflexivity.
      econstructor; eauto.
      vsimpl; auto.

    + inversion HWT1; subst.
      vsimpl.
      autorewrite with var_db in *.

      eapply wt_subst_bang; eauto.
      { constructor. }

  * (* If *) 
    vsimpl.
    inversion Hstep; subst; clear Hstep.
    + (* e -> e1' *)
      step_weakening_tac.
      eapply (IHHWT1) in Hstep1; eauto with var_db;
        vsimpl;
        try reflexivity.
      econstructor; eauto.
      vsimpl; auto.

    + inversion HWT1; subst.
      vsimpl.
      destruct b; auto.
  * (* Pair *)
    vsimpl.
    inversion Hstep; subst; clear Hstep.
    + step_weakening_tac.
      eapply (IHHWT1) in Hstep1; eauto with var_db;
        vsimpl;
        try reflexivity.
      econstructor; eauto.
      vsimpl; auto.

    + apply Var.MapFacts.Partition_sym in Hpart.
      step_weakening_tac.
      apply Var.MapFacts.Partition_sym in Hpart1.
      eapply (IHHWT2) in Hstep1; eauto with var_db;
        vsimpl;
        try reflexivity.
      econstructor; eauto.
      vsimpl; auto.

  * (* LetPair *) 
    vsimpl.
    inversion Hstep; subst; clear Hstep.
    + (* e1 -> e1' *) 

      (* We are given: (e1,refs) ~> (e1',refs') *)
      (* By weakening, we know that (e1,refs1) ~> (e1',refs1') where refs'=refs1' + refs2 *)
      step_weakening_tac.

      (* So by the IH, Γ;refs1' |- e1' : τ *)
      eapply (IHHWT1) in Hstep1; eauto with var_db;
        try reflexivity.
      
      clear H (*duplicate*). clear H12 (* unnecessary *).

      econstructor; eauto; autorewrite with var_db.
      { vsimpl; auto. }

    + inversion HWT1; subst; clear HWT1.
      inversion H12; subst; clear H12.
      reflect_partition; auto.
      eapply wt_subst2; eauto.
      {
        reflect_partition; auto.
        ** eapply Var.Proofs.disjoint_map in Hdisj0.
           rewrite Heq in Hdisj0.
           auto.
        ** rewrite Heq; reflexivity.
      }

  * (* Meas *)
    vsimpl.
    inversion Hstep; subst; clear Hstep.
    + (* e1 -> e1' *) 

      (* We are given: (e1,refs) ~> (e1',refs') *)
      (* By weakening, we know that (e1,refs1) ~> (e1',refs1') where refs'=refs1' + refs2 *)
      step_weakening_tac.
      { apply Var.Proofs.partition_empty_r. }

      (* So by the IH, Γ;refs1' |- e1' : τ *)
      eapply (IHHWT) in Hstep1; eauto with var_db;
        try reflexivity.
      econstructor; eauto with var_db.
      vsimpl; auto.

    + econstructor; eauto.

        inversion H1; subst; clear H1.
        vsimpl.
        eapply Var.Proofs.singleton_remove; eauto.

  * (* New *)
    vsimpl.
    inversion Hstep; subst; clear Hstep.
    + (* e1 -> e1' *) 

      (* We are given: (e1,refs) ~> (e1',refs') *)
      (* By weakening, we know that (e1,refs1) ~> (e1',refs1') where refs'=refs1' + refs2 *)
      step_weakening_tac.
      { apply Var.Proofs.partition_empty_r. }

      (* So by the IH, Γ;refs1' |- e1' : τ *)
      eapply (IHHWT) in Hstep1; eauto with var_db;
        try reflexivity.
      econstructor; eauto with var_db.
      vsimpl; auto.

    + econstructor; eauto.
      inversion H0; subst; clear H0.
      inversion HWT; subst; clear HWT.
      unfold Var.Singleton.
      autorewrite with var_db.

      vsimpl.
      apply Var.MapFacts.F.add_m_Proper; auto.
      rewrite H2. autorewrite with var_db. reflexivity.

  * (* Unitary *)
    vsimpl.
    inversion Hstep; subst; clear Hstep.
    + (* e1 -> e1' *) 

      (* We are given: (e1,refs) ~> (e1',refs') *)
      (* By weakening, we know that (e1,refs1) ~> (e1',refs1') where refs'=refs1' + refs2 *)
      step_weakening_tac.
      { apply Var.Proofs.partition_empty_r. }

      (* So by the IH, Γ;refs1' |- e1' : τ *)
      eapply (IHHWT) in Hstep1; eauto with var_db;
        try reflexivity.
      econstructor; eauto with var_db.
      vsimpl; auto.

    + econstructor; eauto.
      unfold Var.Singleton in *.
      subst_map.

      replace (type_of_unitary U) with QUBIT in * by
        (symmetry; eapply well_typed_qubit; eauto).
      autorewrite with var_db.
      reflexivity.

    + inversion HWT; subst; auto.
      vsimpl.
      replace τ1 with QUBIT in * by
        (symmetry; eapply well_typed_qubit; eauto).
      replace τ2 with QUBIT in * by
        (symmetry; eapply well_typed_qubit; eauto).
      econstructor; eauto.
      {
        vsimpl; auto.
      }
Qed.

(*

Hint Rewrite Var.MapFacts.F.empty_mapsto_iff : var_db.
Theorem progress : forall e τ Γ Δ,
  WellTyped Γ Δ e τ ->
  forall cfg,
  Config.WellScoped cfg ->
  Var.Map.Empty Γ ->
  Var.Map.Empty Δ ->
  WellFormed (e, cfg) ->
  Val e \/ exists e' cfg', (e, cfg) ~> (e', cfg').
Proof.
  intros e τ Γ Δ Hwt.
  induction Hwt; intros cfg Hscoped HΓ HΔ Hwf.
  * contradict H.
    unfold Var.Singleton.
    vsimpl.
    admit (* lemma *).
  * exfalso. vsimpl.
    autorewrite with var_db in *; auto.
  * vsimpl.
    unfold WellFormed in 
  
  exfalso.
    apply (HΓ x τ); auto.
  * 
    
  

(*
Proof.
  intros n e τ cfg Hwt Hdim.
  eapply progress_gen; eauto;
    intros k v Hmap;
    apply Var.MapFacts.F.empty_mapsto_iff in Hmap;
    exact Hmap.
Qed.
*)
Abort.
*)