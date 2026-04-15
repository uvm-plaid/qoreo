From Stdlib Require Import FSets.FMapList FSets.FSetList FSets.FMapFacts OrderedType OrderedTypeEx.
From QuantumLib Require Import Matrix Pad Quantum.
From Qoreo Require Import Base.

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
(*| QRef : QRef.t -> t*)
| New : t -> t
| Unitary : unitary -> t -> t
| Lambda : Var.t -> t -> t
| Fix : Var.t -> Var.t -> t -> t
| App : t -> t -> t
.
Inductive Val : t -> Prop :=
(*| QRefVal : forall q, Val (QRef q)*)
| VarVal : forall x, Val x
| BangVal : forall e, Val (Bang e)
| BitVal  : forall b, Val (Bit b)
| PairVal : forall v1 v2, Val v1 -> Val v2 -> Val (Pair v1 v2)
| LambdaVal : forall x e, Val (Lambda x e)
| FixVal    : forall f x e, Val (Fix f x e)
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


Reserved Notation "cfg1 ~> cfg2" (at level 55).

Inductive step : Expr.t * Config.t -> Expr.t * Config.t -> Prop :=

(* Let *)
| LetC : forall x e1 e2 cfg e1' e2' cfg',
  step (e1, cfg) (e1', cfg') ->
  e2' = e2 ->
  (LetIn x e1 e2, cfg) ~> (LetIn x e1' e2', cfg')
| LetB : forall x e1 e2 cfg e2',
  Val e1 ->
  e2' = subst x e1 e2 ->
  (LetIn x e1 e2, cfg) ~> (e2', cfg)

(* Bang *)
(* no reduction under Bang *)

(* LetBang *)
| LetBangC : forall x e1 e2 cfg e1' cfg',
  (e1, cfg) ~> (e1', cfg') ->
  (LetBang x e1 e2, cfg) ~> (LetBang x e1' e2, cfg')
| LetBangB : forall x e1 e2 cfg e2',
  e2' = subst x (Bang e1) e2 ->
  (LetBang x (Bang e1) e2, cfg) ~> (e2', cfg)

(* If *)
| IfC : forall e e1 e2 cfg e' e1' e2' cfg',
  (e, cfg) ~> (e', cfg') ->
  e1' = e1 -> e2' = e2 ->
  (If e e1 e2, cfg) ~> (If e' e1' e2', cfg')
| IfB : forall (b : bool) e1 e2 cfg e' cfg',
  (if b then e' = e1 else e' = e2) ->
  cfg' = cfg ->
  (If (Bit b) e1 e2, cfg) ~> (e', cfg')


(* Pair *)
| PairC1 : forall e1 e2 cfg e1' e2' cfg',
  (e1, cfg) ~> (e1', cfg') ->
  e2' = e2 ->
  (Pair e1 e2, cfg) ~> (Pair e1' e2', cfg')
| PairC2 : forall e1 e2 cfg e1' e2' cfg',
  Val e1 -> e1' = e1 ->
  (e2, cfg) ~> (e2', cfg') ->
  (Pair e1 e2, cfg) ~> (Pair e1' e2', cfg')

(* LetPair *)
| LetPairC : forall x1 x2 e1 e2 cfg e1' e2' cfg',
  (e1, cfg) ~> (e1', cfg') ->
  e2' = e2 ->
  (LetPair x1 x2 e1 e2, cfg) ~> (LetPair x1 x2 e1' e2', cfg')
| LetPairB : forall x1 x2 v1 v2 e' cfg e'' cfg',
  Val v1 ->
  Val v2 ->
  e'' = subst x1 v1 (subst x2 v2 e') ->
  cfg' = cfg ->
  (LetPair x1 x2 (Pair v1 v2) e', cfg) ~> (e'', cfg')

| AppC1 : forall e1 e2 cfg e1' e2' cfg',
  (e1, cfg) ~> (e1', cfg') ->
  e2' = e2 ->
  (App e1 e2, cfg) ~> (App e1' e2', cfg')
| AppC2 : forall e1 e2 cfg e1' e2' cfg',
  Val e1 -> e1' = e1 ->
  (e2,cfg) ~> (e2', cfg') ->
  (App e1 e2, cfg) ~> (App e1' e2', cfg')
| AppB : forall x e v cfg e' cfg',
  Val v ->
  e' = subst x v e ->
  cfg' = cfg ->
  (App (Lambda x e) v, cfg) ~> (e', cfg')
| AppFixB : forall f x e v cfg e' cfg',
  Val v ->
  e' = subst x v (subst f (Fix f x e) e) ->
  cfg' = cfg ->
  (App (Fix f x e) v, cfg) ~> (e', cfg')

(* New *)
| NewC : forall e cfg e' cfg',
  (e, cfg) ~> (e', cfg') ->
  (New e, cfg) ~> (New e', cfg')
| New0 : forall b cfg x cfg',
  (x, cfg') = Config.new b cfg ->
  (New (Bit b), cfg) ~> (Var x, cfg')

(* Meas *)
| MeasC : forall e cfg e' cfg',
  (e, cfg) ~> (e',cfg') ->
  (Meas e, cfg) ~> (Meas e', cfg')
| MeasB : forall b x cfg cfg',
  cfg' = Config.measure b x cfg ->
  (Meas (Var x), cfg) ~> (Bit b, cfg')

(* Unitary *)
| UnitaryC : forall u e cfg e' cfg',
  (e, cfg) ~> (e', cfg') ->
  (Unitary u e, cfg) ~> (Unitary u e', cfg')
| UnitaryB1 : forall g q cfg cfg',
  cfg' = Config.apply_gate g [q] cfg ->
  (Unitary g (Var q), cfg) ~> (Var q, cfg')
| UnitaryB2 : forall g q1 q2 cfg cfg',
  cfg' = Config.apply_gate g [q1;q2] cfg ->
  (Unitary g (Pair (Var q1) (Var q2)), cfg) ~> (Pair (Var q1) (Var q2), cfg')

where "cfg1 '~>' cfg2" :=  (step cfg1 cfg2) : qoreo.

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

  WellTyped Γ Δ (LetPair x1 x2 e e') τ'

| WTMeas : forall Γ Δ e,
  WellTyped Γ Δ e QUBIT ->
  WellTyped Γ Δ (Meas e) (BANG BIT)

  (*
| WTQRef : forall Γ Δ q,
  (q < n)%nat ->
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
  * apply WTQVar.
    unfold Var.Singleton in *.
    rewrite <- HΔ; auto.
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

Lemma weakening_gen : forall Γ Δ e τ,
  WellTyped Γ Δ e τ ->
  forall Γ',
  (forall x τ, Var.Map.MapsTo x τ Γ -> Var.Map.MapsTo x τ Γ') ->
  WellTyped Γ' Δ e τ.
Proof.
  intros Γ Δ e τ HWT.
  induction HWT; intros Γ' Hsub.
  * apply WTQVar; auto.
  * apply WTCVar; auto.
  * eapply WTLetIn; eauto.
  * eapply WTBang; eauto.
  * eapply WTLetBang; eauto.
    apply IHHWT2.
    intros y σ Hy.
    apply Var.MapFacts.F.add_mapsto_iff.
    apply Var.MapFacts.F.add_mapsto_iff in Hy.
    destruct Hy as [[Heq Hmaps] | [Hneq Hmaps]].
    + left; auto.
    + right; split; auto.

  * eapply WTBit; eauto.
  * eapply WTIf; eauto.
  * eapply WTPair; eauto.
  * eapply WTLetPair; eauto.
  * eapply WTMeas; eauto.
  * eapply WTNew; eauto.
  * eapply WTUnitary; eauto.
  * eapply WTLambda; eauto.
  * eapply WTFix; eauto.
    apply IHHWT.
    intros y τ Hy.
    apply Var.MapFacts.F.add_mapsto_iff.
    apply Var.MapFacts.F.add_mapsto_iff in Hy.
    destruct Hy as [[Heqf Hmaps] | [Hneqf Hy]].
    + left; auto.
    + right; split; auto.
      apply Var.MapFacts.F.add_mapsto_iff.
      apply Var.MapFacts.F.add_mapsto_iff in Hy.
      destruct Hy as [[Heqx Hmaps] | [Hneqx Hmaps]].
      - left; auto.
      - right; split; auto.
Qed.


(***************)
(* Type safety *)
(***************)

Lemma weakening : forall Γ Δ e τ,
  WellTyped (Var.Map.empty _) Δ e τ ->
  WellTyped Γ Δ e τ.
Proof.
  intros Γ Δ e τ HWT.
  eapply weakening_gen; eauto.
  intros x τ' Hmaps.
  exfalso.
  apply Var.MapFacts.F.empty_mapsto_iff in Hmaps.
  exact Hmaps.
Qed.


(* If Δ(x0)=τ0 and Δ==Δ1,Δ2 and x ∉ Δ2 then Δ1(x0)=τ0 *)
Lemma partition_not_in_r : forall Δ Δ2 Δ1 x (τ : typ),
  Var.Map.MapsTo x τ Δ ->
  Var.MapFacts.Partition Δ Δ1 Δ2 ->
  ~ (Var.Map.In x Δ2) ->
  Var.Map.MapsTo x τ Δ1.
Proof.
  intros ? ? ? x τ Hx [Hdisjoint Hmapsto] Hnotin.
  apply Hmapsto in Hx.
  destruct Hx; auto.
  * contradict Hnotin.
    exists τ; auto.
Qed.

Lemma partition_remove : forall {A} x0 (Δ Δ1 Δ2 : Var.Map.t A),
  Var.MapFacts.Partition Δ Δ1 Δ2 ->
  Var.MapFacts.Partition (Var.Map.remove x0 Δ) (Var.Map.remove x0 Δ1) (Var.Map.remove x0 Δ2).
Proof.
  intros A x0 Δ Δ1 Δ2 [Hdisj Hiff].
  split.
  - (* Disjoint (remove x0 Δ1) (remove x0 Δ2) *)
    intros k [Hin1 Hin2].
    apply Var.MapFacts.F.remove_in_iff in Hin1.
    apply Var.MapFacts.F.remove_in_iff in Hin2.
    destruct Hin1 as [_ Hin1].
    destruct Hin2 as [_ Hin2].
    apply (Hdisj k); split; auto.
  - (* forall k e, MapsTo k e (remove x0 Δ) <-> MapsTo k e (remove x0 Δ1) \/ MapsTo k e (remove x0 Δ2) *)
    intros k e.
    rewrite Var.MapFacts.F.remove_mapsto_iff.
    rewrite Var.MapFacts.F.remove_mapsto_iff.
    rewrite Var.MapFacts.F.remove_mapsto_iff.
    firstorder.
Qed.


Lemma wt_subst : forall τ Γ Δ x v e τ',
  WellTyped Γ Δ e τ' ->
  Val v ->
  WellTyped (Var.Map.empty _) (Var.Map.empty _) v τ ->
  Var.Map.MapsTo x τ Δ ->
  WellTyped Γ (Var.Map.remove x Δ) (subst x v e) τ'.
Proof.
    intros τ Γ Δ x v e τ' HWT.
    revert τ x v.
    induction HWT; intros τ0 x0 v0 Hvalv0 HWTv0 Hindom;
      simpl.
    * unfold Var.Singleton in H.
      assert (Heq : x = x0 /\ τ = τ0).
      { rewrite H in Hindom.
          apply Var.MapFacts.F.add_mapsto_iff in Hindom.
          destruct Hindom as [ | [_ Hcontra]]; auto.
          apply Var.MapFacts.F.empty_mapsto_iff in Hcontra; contradiction.
      }
      destruct Heq; subst.
      rewrite Var.eq_dec_refl.
      rewrite H.
      rewrite Var.remove_add_eq.
      rewrite Var.remove_empty.
      apply weakening; auto.

    * contradict Hindom; apply H.

    *
      rewrite (Var.partition_concat _ Δ Δ1 Δ2); auto.
      
      assert (Hmapsto :
              (Var.Map.MapsTo x0 τ0 Δ1 /\ ~ Var.Map.In x0 Δ2)
            \/ (Var.Map.MapsTo x0 τ0 Δ2 /\ ~ Var.Map.In x0 Δ1)).
      {
        destruct H as [Hdisj Hiff].
        apply Hiff in Hindom.
        destruct Hindom; [left | right]; split; auto.
        { intros Hin.
          apply (Hdisj x0).
          split; auto. eexists; eauto.
        }
        {
          intros Hin.
          apply (Hdisj x0).
          split; auto. eexists; eauto.
        }
      }
      admit. (*
      destruct (Var.eq_dec x0 x) eqn:Heq.
      ** subst.
        apply (WTLetIn τ (Var.Map.remove x Δ1) (Var.Map.remove x Δ2)); auto.
        + eapply IHHWT1; eauto.
          eapply partition_not_in_r; eauto.
        + setoid_replace (Var.Map.add x τ (Var.Map.remove x Δ2)) with (Var.Map.add x τ Δ2); auto.
          { admit (* add x0 τ (remove x0 Δ2) = add x0 τ Δ2 *). }
        + apply partition_remove; auto.
        + apply Var.Map.remove_1; auto.
      **
        destruct H0 as [Hdisj Hiff].
        apply Hiff in Hindom.
      
    apply (WTLetIn τ (Var.Map.remove x0 Δ1) (Var.Map.remove x0 Δ2)); auto.
        + admit (*?*).
          (* eapply IHHWT1; eauto.
          eapply partition_not_in_r; eauto.*)
        + setoid_replace (Var.Map.add x τ (Var.Map.remove x0 Δ2)) with (Var.Map.remove x0 (Var.Map.add x τ Δ2)).
          2:{ admit. }
          eapply IHHWT2; eauto.
          admit (*?*)
        +
        +

         *)
        

    * simpl; econstructor; eauto.
      admit (* lemma *).
    * (*let!*) admit.
    * contradict Hindom.
      apply H.
    * (* if *)  admit.
    * (* Pair *)  admit.
    * (* LetPair *) admit.
    * (* Measure *) admit.
    * (* new *) econstructor; eauto.
    * (* Unitary *) econstructor; eauto.
    * (* Lambda *) admit.
    * (* Fix *) admit.
Admitted. 


Definition cfg_to_ctx (cfg : Config.t) :=
  Var.Map.map (fun _ => QUBIT) (Config.qrefs cfg).


Theorem preservation : forall e cfg e' cfg',
  (e, cfg) ~> (e',cfg') ->
  forall τ Δ Δ',
  Δ = cfg_to_ctx cfg ->
  Δ' = cfg_to_ctx cfg' ->
  WellTyped (Var.Map.empty _) Δ e τ ->
  WellTyped (Var.Map.empty _) Δ' e' τ.
Proof.
  intros e cfg e' cfg' step.
  remember (e,cfg) as CFG eqn:HCFG.
  remember (e',cfg') as CFG' eqn:HCFG'.
  revert e cfg e' cfg' HCFG HCFG'.
  induction step; intros ? ? ? ? HCFG HCFG' τ Δ Δ' HΔ HΔ' Hwt;   
    inversion HCFG; inversion HCFG'; subst;
    clear HCFG; clear HCFG'.
  * inversion Hwt; subst; clear Hwt.
    (* Δ1 = Var.Map.empty and Δ2 = Var.Map.empty *)
    admit.
  * (*apply wt_subst. *) admit.
  *
Admitted. 



Lemma empty_map_equal : forall {A} (m : Var.Map.t A),
  Var.Map.Empty m -> Var.Map.Equal m (Var.Map.empty A).
Proof.
  intros A m Hempty k.
  destruct (Var.Map.find k m) eqn:Hfind.
  - apply Var.Map.find_2 in Hfind. exfalso. eapply Hempty; eauto.
  - destruct (Var.Map.find k (Var.Map.empty A)) eqn:Hfind'.
    + apply Var.Map.find_2 in Hfind'.
      apply Var.MapFacts.F.empty_mapsto_iff in Hfind'. contradiction.
    + reflexivity.
Qed.

Lemma partition_of_empty : forall {A} (Δ1 Δ2 : Var.Map.t A),
  Var.MapFacts.Partition (Var.Map.empty A) Δ1 Δ2 ->
  Var.Map.Empty Δ1 /\ Var.Map.Empty Δ2.
Proof.
  intros A Δ1 Δ2 [Hdisj Hiff].
  split; intros k v Hmap.
  - assert (H : Var.Map.MapsTo k v (Var.Map.empty A)).
    { apply Hiff. left; auto. }
    apply Var.MapFacts.F.empty_mapsto_iff in H. exact H.
  - assert (H : Var.Map.MapsTo k v (Var.Map.empty A)).
    { apply Hiff. right; auto. }
    apply Var.MapFacts.F.empty_mapsto_iff in H. exact H.
Qed.

Lemma empty_partition_empty : forall {A} (Δ Δ1 Δ2 : Var.Map.t A),
  Var.Map.Empty Δ ->
  Var.MapFacts.Partition Δ Δ1 Δ2 ->
  Var.Map.Empty Δ1 /\ Var.Map.Empty Δ2.
Proof.
  intros A Δ Δ1 Δ2 Hempty Hpart.
  apply empty_map_equal in Hempty.
  rewrite Hempty in Hpart.
  apply partition_of_empty. auto.
Qed.

(*
Lemma canonical_bit : forall Γ Δ e,
  Val e -> WellTyped Γ Δ e BIT -> exists b, e = Bit b.
Proof.
  intros Γ Δ e Hval Hwt.
  inversion Hval.
  inversion Hval; subst; inversion Hwt; subst; try discriminate.
  exists b. reflexivity.
Qed.

Lemma canonical_bang : forall n Γ Δ e τ,
  Val e -> WellTyped n Γ Δ e (BANG τ) -> exists e', e = Bang e'.
Proof.
  intros n Γ Δ e τ Hval Hwt.
  inversion Hval; subst; inversion Hwt; subst; try discriminate.
  exists e0. reflexivity.
Qed.

Lemma canonical_qubit : forall n Γ Δ e,
  Val e -> WellTyped n Γ Δ e QUBIT -> exists q, e = QRef q.
Proof.
  intros n Γ Δ e Hval Hwt.
  inversion Hval; subst; inversion Hwt; subst; try discriminate.
  exists q. reflexivity.
Qed.

Lemma canonical_tensor : forall n Γ Δ e τ1 τ2,
  Val e -> WellTyped n Γ Δ e (Tensor τ1 τ2) ->
  exists v1 v2, e = Pair v1 v2 /\ Val v1 /\ Val v2.
Proof.
  intros n Γ Δ e τ1 τ2 Hval Hwt.
  inversion Hval; subst; inversion Hwt; subst; try discriminate.
  exists v1, v2. auto.
Qed.

Lemma canonical_tensor_qubit : forall n Γ Δ e,
  Val e -> WellTyped n Γ Δ e (Tensor QUBIT QUBIT) ->
  exists q1 q2, e = Pair (QRef q1) (QRef q2).
Proof.
  intros n Γ Δ e Hval Hwt.
  destruct (canonical_tensor _ _ _ _ _ _ Hval Hwt) as [v1 [v2 [Heq [Hv1 Hv2]]]].
  subst.
  inversion Hwt; subst.
  match goal with
  | [ Hwt1 : WellTyped _ _ _ v1 QUBIT,
      Hwt2 : WellTyped _ _ _ v2 QUBIT |- _ ] =>
    destruct (canonical_qubit _ _ _ _ Hv1 Hwt1) as [q1 Hq1];
    destruct (canonical_qubit _ _ _ _ Hv2 Hwt2) as [q2 Hq2];
    subst; exists q1, q2; reflexivity
  end.
Qed.

Lemma progress_gen : forall n Γ Δ e τ,
  WellTyped n Γ Δ e τ ->
  Var.Map.Empty Γ ->
  Var.Map.Empty Δ ->
  forall cfg, Config.dim cfg = n ->
  Val e \/ exists e' cfg', (e, cfg) ~> (e', cfg').
Proof.
  intros n Γ Δ e τ Hwt.
  induction Hwt; intros HempΓ HempΔ cfg Hdim.

  - (* WTQVar *)
    exfalso.
    unfold Var.Singleton in H.
    assert (Hm : Var.Map.MapsTo x τ (Var.Map.add x τ (Var.Map.empty typ))).
    { apply Var.Map.add_1. reflexivity. }
    rewrite <- H in Hm.
    eapply HempΔ; eauto.

  - (* WTCVar *)
    exfalso. eapply HempΓ; eauto.

  - (* WTLetIn *)
    right.
    destruct (empty_partition_empty _ _ _ HempΔ H) as [HΔ1 HΔ2].
    specialize (IHHwt1 HempΓ HΔ1 cfg Hdim).
    destruct IHHwt1 as [Hval | [e1' [cfg' Hstep]]].
    + exists (subst x e1 e2), cfg.
      apply LetB; auto.
    + exists (LetIn x e1' e2), cfg'.
      eapply LetC; eauto.

  - (* WTBang *)
    left. constructor.

  - (* WTLetBang *)
    right.
    destruct (empty_partition_empty _ _ _ HempΔ H) as [HΔ1 HΔ2].
    specialize (IHHwt1 HempΓ HΔ1 cfg Hdim).
    destruct IHHwt1 as [Hval | [e1' [cfg' Hstep]]].
    + destruct (canonical_bang _ _ _ _ _ Hval Hwt1) as [e' He']. subst.
      exists (subst x (Bang e') e2), cfg.
      apply LetBangB. reflexivity.
    + exists (LetBang x e1' e2), cfg'.
      apply LetBangC. auto.

  - (* WTBit *)
    left. constructor.

  - (* WTIf *)
    right.
    destruct (empty_partition_empty _ _ _ HempΔ H) as [HΔ' HΔ''].
    specialize (IHHwt1 HempΓ HΔ' cfg Hdim).
    destruct IHHwt1 as [Hval | [e' [cfg' Hstep]]].
    + destruct (canonical_bit _ _ _ _ Hval Hwt1) as [b Hb]. subst.
      destruct b.
      * exists e1, cfg. apply IfB; auto.
      * exists e2, cfg. apply IfB; auto.
    + exists (If e' e1 e2), cfg'.
      eapply IfC; eauto.

  - (* WTPair *)
    destruct (empty_partition_empty _ _ _ HempΔ H) as [HΔ1 HΔ2].
    specialize (IHHwt1 HempΓ HΔ1 cfg Hdim).
    specialize (IHHwt2 HempΓ HΔ2 cfg Hdim).
    destruct IHHwt1 as [Hval1 | [e1' [cfg' Hstep1]]].
    + destruct IHHwt2 as [Hval2 | [e2' [cfg' Hstep2]]].
      * left. constructor; auto.
      * right. exists (Pair e1 e2'), cfg'.
        eapply PairC2; eauto.
    + right. exists (Pair e1' e2), cfg'.
      eapply PairC1; eauto.

  - (* WTLetPair *)
    right.
    destruct (empty_partition_empty _ _ _ HempΔ H) as [HΔ1 HΔ2].
    specialize (IHHwt1 HempΓ HΔ1 cfg Hdim).
    destruct IHHwt1 as [Hval | [e'' [cfg' Hstep]]].
    + destruct (canonical_tensor _ _ _ _ _ _ Hval Hwt1) as [v1 [v2 [Heq [Hv1 Hv2]]]]. subst.
      exists (subst x1 v1 (subst x2 v2 e')), cfg.
      apply LetPairB; auto.
    + exists (LetPair x1 x2 e'' e'), cfg'.
      eapply LetPairC; eauto.

  - (* WTMeas *)
    right.
    specialize (IHHwt HempΓ HempΔ cfg Hdim).
    destruct IHHwt as [Hval | [e' [cfg' Hstep]]].
    + destruct (canonical_qubit _ _ _ _ Hval Hwt) as [q Hq]. subst.
      exists (Bit true), (Config.measure true q cfg).
      apply MeasB. reflexivity.
    + exists (Meas e'), cfg'.
      apply MeasC. auto.

  - (* WTQRef *)
    left. constructor.

  - (* WTNew *)
    right.
    specialize (IHHwt HempΓ HempΔ cfg Hdim).
    destruct IHHwt as [Hval | [e' [cfg' Hstep]]].
    + destruct (canonical_bit _ _ _ _ Hval Hwt) as [b Hb]. subst.
      destruct (Config.new b cfg) as [i cfg'] eqn:Hnew.
      exists (QRef i), cfg'.
      apply New0. rewrite Hnew. reflexivity.
    + exists (New e'), cfg'.
      apply NewC. auto.

  - (* WTUnitary *)
    right.
    specialize (IHHwt HempΓ HempΔ cfg Hdim).
    destruct IHHwt as [Hval | [e' [cfg' Hstep]]].
    + destruct U; simpl in H; subst.
      1-4,6-9: (
        destruct (canonical_qubit _ _ _ _ Hval Hwt) as [q Hq]; subst;
        eexists; eexists;
        apply UnitaryB1; reflexivity
      ).
      (* CNOT *)
      destruct (canonical_tensor_qubit _ _ _ _ Hval Hwt) as [q1 [q2 Hq]]. subst.
      eexists; eexists.
      apply UnitaryB2. reflexivity.
    + exists (Unitary U e'), cfg'.
      apply UnitaryC. auto.

  - (* WTLambda *)
    left. constructor.

  - (* WTFix *)
    left. constructor.
Qed.
*)

Theorem progress : forall e τ cfg Γ Δ,
  Config.WellScoped cfg ->
  Var.Map.Equal Δ (cfg_to_ctx cfg) ->
  Var.Map.Empty Γ ->
  WellTyped Γ Δ e τ ->
  Val e \/ exists e' cfg', (e, cfg) ~> (e', cfg').
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