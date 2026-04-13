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
| QRef : qref -> t
| New : t -> t
| Unitary : unitary -> t -> t
| Lambda : Var.t -> t -> t
| Fix : Var.t -> Var.t -> t -> t
| App : t -> t -> t
.
Inductive Val : t -> Prop :=
| QRefVal : forall q, Val (QRef q)
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
| New0 : forall b cfg i cfg',
  (i, cfg') = Config.new b cfg ->
  (New (Bit b), cfg) ~> (QRef i, cfg')

(* Meas *)
| MeasC : forall e cfg e' cfg',
  (e, cfg) ~> (e',cfg') ->
  (Meas e, cfg) ~> (Meas e', cfg')
| MeasB : forall b q cfg cfg',
  cfg' = Config.measure b q cfg ->
  (Meas (QRef q), cfg) ~> (Bit b, cfg')

(* Unitary *)
| UnitaryC : forall u e cfg e' cfg',
  (e, cfg) ~> (e', cfg') ->
  (Unitary u e, cfg) ~> (Unitary u e', cfg')
| UnitaryB1 : forall g q cfg cfg',
  cfg' = Config.apply_gate g [q] cfg ->
  (Unitary g (QRef q), cfg) ~> (QRef q, cfg')
| UnitaryB2 : forall g q1 q2 cfg cfg',
  cfg' = Config.apply_gate g [q1;q2] cfg ->
  (Unitary g (Pair (QRef q1) (QRef q2)), cfg) ~> (Pair (QRef q1) (QRef q2), cfg')

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

(* Typing judgment: n; Γ; Δ ⊢ t : τ 
 * Here, n is maximum number of qubit references currently in scope
 *)
Inductive WellTyped {n : nat} : Var.Map.t typ -> Var.Map.t typ -> Expr.t -> typ -> Prop :=

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

| WTQRef : forall Γ Δ q,
  (q < n)%nat ->
  Var.Map.Empty Δ ->
  WellTyped Γ Δ (QRef q) QUBIT

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
Arguments WellTyped : clear implicits.

Hint Constructors WellTyped : qoreo_db.
(* TODO: The stronger statement would be 
to define alpha equivalence for Expr.tessions
and then to prove this with respect to
    Var.Map.Equiv alpha_equiv
*)
Lemma WellTyped_context_equal :
  forall n Γ Δ e τ,
    WellTyped n Γ Δ e τ ->
  forall Γ' Δ',
    Var.Map.Equal Γ Γ' ->
    Var.Map.Equal Δ Δ' ->
    WellTyped n Γ' Δ' e τ.
Proof.
  intros n Γ Δ e τ He.
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
    

Global Instance WellTypedProper : Proper ((@eq nat) ==> Var.Map.Equal ==> Var.Map.Equal ==> eq ==> eq ==> iff) WellTyped.
Proof.
  intros n1 n2 Hn Γ1 Γ2 HΓ
    Δ1 Δ2 HΔ e1 e2 He
    τ1 τ2 Hτ; subst.
  split; intros; eapply WellTyped_context_equal; eauto.
  * rewrite HΓ; reflexivity.
  * rewrite HΔ; reflexivity. 
Qed.

Lemma weakening_gen : forall n Γ Δ e τ,
  WellTyped n Γ Δ e τ ->
  forall Γ',
  (forall x τ, Var.Map.MapsTo x τ Γ -> Var.Map.MapsTo x τ Γ') ->
  WellTyped n Γ' Δ e τ.
Proof.
  intros n Γ Δ e τ HWT.
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
  * eapply WTQRef; eauto.
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

Lemma weakening : forall n Γ Δ e τ,
  WellTyped n (Var.Map.empty _) Δ e τ ->
  WellTyped n Γ Δ e τ.
Proof.
  intros n Γ Δ e τ HWT.
  eapply weakening_gen; eauto.
  intros x τ' Hmaps.
  exfalso.
  apply Var.MapFacts.F.empty_mapsto_iff in Hmaps.
  exact Hmaps.
Qed.

Lemma dim_weakening : forall n n' Γ Δ e τ,
  WellTyped n Γ Δ e τ ->
  (n <= n')%nat ->
  WellTyped n' Γ Δ e τ.
Proof.
  intros n n' Γ Δ e τ HWT Hle.
  induction HWT; try solve [econstructor; eauto].
  apply WTQRef; auto.
  lia.
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
Admitted.

Lemma wt_subst : forall τ n Γ Δ x v e τ',
  WellTyped n Γ Δ e τ' ->
  Val v ->
  WellTyped n (Var.Map.empty _) (Var.Map.empty _) v τ ->
  Var.Map.MapsTo x τ Δ ->
  WellTyped n Γ (Var.Map.remove x Δ) (subst x v e) τ'.
Proof.
    intros τ n Γ Δ x v e τ' HWT.
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
      destruct (Var.eq_dec x0 x0) as [Heq | Hneq].
      2:{ contradict Hneq. reflexivity. }
      setoid_replace (Var.Map.remove x0 Δ) with (Var.Map.empty typ).
      2:{
        rewrite H.
        apply Var.MapFacts.F.Equal_mapsto_iff;
          intros x τ.
        rewrite Var.MapFacts.F.remove_mapsto_iff.
        rewrite Var.MapFacts.F.add_mapsto_iff.
        split; [intros [? [[? ?] | [? ?]]] | inversion 1];
          auto;
          try contradiction.
      }
      apply weakening; auto.

    * contradict Hindom.
        apply (Var.MapFacts.elements_Empty Δ) in H.
        intros HMapsTo.
        apply Var.Map.elements_1 in HMapsTo.
        rewrite H in HMapsTo. 
        inversion HMapsTo.

    * 

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
    * contradict Hindom. admit.
    * (* if *)  admit.
    * (* Pair *)  admit.
    * (* LetPair *) admit.
    * (* Bang *) contradict Hindom. admit.
    * (* QRef *) (* Maybe our typing judgment should also have a list of qubit Var.tiables in scope... *) admit.
    * (* new *) econstructor; eauto.
    * (* Unitary *) econstructor; eauto.
    * (* Lambda *) admit.
    * (* Fix *) admit.
Admitted. 

Theorem preservation : forall e cfg e' cfg',
  (e, cfg) ~> (e',cfg') ->
  forall τ,
  WellTyped (Config.dim cfg) (Var.Map.empty _) (Var.Map.empty _) e τ ->
  WellTyped (Config.dim cfg') (Var.Map.empty _) (Var.Map.empty _) e' τ.
Proof.
  intros e cfg e' cfg' step.
  remember (e,cfg) as CFG eqn:HCFG.
  remember (e',cfg') as CFG' eqn:HCFG'.
  revert e cfg e' cfg' HCFG HCFG'.
  induction step; intros ? ? ? ? HCFG HCFG' τ Hwt;   
    inversion HCFG; inversion HCFG'; subst;
    clear HCFG; clear HCFG'.
  * inversion Hwt; subst; clear Hwt.
    (* Δ1 = Var.Map.empty and Δ2 = Var.Map.empty *)
    admit.
  * (*apply wt_subst. *) admit.
  *
Admitted. 



Theorem progress : forall n e τ cfg,
  WellTyped n (Var.Map.empty _) (Var.Map.empty _) e τ ->
  Config.dim cfg = n ->
  Val e \/ exists e' cfg', (e, cfg) ~> (e', cfg').
Admitted.
