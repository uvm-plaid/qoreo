From Stdlib Require Import FSets.FMapList FSets.FSetList FSets.FMapFacts OrderedType OrderedTypeEx.
From QuantumLib Require Import Matrix Pad Quantum.
From Qoreo Require Import Base.
Import Base.Tactics.

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
| WFQRef : forall refs x q,
  Var.Singleton x q refs ->
  WFRefs refs (QRef x)
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


Inductive Val : Var.Map.t nat -> t -> Prop :=
| QRefVal : forall refs q i,
  Var.Singleton q i refs ->
  Val refs (QRef q)
(*| VarVal : forall x, Val x*)
| BangVal : forall refs e,
  WFRefs refs e ->
  Val refs (Bang e)
| BitVal  : forall refs b,
  Var.Map.Empty refs ->
  Val refs (Bit b)
| PairVal : forall refs1 refs2 refs v1 v2,
  Val refs1 v1 -> Val refs2 v2 ->
  Var.MapFacts.Partition refs refs1 refs2 ->
  Val refs (Pair v1 v2)
| LambdaVal : forall refs x e,
  WFRefs refs e ->
  Val refs (Lambda x e)
| FixVal    : forall refs f x e,
  WFRefs refs e ->
  Val refs (Fix f x e)
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



Inductive step : Expr.t -> Var.Map.t nat -> Config.t -> Expr.t -> Var.Map.t nat -> Config.t -> Prop :=

(* Let *)
| LetC :
  forall refs1 refs1' refs2,
  forall x e1 e2 refs cfg e1' refs' cfg',
  
  step e1 refs1 cfg e1' refs1' cfg' ->

  WFRefs refs1 e1 ->
  WFRefs refs2 e2 ->
  Var.MapFacts.Partition refs refs1 refs2 ->
  Var.MapFacts.Partition refs' refs1' refs2 ->

  step (LetIn x e1 e2) refs cfg (LetIn x e1' e2) refs' cfg'

| LetB : forall refs1 refs2 x v1 e2 refs cfg e2',
  Val refs1 v1 ->
  e2' = subst x v1 e2 ->

  WFRefs refs2 e2 ->
  Var.MapFacts.Partition refs refs1 refs2 ->

  step (LetIn x v1 e2) refs cfg e2' refs cfg

(* Bang *)
(* no reduction under Bang *)

(* LetBang *)
| LetBangC :
  forall refs1 refs1' refs2,
  forall x e1 e2 refs cfg e1' refs' cfg',

  step e1 refs1 cfg e1' refs1' cfg' ->

  WFRefs refs2 e2 ->
  Var.MapFacts.Partition refs refs1 refs2 ->
  Var.MapFacts.Partition refs' refs1' refs2 ->

  step (LetBang x e1  e2) refs cfg
       (LetBang x e1' e2) refs' cfg'

| LetBangB : forall refs1 refs2 x e1 e2 refs cfg e2',
  e2' = subst x (Bang e1) e2 ->
  
  WFRefs refs1 e1 ->
  WFRefs refs2 e2 ->
  Var.MapFacts.Partition refs refs1 refs2 ->

  step (LetBang x (Bang e1) e2) refs cfg
       e2' refs cfg

(* If *)
| IfC : forall refs1 refs1' refs2,
  forall e1 e2 e3 refs cfg e1' refs' cfg',
  step e1 refs1 cfg e1' refs1' cfg' ->

  WFRefs refs2 e2 ->
  WFRefs refs2 e3 ->
  Var.MapFacts.Partition refs refs1 refs2 ->
  Var.MapFacts.Partition refs' refs1' refs2 ->

  step (If e1  e2 e3) refs cfg
       (If e1' e2 e3) refs' cfg'
  

| IfB : forall (b : bool) e2 e3 refs cfg e',

  (e' = if b then e2 else e3) ->
  WFRefs refs e2 ->
  WFRefs refs e3 ->
  
  step (If (Bit b) e2 e3) refs cfg
       e' refs cfg

(* Pair *)
| PairC1 : forall refs1 refs2 refs1',
  forall e1 e2 refs cfg e1' refs' cfg',
  step e1 refs1 cfg e1' refs1' cfg' ->

  WFRefs refs2 e2 ->
  Var.MapFacts.Partition refs refs1 refs2 ->
  Var.MapFacts.Partition refs' refs1' refs2 ->

  step (Pair e1 e2) refs cfg (Pair e1' e2) refs' cfg'

| PairC2 : forall refs1 refs2 refs2',
  forall e1 e2 refs cfg e2' refs' cfg',

  Val refs1 e1 ->
  step e2 refs2 cfg e2' refs2' cfg' ->

  Var.MapFacts.Partition refs refs1 refs2 ->
  Var.MapFacts.Partition refs' refs1 refs2' ->

  step (Pair e1 e2) refs cfg (Pair e1 e2') refs' cfg'

(* LetPair *)
| LetPairC : forall refs1 refs2 refs1',
  forall x1 x2 e1 e2 refs cfg e1' refs' cfg',

  step e1 refs1 cfg e1' refs1' cfg' ->
  WFRefs refs2 e2 ->

  Var.MapFacts.Partition refs refs1 refs2 ->
  Var.MapFacts.Partition refs' refs1' refs2 ->

  step (LetPair x1 x2 e1 e2) refs cfg
       (LetPair x1 x2 e1' e2) refs' cfg'

| LetPairB : forall refs1 refs2 x1 x2 v1 v2 e' refs cfg e'',
  Val refs1 (Pair v1 v2) ->
  WFRefs refs2 e' ->
  e'' = subst x1 v1 (subst x2 v2 e') ->

  Var.MapFacts.Partition refs refs1 refs2 ->

  step (LetPair x1 x2 (Pair v1 v2) e') refs cfg 
        e'' refs cfg

| AppC1 : forall refs1 refs2 refs1',
  forall e1 e2 refs cfg e1' refs' cfg',

  step e1 refs1 cfg e1' refs1' cfg' ->
  WFRefs refs2 e2 ->

  Var.MapFacts.Partition refs refs1 refs2 ->
  Var.MapFacts.Partition refs' refs1' refs2 ->

  step (App e1 e2) refs cfg
        (App e1' e2) refs' cfg'

| AppC2 : forall refs1 refs2 refs2',
  forall e1 e2 refs cfg e2' refs' cfg',

  Val refs1 e1 ->
  step e2 refs2 cfg e2' refs2' cfg' ->

  Var.MapFacts.Partition refs refs1 refs2 ->
  Var.MapFacts.Partition refs' refs1 refs2' ->

  step (App e1 e2) refs cfg
        (App e1 e2') refs' cfg'

| AppB : forall refs1 refs2 x e v refs cfg e',
  WFRefs refs1 e ->
  Val refs2 v ->
  e' = subst x v e ->
  Var.MapFacts.Partition refs refs1 refs2 ->

  step (App (Lambda x e) v) refs cfg
        e' refs cfg

| AppFixB : forall refs1 refs2 f x e v refs cfg e',

  WFRefs refs1 e ->
  Val refs2 v ->
  e' = subst x v (subst f (Fix f x e) e) ->

  Var.MapFacts.Partition refs refs1 refs2 ->

  step (App (Fix f x e) v) refs cfg e' refs cfg


(* New *)
| NewC : forall e refs cfg e' refs' cfg',

  step e refs cfg e' refs' cfg' ->

  step (New e) refs cfg (New e') refs' cfg'

| New0 : forall b refs cfg x refs' cfg',

  Var.Map.Empty refs ->
  (x, refs', cfg') = Config.new b refs cfg ->

  step (New (Bit b)) refs cfg
        (QRef x) refs' cfg'

(* Meas *)
| MeasC : forall e refs cfg e' refs' cfg',

  step e refs cfg e' refs' cfg' ->

  step (Meas e)  refs  cfg
       (Meas e') refs' cfg'

| MeasB : forall i b x refs cfg refs' cfg',
  Var.Singleton x i refs ->
  (refs', cfg') = Config.measure b x refs cfg ->

  step (Meas (QRef x)) refs cfg (Bang (Bit b)) refs' cfg'


(* Unitary *)
| UnitaryC : forall u e refs cfg e' refs' cfg',

  step e refs cfg e' refs' cfg' ->

  step (Unitary u e) refs cfg
       (Unitary u e') refs' cfg'

| UnitaryB1 : forall i g q refs cfg cfg',
  Var.Singleton q i refs ->
  cfg' = Config.apply_gate g [q] refs cfg ->

  step (Unitary g (QRef q)) refs cfg
       (QRef q) refs cfg'

| UnitaryB2 : forall i1 i2 g q1 q2 refs cfg cfg',
  Var.Map.Equal refs (Var.Map.add q1 i1 (Var.Map.add q2 i2 (Var.Map.empty _))) ->
  cfg' = Config.apply_gate g [q1;q2] refs cfg ->

  step (Unitary g (Pair (QRef q1) (QRef q2))) refs cfg
       (Pair (QRef q1) (QRef q2)) refs cfg'
.

Lemma wfrefs_val : forall refs v,
  Val refs v ->
  WFRefs refs v.
Proof.
  intros ? ? Hval.
  induction Hval; econstructor; eauto.
Qed.
Hint Resolve wfrefs_val : qoreo_db.
Hint Constructors WFRefs : qoreo_db.

Lemma partition_empty_l : forall A m,
  Var.MapFacts.Partition m (Var.Map.empty A) m.
Admitted.
Lemma partition_empty_r : forall A m,
  Var.MapFacts.Partition m m (Var.Map.empty A).
Admitted.
Lemma singleton_singleton : forall A x (a : A),
  Var.Singleton x a (Var.Map.add x a (Var.Map.empty _)).
Admitted.

Lemma partition_add_l : forall A x (a:A) m m1 m2,
  Var.MapFacts.Partition m m1 m2 ->
  Var.MapFacts.Partition (Var.Map.add x a m) (Var.Map.add x a m1) m2.
Admitted.
Lemma partition_add_r : forall A x (a:A) m m1 m2,
  Var.MapFacts.Partition m m1 m2 ->
  Var.MapFacts.Partition (Var.Map.add x a m) m1 (Var.Map.add x a m2).
Admitted.
Hint Resolve partition_empty_l partition_empty_r singleton_singleton : var_db.
Hint Resolve Var.Map.empty_1 partition_add_l partition_add_r : var_db.
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

Lemma partition_empty : forall {A},
  Var.MapFacts.Partition (Var.Map.empty A) (Var.Map.empty A) (Var.Map.empty A).
Admitted.
Lemma partition_empty1 : forall {A} (Δ1 Δ2 : Var.Map.t A),
  Var.MapFacts.Partition (Var.Map.empty _) Δ1 Δ2 ->
  Var.Map.Equal Δ1 (Var.Map.empty _).
Admitted.
Lemma partition_empty2 : forall {A} (Δ1 Δ2 : Var.Map.t A),
  Var.MapFacts.Partition (Var.Map.empty _) Δ1 Δ2 ->
  Var.Map.Equal Δ2 (Var.Map.empty _).
Admitted.
Ltac partition_empty :=
  repeat match goal with
  | [ H : Var.Map.Empty ?G |- _ ] =>
    rewrite (empty_map_equal G H) in *;
    clear H

  | [ H : Var.MapFacts.Partition (Var.Map.empty _) ?D1 ?D2 |- _ ] =>
    rewrite (partition_empty1 D1 D2 H) in *;
    rewrite (partition_empty2 D1 D2 H) in *;
    clear D1 D2 H
  | [ |- Var.MapFacts.Partition (Var.Map.empty _) _ _ ] =>
    apply Var.MapFacts.Partition_Empty
  | [ |- Var.Map.Empty (Var.Map.empty _) ] =>
    apply Var.Map.empty_1

  end.

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
      by (partition_empty; reflexivity).
    admit (* not sure why this isn't going through *).
    
  * inversion H0; subst; clear H0.
    constructor. constructor.
    unfold Var.Singleton in *.
    rewrite H.
    autorewrite with var_db.
    partition_empty.
  * econstructor.
    { econstructor. unfold Var.Singleton. reflexivity. }
    { econstructor. unfold Var.Singleton. reflexivity. }
    rewrite H. eauto with var_db.
  Unshelve.
  + apply Var.Map.empty.
  + apply Var.Map.empty.
  + exact 0%nat.
Admitted. 

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
  WellTyped Γ Δ (Meas e) (BANG BIT)

| WTQRef : forall Γ Δ q,
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
  autorewrite with var_db in Hmaps.
  contradiction.
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
    autorewrite with var_db in *.
    destruct Hin1 as [_ Hin1].
    destruct Hin2 as [_ Hin2].
    apply (Hdisj k); split; auto.
  - (* forall k e, MapsTo k e (remove x0 Δ) <-> MapsTo k e (remove x0 Δ1) \/ MapsTo k e (remove x0 Δ2) *)
    intros k e.
    autorewrite with var_db in *.
    firstorder.
Qed.

Lemma wt_subst_bang : forall τ Γ Γ' Δ x v e τ',
  WellTyped Γ Δ e τ' ->
  Val v ->
  WellTyped (Var.Map.empty _) (Var.Map.empty _) v (BANG τ) ->
  Var.Map.Equal Γ' (Var.Map.remove x Γ) ->
  WellTyped Γ' Δ (subst x v e) τ'.
Proof.
Admitted.

Lemma wt_subst : forall τ Γ Δ Δ' x v e τ',
  WellTyped Γ Δ e τ' ->
  Val v ->
  WellTyped Γ (Var.Map.empty _) v τ ->
  Var.Map.MapsTo x τ Δ ->
  Var.Map.Equal Δ' (Var.Map.remove x Δ) ->
  WellTyped Γ Δ' (subst x v e) τ'.
Proof.
    intros τ Γ Δ Δ' x v e τ' HWT.
    revert τ x v Δ'.
    induction HWT; intros τ0 x0 v0 Δ0' Hvalv0 HWTv0 Hindom Heq;
      rewrite Heq in *; clear Heq;
      simpl.
    * unfold Var.Singleton in H;
         rewrite H in *; clear H.
      assert (Heq : x = x0 /\ τ = τ0).
      { 
        autorewrite with var_db in Hindom.
        destruct Hindom as [ | [_ Hcontra]]; auto.
        contradiction.
      }
      destruct Heq; subst.
      autorewrite with var_db.
      auto.

    * contradict Hindom; apply H.

    *
      rewrite (Var.partition_concat _ Δ Δ1 Δ2); auto.
      
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
      admit.
      admit (* lemma *).
    * (*let!*) admit.
    * contradict Hindom.
      apply H.
    * (* if *)  admit.
    * (* Pair *)  admit.
    * (* LetPair *) admit.
    * (* Measure *) admit.
    * (* new *) econstructor; eauto.
      admit.
    * (* Unitary *) econstructor; eauto. admit.
    * (* Lambda *) admit.
    * (* Fix *) admit.
Admitted. 


Lemma fset_in_union : forall x X1 X2,
  Var.FSet.In x (Var.FSet.union X1 X2)
  <->
  Var.FSet.In x X1 \/ Var.FSet.In x X2.
Admitted.
Hint Rewrite fset_in_union : var_db.

Lemma wf_preservation : forall CFG CFG',
  CFG ~> CFG' ->
  WFConfig (snd CFG) (fst CFG) ->
  WFConfig (snd CFG') (fst CFG').
Proof.
  intros CFG CFG' Hstep.
  induction Hstep; inversion 1;
    simpl in *; subst;
    auto.
  * econstructor; eauto.
    eapply IHHstep; auto. 

  * specialize (HWF z).
    autorewrite with var_db in *.
   destruct Hin as [Hin | Hin]; auto.
    + apply IHHstep; auto.
  Qed.


Theorem preservation : forall e cfg e' cfg',
  (e, cfg) ~> (e',cfg') ->
  forall τ,
  WellTyped (Var.Map.empty _) (Var.Map.empty _) e τ ->
  
  WellTyped (Var.Map.empty _) (Var.Map.empty _) e' τ.
Proof.
  intros e cfg e' cfg' step.
  remember (e,cfg) as CFG eqn:HCFG.
  remember (e',cfg') as CFG' eqn:HCFG'.
  revert e cfg e' cfg' HCFG HCFG'.
  induction step; intros e0 cfg0 e0' cfg0' HCFG HCFG' τ Hwt;   
    inversion HCFG; inversion HCFG'; subst;
    clear HCFG; clear HCFG';
    inversion Hwt; subst; clear Hwt;
    try partition_empty;
    try (econstructor; eauto; try apply partition_empty; fail).
  * eapply wt_subst; eauto;
    autorewrite with var_db; auto.
    reflexivity.
  * eapply wt_subst_bang; eauto.
    { constructor. }
    { autorewrite with var_db. reflexivity. }
  * destruct b; subst; auto.
  * inversion H5; subst; clear H5.
    partition_empty.
    eapply wt_subst; eauto.
    eapply wt_subst; eauto.
    { autorewrite with var_db; auto. }
    { reflexivity. }
    { autorewrite with var_db; auto. }
    {
      rewrite Var.remove_add_neq; auto.
      autorewrite with var_db.
      reflexivity.
    }

  * econstructor; partition_empty.
  * repeat econstructor; try partition_empty.
  * inversion H5; subst. constructor. partition_empty.
  * inversion H5; subst.
    econstructor; eauto.
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
    partition_empty.
    admit (* lemma *).
  * exfalso. partition_empty.
    autorewrite with var_db in *; auto.
  * partition_empty.
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
