From Stdlib Require Import FSets.FMapList FSets.FSetList FSets.FMapFacts OrderedType OrderedTypeEx.
From QuantumLib Require Import Matrix Pad.

Declare Scope qoreo.
Module Var.
  Module Export V := OrderedTypeEx.UOT_to_OT (OrderedTypeEx.Nat_as_OT).
  Definition t := V.t.
  
  Module Map := FSets.FMapList.Make(V).
  Module MapFacts := FMapFacts.Properties(Map).
  Module FSet := FSets.FSetList.Make(V).

  #[export] Existing Instance MapFacts.F.EqualSetoid.

  Definition domain {A} (m : Map.t A) : FSet.t :=
    let f := fun x _ s => FSet.add x s in
    Map.fold f m FSet.empty.

  Definition Singleton {A} x a (m : Map.t A) : Prop :=
    Map.Equal m (Map.add x a (Map.empty _)).

End Var.
Open Scope qoreo.


Definition var := Var.t.
Definition qref := nat.

Inductive unitary :=
| H | X | Y | Z | CNOT | Sgate | Sdag | Tgate | Tdag.

Inductive expr :=
| Var : var -> expr
| LetIn : var -> expr -> expr -> expr
| Bang : expr -> expr
| LetBang : var -> expr -> expr -> expr
| Bit : bool -> expr
| If : expr -> expr -> expr -> expr
| Pair : expr -> expr -> expr
| LetPair : var -> var -> expr -> expr -> expr
| Meas : expr -> expr
| QRef : qref -> expr
| New : expr -> expr
| Unitary : unitary -> expr -> expr
| Lambda : var -> expr -> expr
| Fix : var -> var -> expr -> expr
| App : expr -> expr -> expr
.
Inductive Val : expr -> Prop :=
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


Inductive Fresh x : expr -> Prop :=
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
  | Var y => if Var.V.eq_dec x y then v else Var y
  | LetIn y e1 e2 =>
    LetIn y (subst x v e1) (if Var.V.eq_dec x y then e2 else subst x v e2)
  | Bang e => Bang (subst x v e)
  | LetBang y e1 e2 =>
    LetBang y (subst x v e1) (if Var.V.eq_dec x y then e2 else subst x v e2)
  | Bit b => Bit b
  | If e e1 e2 => If (subst x v e) (subst x v e1) (subst x v e2)
  | Pair e1 e2 => Pair (subst x v e1) (subst x v e2)
  | LetPair y1 y2 e1 e2 =>
    LetPair y1 y2 (subst x v e1)
      (if Var.V.eq_dec x y1 then e2
       else if Var.V.eq_dec x y2 then e2
       else subst x v e2)
  | Meas e => Meas (subst x v e)
  | QRef q => QRef q
  | New e => New (subst x v e)
  | Unitary u e => Unitary u (subst x v e)
  | Lambda y e =>
    Lambda y (if Var.V.eq_dec x y then e else subst x v e)
  | Fix f y e =>
    Fix f y (if Var.V.eq_dec x f then e
             else if Var.V.eq_dec x y then e
             else subst x v e)
  | App e1 e2 => App (subst x v e1) (subst x v e2)
  end.

Module Config.
  Record t := {
    dim : nat;
    qstate : Matrix dim dim
  }.
  (* Definition add x (v : expr) (cfg : t) : t :=
  {|
    state := Var.Map.add x v (state cfg);
    dim := dim cfg;
    qstate := qstate cfg
  |}. *)
  (* Definition find x (cfg : t) : option expr :=
    Var.Map.find x (state cfg). *)


  (* Project onto the state where qubit q is in the classical state |b> *)
  (*Definition proj q dim (b : bool) := pad_u dim q (bool_to_matrix b).*)
  Definition measure (b : bool) (q : qref) (cfg : t) : t :=
    let rho' := super (pad_u q (dim cfg) (bool_to_matrix b)) (qstate cfg) in
    {|
      dim := dim cfg;
      qstate := rho'
    |}.
    
  Definition new (b : bool) (cfg : t) : qref * t :=
    let q := dim cfg in
    let rho' := kron (qstate cfg) (bool_to_ket b) in
    (q, {|
      dim := 1 + dim cfg;
      qstate := rho'
    |}).

  Definition apply_matrix (cfg : t) (U : Matrix (2 ^ dim cfg) (2 ^ dim cfg)) : t :=
  {|
    dim := dim cfg;
    qstate := super U (qstate cfg)
  |}.
  
  Definition gate_to_matrix (n : nat) (U : unitary) (qs : list qref) : Matrix (2^n) (2^n) :=
  match U, qs with
  | H, [q] => @pad 1 q n Quantum.hadamard
  | X, [q] => @pad 1 q n Quantum.σx
  | Y, [q] => @pad 1 q n Quantum.σy
  | Z, [q] => @pad 1 q n Quantum.σz
  | CNOT, [q1; q2] => pad_ctrl n q1 q2 Quantum.σx
  | Sgate, [q] => @pad 1 q n Quantum.Sgate
  | Sdag, [q]  => @pad 1 q n Quantum.Sgate†
  | Tgate, [q] => @pad 1 q n Quantum.Tgate
  | Tdag, [q]  => @pad 1 q n Quantum.Tgate†
  | _, _ => Zero
  end.
  Definition apply_gate (U : unitary) (qs : list qref) (cfg : t) : t :=
    apply_matrix cfg (gate_to_matrix _ U qs).

  
  Lemma test1 : gate_to_matrix 2 CNOT [0;1]%nat = cnot.
  Proof.
    assert (H : WF_Matrix (gate_to_matrix 2 CNOT [0%nat; 1%nat])).
    { simpl.
      set (H0 := QuantumLib.Pad.WF_pad_ctrl 2 0 1 σx).
      apply H0.
      auto with wf_db.
    }
    prep_matrix_equality.
    destruct x as [ | [ | [ | [ | x ]]]];
    destruct y as [ | [ | [ | [ | y ]]]];
      try (rewrite H; [ auto | right; simpl; lia]; fail);
      try (rewrite H; [ auto | left; simpl; lia]; fail);
      try lca.
  Qed.

  Lemma test2 :gate_to_matrix 1 H [0]%nat = hadamard.
  Proof.
    simpl. unfold pad. simpl. Msimpl; auto.
  Qed.


End Config.

Reserved Notation "cfg1 ~> cfg2" (at level 55).

Inductive step : expr * Config.t -> expr * Config.t -> Prop :=

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

(* Typing judgment: Gamma; Delta; Delta ⊢ t : tau 
 * Here, Delta is a set of qubit references that are currently in scope
 *)
Inductive WellTyped {n : nat} : Var.Map.t typ -> Var.Map.t typ -> expr -> typ -> Prop :=

| WTQVar : forall Gamma Delta x tau,
  Var.Singleton x tau Delta ->
  WellTyped Gamma Delta (Var x) tau

| WTCVar : forall Gamma Delta x tau,
  Var.Map.Empty Delta ->
  Var.Map.MapsTo x tau Gamma ->
  WellTyped Gamma Delta (Var x) tau

| WTLetIn : forall tau Delta1 Delta2 Gamma Delta x e1 e2 tau',
  WellTyped Gamma Delta1 e1 tau ->

  WellTyped Gamma (Var.Map.add x tau Delta2) e2 tau' ->
  
  Var.MapFacts.Partition Delta Delta1 Delta2 ->
  ~ Var.Map.In x Delta2 ->

  WellTyped Gamma Delta (LetIn x e1 e2) tau'

| WTBang : forall Gamma Delta e tau,
  Var.Map.Empty Delta ->
  WellTyped Gamma Delta e tau ->
  WellTyped Gamma Delta (Bang e) (BANG tau)

| WTLetBang : forall tau Delta1 Delta2 Gamma Delta x e1 e2 tau',
  WellTyped Gamma Delta1 e1 (BANG tau) ->
  WellTyped (Var.Map.add x tau Gamma) Delta2 e2 tau' ->

  Var.MapFacts.Partition Delta Delta1 Delta2 ->

  WellTyped Gamma Delta (LetBang x e1 e2) tau'

| WTBit : forall Gamma Delta b,
  Var.Map.Empty Delta ->
  WellTyped Gamma Delta (Bit b) BIT

| WTIf : forall Delta' Delta'' Gamma Delta e e1 e2 tau,

  WellTyped Gamma Delta' e BIT ->
  WellTyped Gamma Delta'' e1 tau ->
  WellTyped Gamma Delta'' e2 tau ->

  Var.MapFacts.Partition Delta Delta' Delta'' ->

  WellTyped Gamma Delta (If e e1 e2) tau

| WTPair : forall Delta1 Delta2 Gamma Delta e1 e2 tau1 tau2,
  WellTyped Gamma Delta1 e1 tau1 ->
  WellTyped Gamma Delta2 e2 tau2 ->

  Var.MapFacts.Partition Delta Delta1 Delta2 ->

  WellTyped Gamma Delta (Pair e1 e2) (Tensor tau1 tau2)

| WTLetPair : forall tau1 tau2 Delta1 Delta2 Gamma Delta x1 x2 e e' tau',

  WellTyped Gamma Delta1 e (Tensor tau1 tau2) ->
  WellTyped Gamma (Var.Map.add x1 tau1 (Var.Map.add x2 tau2 Delta2)) e' tau' ->
  
  Var.MapFacts.Partition Delta Delta1 Delta2 ->
  ~ Var.Map.In x1 Delta2 ->
  ~ Var.Map.In x2 Delta2 ->

  WellTyped Gamma Delta (LetPair x1 x2 e e') tau'

| WTMeas : forall Gamma Delta e,
  WellTyped Gamma Delta e QUBIT ->
  WellTyped Gamma Delta (Meas e) (BANG BIT)

| WTQRef : forall Gamma Delta q,
  (q < n)%nat ->
  Var.Map.Empty Delta ->
  WellTyped Gamma Delta (QRef q) QUBIT

| WTNew : forall Gamma Delta e,
  WellTyped Gamma Delta e BIT ->
  WellTyped Gamma Delta (New e) QUBIT

| WTUnitary : forall Gamma Delta U e tau,
  type_of_unitary U = tau ->
  WellTyped Gamma Delta e tau ->
  WellTyped Gamma Delta (Unitary U e) tau

| WTLambda : forall Gamma Delta x e tau1 tau2,
  ~ Var.Map.In x Delta ->
  WellTyped Gamma (Var.Map.add x tau1 Delta) e tau2 ->
  WellTyped Gamma Delta (Lambda x e) (Lolli tau1 tau2)

| WTFix : forall Gamma Delta f x e tau1 tau2,

  Var.Map.Empty Delta ->
  ~ Var.V.eq f x ->
  WellTyped (Var.Map.add f (Lolli tau1 tau2) (Var.Map.add x tau1 Gamma)) Delta e tau2 ->

  WellTyped Gamma Delta (Fix f x e) (Lolli (BANG tau1) tau2)
.
Arguments WellTyped : clear implicits.

Hint Constructors WellTyped : qoreo_db.
(* TODO: The stronger statement would be 
to define alpha equivalence for expressions
and then to prove this with respect to
    Var.Map.Equiv alpha_equiv
*)
Lemma WellTyped_context_equal :
  forall n Gamma Delta e tau,
    WellTyped n Gamma Delta e tau ->
  forall Gamma' Delta',
    Var.Map.Equal Gamma Gamma' ->
    Var.Map.Equal Delta Delta' ->
    WellTyped n Gamma' Delta' e tau.
Proof.
  intros n Gamma Delta e tau He.
  induction He; intros Gamma' Delta' HGamma HDelta;
    try (econstructor; eauto;
      try apply IHHe;
      try apply IHHe1;
      try apply IHHe2;
      try apply IHHe3;
      try rewrite <- HDelta;
      try rewrite <- HGamma;
      try reflexivity;
      auto; fail).
  * apply WTQVar.
    unfold Var.Singleton in *.
    rewrite <- HDelta; auto.
Qed.
    

Global Instance WellTypedProper : Proper ((@eq nat) ==> Var.Map.Equal ==> Var.Map.Equal ==> eq ==> eq ==> iff) WellTyped.
Proof.
  intros n1 n2 Hn Gamma1 Gamma2 HGamma
    Delta1 Delta2 HDelta e1 e2 He
    tau1 tau2 Htau; subst.
  split; intros; eapply WellTyped_context_equal; eauto.
  * rewrite HGamma; reflexivity.
  * rewrite HDelta; reflexivity. 
Qed.


(***************)
(* Type safety *)
(***************)

Lemma weakening : forall n Gamma Delta e tau,
  WellTyped n (Var.Map.empty _) Delta e tau ->
  WellTyped n Gamma Delta e tau.
Proof.
Admitted.

Lemma dim_weakening : forall n n' Gamma Delta e tau,
  WellTyped n Gamma Delta e tau ->
  (n <= n')%nat ->
  WellTyped n' Gamma Delta e tau.
Admitted.

Lemma wt_subst : forall tau n Gamma Delta x v e tau',
  WellTyped n Gamma Delta e tau' ->
  Val v ->
  WellTyped n (Var.Map.empty _) (Var.Map.empty _) v tau ->
  Var.Map.MapsTo x tau Delta ->
  WellTyped n Gamma (Var.Map.remove x Delta) (subst x v e) tau'.
Proof.
    intros tau n Gamma Delta x v e tau' HWT.
    revert tau x v.
    induction HWT; intros tau0 x0 v0 Hvalv0 HWTv0 Hindom;
      simpl.
    * unfold Var.Singleton in H0.
      assert (Heq : x = x0 /\ tau = tau0).
      { rewrite H0 in Hindom.
          apply Var.MapFacts.F.add_mapsto_iff in Hindom.
          destruct Hindom as [ | [_ Hcontra]]; auto.
          apply Var.MapFacts.F.empty_mapsto_iff in Hcontra; contradiction.
      }
      destruct Heq; subst.
      destruct (Var.V.eq_dec x0 x0) as [Heq | Hneq].
      2:{ contradict Hneq. reflexivity. }
      setoid_replace (Var.Map.remove x0 Delta) with (Var.Map.empty typ).
      2:{
        rewrite H0.
        apply Var.MapFacts.F.Equal_mapsto_iff;
          intros x tau.
        rewrite Var.MapFacts.F.remove_mapsto_iff.
        rewrite Var.MapFacts.F.add_mapsto_iff.
        split; [intros [? [[? ?] | [? ?]]] | inversion 1];
          auto;
          try contradiction.
      }
      apply weakening; auto.

    * contradict Hindom.
        apply (Var.MapFacts.elements_Empty Delta) in H0.
        intros HMapsTo.
        apply Var.Map.elements_1 in HMapsTo.
        rewrite H0 in HMapsTo. 
        inversion HMapsTo.

    * apply (WTLetIn tau (Var.Map.remove x0 Delta1) (Var.Map.remove x0 Delta2)); auto.
      + eapply IHHWT1; eauto.
        admit (* If Delta(x0)=tau0 and Delta==Delt1,Delta2 and x ∉ Delta2 then Delta1(x0)=tau0 *).
      + admit.
      + admit (* partition wrt remove function *).
      + Search Var.Map.In Var.Map.remove. 
        rewrite Var.MapFacts.F.remove_in_iff.
        admit.

    * simpl; econstructor; eauto.
      admit (* lemma *).
    * (*let!*) admit.
    *  contradict Hindom. admit.
    * (* if *)  admit.
    * (* Pair *)  admit.
    * (* LetPair *) admit.
    * (* Bang *) contradict Hindom. admit.
    * (* QRef *) (* Maybe our typing judgment should also have a list of qubit variables in scope... *) admit.
    * (* new *) econstructor; eauto.
    * (* Unitary *) econstructor; eauto.
    * (* Lambda *) admit.
    * (* Fix *) admit.
Admitted. 

Theorem preservation : forall e cfg e' cfg',
  (e, cfg) ~> (e',cfg') ->
  forall tau,
  WellTyped (Config.dim cfg) (Var.Map.empty _) (Var.Map.empty _) e tau ->
  WellTyped (Config.dim cfg') (Var.Map.empty _) (Var.Map.empty _) e' tau.
Proof.
  intros e cfg e' cfg' step.
  remember (e,cfg) as CFG eqn:HCFG.
  remember (e',cfg') as CFG' eqn:HCFG'.
  revert e cfg e' cfg' HCFG HCFG'.
  induction step; intros ? ? ? ? HCFG HCFG' tau Hwt;   
    inversion HCFG; inversion HCFG'; subst;
    clear HCFG; clear HCFG'.
  * inversion Hwt; subst; clear Hwt.
    (* Delta1 = Var.Map.empty and Delta2 = Var.Map.empty *)
    admit.
  * (*apply wt_subst. *) admit.
  *
Admitted. 



Theorem progress : forall n e tau cfg,
  WellTyped n (Var.Map.empty _) (Var.Map.empty _) e tau ->
  Config.dim cfg = n ->
  Val e \/ exists e' cfg', (e, cfg) ~> (e', cfg').
Admitted.
