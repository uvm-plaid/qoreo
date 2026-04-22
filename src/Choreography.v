From Qoreo Require Import Base.
From Qoreo Require Expr.

From Stdlib Require Import Structures.Equalities.

Module Insn.
    Inductive t : Type :=

    | Send : Actor.t -> Expr.t -> Actor.t -> Var.t -> t
    | EPR : Actor.t -> Var.t -> Actor.t -> Var.t -> t

    | Let : Actor.t -> Var.t -> Expr.t -> t
    | LetBang : Actor.t -> Var.t -> Expr.t -> t
    | LetPair : Actor.t -> Var.t -> Var.t -> Expr.t -> t.


    Definition actors (I : t) : Actor.FSet.t :=
        match I with
        | Send A _ B _ | EPR A _ B _ => Actor.FSet.add A (Actor.FSet.singleton B)
        | Let A _ _ | LetBang A _ _ | LetPair A _ _ _ => Actor.FSet.singleton A
        end.

    
(* substitute the value v for A.x in I *)
    Definition subst (A : Actor.t) (x : Var.t) (v : Expr.t)  (I : t) : t :=
    match I with
    | Send B1 e B2 y => 
        (* Assume x <> y *)
        let e' := if Actor.eq_dec A B1 then Expr.subst x v e else e in
        Send B1 e' B2 y
    | EPR B1 y1 B2 y2 => EPR B1 y1 B2 y2
    | Let B y e =>
        let e' := if Actor.eq_dec A B then Expr.subst x v e else e in
        Let B y e'
    | LetBang B y e =>
        let e' := if Actor.eq_dec A B then Expr.subst x v e else e in
        LetBang B y e'
    | LetPair B y1 y2 e =>
        let e' := if Actor.eq_dec A B then Expr.subst x v e else e in
        LetPair B y1 y2 e'
    end.

    Definition bindt : Type := Actor.t * Var.t.

    Definition bindings (I : t) : list bindt :=
      match I with
      | Send B1 e B2 y => [(B2,y)]    
      | EPR B1 y1 B2 y2 => [(B1,y1);(B2,y2)]
      | Let B y e => [(B,y)]
      | LetBang B y e => [(B,y)]
      | LetPair B y1 y2 e => [(B,y1);(B,y2)]
    end.
           
    Definition bind_eqb  (Ax : bindt) (By: bindt) : bool :=
      if Actor.eq_dec (fst Ax) (fst By) then if Var.eq_dec (snd Ax) (snd By) then true else false else false.

    Definition rebound_in (A : Actor.t) (x : Var.t) (I : t) : bool :=
      match I with
      | Send B1 e B2 y => bind_eqb (A,x) (B2,y)    
      | EPR B1 y1 B2 y2 => (bind_eqb (A,x) (B1,y1)) || (bind_eqb (A,x) (B2,y2))
      | Let B y e => bind_eqb (A,x) (B,y) 
      | LetBang B y e => bind_eqb (A,x) (B,y) 
      | LetPair B y1 y2 e => (bind_eqb (A,x) (B,y1)) || (bind_eqb (A,x) (B,y2)) 
    end.       
End Insn.

Module Choreography.
    Definition t := list Insn.t.

    Definition actors (C : t) : Actor.FSet.t :=
        List.fold_left (fun X I => Actor.FSet.union X (Insn.actors I)) C Actor.FSet.empty.

    Fixpoint subst (A : Actor.t) (x : Var.t) (v : Expr.t) (C : t) : t :=
      match C with
      | [] => []
      | (Ins :: C') => (Insn.subst A x v Ins)::(if (Insn.rebound_in A x Ins)
                                                then C' else (subst A x v C')) 
      end. 

    (* Fixpoint subst (A : Actor.t) (x : Var.t) (v : Expr.t) (C : t) : t :=
      match C with
      | [] => []
      | (Ins :: C') =>
          if (List.existsb (Insn.bind_eqb (A,x)) (Insn.bindings (Ins))) then
            (Insn.subst A x v Ins)::C'
          else
            (Insn.subst A x v Ins)::(subst A x v C') 
      end.*)
End Choreography.

Module Label.
    Inductive t :=
    | Send : Actor.t -> Expr.t -> Actor.t -> t
    | EPR  : Actor.t -> Actor.t -> t
    | Loc  : Actor.t -> t
    .


    Definition actors (l : t) : Actor.FSet.t :=
        match l with
        | Send A _ B | EPR A B => Actor.FSet.add A (Actor.FSet.singleton B)
        | Loc A => Actor.FSet.singleton A
        end.
End Label.



(** Semantics **)


Inductive step : Choreography.t * Config.t -> Label.t -> Choreography.t * Config.t -> Prop :=

| SendC : forall A e B x C cfg e' cfg',
    Expr.step (e, cfg) (e', cfg') ->
    step (Insn.Send A e B x :: C, cfg) (Label.Loc A) (Insn.Send A e' B x :: C, cfg')

| SendB : forall A v B x C cfg C',
    Expr.Val v ->
    C' = Choreography.subst B x v C ->
    step (Insn.Send A v B x :: C, cfg) (Label.Send A v B) (C', cfg)

| EPRB : forall q1 q2 A x B y C cfg C' cfg',
    Config.epr cfg = (q1,q2,cfg') ->
    C' = Choreography.subst A x (Expr.Var q1) (Choreography.subst B y (Expr.Var q2) C) ->
    step (Insn.EPR A x B y :: C, cfg) (Label.EPR A B) (C', cfg')

| LetC : forall A x e C cfg e' cfg',
    Expr.step (e,cfg) (e',cfg') ->
    step (Insn.Let A x e :: C, cfg) (Label.Loc A) (Insn.Let A x e' :: C, cfg')
| LetB : forall A x v C cfg C',
    Expr.Val v ->
    C' = Choreography.subst A x v C ->
    step (Insn.Let A x v :: C, cfg) (Label.Loc A) (C', cfg)

| LetBangC : forall A x e C cfg e' cfg',
    Expr.step (e,cfg) (e',cfg') ->
    step (Insn.LetBang A x e :: C, cfg) (Label.Loc A) (Insn.LetBang A x e' :: C, cfg')
| LetBangB : forall A x e0 C cfg C',
    C' = Choreography.subst A x e0 C ->
    step (Insn.LetBang A x (Expr.Bang e0) :: C, cfg) (Label.Loc A) (C', cfg)

| LetPairC : forall A x1 x2 e C cfg e' cfg',
    Expr.step (e,cfg) (e',cfg') ->
    step (Insn.LetPair A x1 x2 e :: C, cfg) (Label.Loc A) (Insn.LetPair A x1 x2 e' :: C, cfg')
| LetPairB : forall A x1 x2 v1 v2 C cfg C',
    Expr.Val v1 -> Expr.Val v2 ->
    C' = Choreography.subst A x1 v1 (Choreography.subst A x2 v2 C) ->
    step (Insn.LetPair A x1 x2 (Expr.Pair v1 v2) :: C, cfg) (Label.Loc A) (C', cfg)

(* delay *)
| Delay : forall I C cfg C' cfg' l,
    step (C, cfg) l (C', cfg') ->
    Actor.FSet.Empty (Actor.FSet.inter (Label.actors l) (Insn.actors I)) ->
    step (I::C, cfg) l (I::C', cfg')
.

Module ChorTEnv.
    Definition t := Actor.Map.t (Var.Map.t Expr.typ).
    (* equivalence of ChorTEnv.t *)
    Definition Equal (G1 G2 : t) : Prop := Actor.Map.Equiv (Var.Map.Equal) G1 G2.
    Definition find (A : Actor.t) (G : t) : Var.Map.t Expr.typ :=
        match Actor.Map.find A G with
        | Some D => D
        | None => Var.Map.empty _
        end.

    Definition add (A : Actor.t) (x : Var.t) (tau : Expr.typ) (G : t) : t :=
        let D := find A G in
        Actor.Map.add A (Var.Map.add x tau D) G.

    Definition MapsTo (A : Actor.t) (x : Var.t) (tau : Expr.typ) (G : t) : Prop :=
      Var.Map.MapsTo x tau (find A G).
End ChorTEnv.


Inductive WellTyped : ChorTEnv.t -> ChorTEnv.t -> Choreography.t -> Prop :=
  
| Nil : forall G D, 
    Actor.Map.Empty D ->
    WellTyped G D nil
                                
| EPR : forall G D A x B y C,
    A <> B ->
    WellTyped G (ChorTEnv.add B y Expr.QUBIT (ChorTEnv.add A x Expr.QUBIT D)) C ->

    ~ Var.Map.In x (ChorTEnv.find A D) ->
    ~ Var.Map.In y (ChorTEnv.find A D) ->

    WellTyped G D ((Insn.EPR A x B y)::C)

| Send : forall DeltaA1 DeltaA2 G D A e tau B y C,
    A <> B ->
    Expr.WellTyped (ChorTEnv.find A G) DeltaA1 e (Expr.BANG tau) ->
    WellTyped (ChorTEnv.add B y tau G) (Actor.Map.add A DeltaA2 D) C ->

    Var.MapFacts.Partition (ChorTEnv.find A D) DeltaA1 DeltaA2 ->

    WellTyped G D ((Insn.Send A e B y)::C)

| LetBang : forall DeltaA1 DeltaA2 G D A x e tau C,

    Expr.WellTyped (ChorTEnv.find A G) DeltaA1 e (Expr.BANG tau) ->
    WellTyped (ChorTEnv.add A x tau G) (Actor.Map.add A DeltaA2 D) C ->

    Var.MapFacts.Partition (ChorTEnv.find A D) DeltaA1 DeltaA2 ->

    WellTyped G D ((Insn.LetBang A x e)::C)

| LetIn : forall DeltaA1 DeltaA2 G D A x e tau C,

    Expr.WellTyped (ChorTEnv.find A G) DeltaA1 e tau ->
    WellTyped G (Actor.Map.add A (Var.Map.add x tau DeltaA2) D) C ->

    Var.MapFacts.Partition (ChorTEnv.find A D) DeltaA1 DeltaA2 ->
    ~ Var.Map.In x DeltaA2 ->

    WellTyped G D ((Insn.Let A x e)::C)

| LetPair: forall DeltaA1 DeltaA2 G D A x1 x2 tau1 tau2 e C,

    Expr.WellTyped (ChorTEnv.find A G) DeltaA1 e (Expr.Tensor tau1 tau2) ->
    WellTyped G (Actor.Map.add A (Var.Map.add x1 tau1 (Var.Map.add x2 tau2 DeltaA2)) D) C ->

    Var.MapFacts.Partition (ChorTEnv.find A D) DeltaA1 DeltaA2 ->
    ~ Var.Map.In x1 DeltaA2 -> 
    ~ Var.Map.In x2 DeltaA2 ->

    WellTyped G D ((Insn.LetPair A x1 x2 e)::C)
.

Lemma extension : forall A G x tau,
    ChorTEnv.MapsTo A x tau G <-> Var.Map.MapsTo x tau (ChorTEnv.find A G).
Proof.
  intros A G x tau.
  split.
  auto.
  auto.
Qed.

Lemma map_subset_add : forall G1 G2,
    (forall A x tau, (ChorTEnv.MapsTo A x tau G1 -> ChorTEnv.MapsTo A x tau G2)) ->
    (forall A x tau1 B y tau2,
        (ChorTEnv.MapsTo A x tau1 (ChorTEnv.add B y tau2 G1) ->
         ChorTEnv.MapsTo A x tau1 (ChorTEnv.add B y tau2 G2))).
Proof.
  intros G1 G2 HMA1 A x tau1 B y tau2 HMA2. 
Admitted.

Lemma weakening_gen : forall G D C,
    WellTyped G D C -> forall G',
      (forall A x tau, ChorTEnv.MapsTo A x tau G -> ChorTEnv.MapsTo A x tau G') ->
      WellTyped G' D C.
Proof.
  intros G D C HWT.
  induction HWT.
  
  - intros G' HW. apply Nil. auto. 

  - intros G' HW. apply EPR; auto.

  - intros G' HW. eapply Send. auto.
    eapply Expr.weakening_gen. eauto.

    intros x tau' HEW.
    rewrite <- extension.
    apply extension in HEW.
    apply (HW A x tau') in HEW.
    auto.

    specialize (IHHWT (ChorTEnv.add B y tau G')).
    apply IHHWT.
    intros A0 x tau' HWB.
    pose proof (map_subset_add G G' HW A0 x tau' B y tau) as HMA.
    auto.

    auto.

  - intros G' HW. eapply LetBang.
    pose proof (Expr.weakening_gen
                  (ChorTEnv.find A G) DeltaA1 e (Expr.BANG tau) H (ChorTEnv.find A G'))
      as HEW.
    apply HEW.
    intros x' tau' HVM.
    specialize (HW A x' tau').
    rewrite -> extension in HW.
    rewrite -> extension in HW.
    auto.

    specialize (IHHWT (ChorTEnv.add A x tau G')).
    apply IHHWT.
    intros A0 x0 tau0 HE.
    pose proof (map_subset_add G G' HW A0 x0 tau0 A x tau) as HMA.
    auto.

    auto.

  - intros G' HW. eapply LetIn.
    pose proof (Expr.weakening_gen (ChorTEnv.find A G) DeltaA1 e tau H (ChorTEnv.find A G'))
      as HEW.
    setoid_rewrite -> extension in HW.
    auto.

    apply IHHWT.
    auto.

    apply H0.

    auto.

  - intros G' HW. eapply LetPair.
    pose proof (Expr.weakening_gen (ChorTEnv.find A G) DeltaA1 e
                  (Expr.Tensor tau1 tau2) H (ChorTEnv.find A G'))
      as HEW.
    setoid_rewrite -> extension in HW.
    auto.
    
    apply IHHWT.
    auto.

    apply H0.
    auto.

    auto.
Qed.

Lemma no_capture_add : forall A x tau1 I G, 
    (Insn.rebound_in A x I) = false ->
    (forall B y tau2, (List.In (B,y) (Insn.bindings I)) ->
                      ChorTEnv.MapsTo A x tau1 G -> ChorTEnv.MapsTo A x tau1 (ChorTEnv.add B y tau2 G))
.
Proof.
Admitted.

Lemma wt_subst_bang : forall tau G D A x v C,
    WellTyped G D C ->
    Expr.Val v ->
    Expr.WellTyped (Var.Map.empty _) (Var.Map.empty _) v (Expr.BANG tau) ->
    ChorTEnv.MapsTo A x tau G ->
               WellTyped G D (Choreography.subst A x v C).
Proof.
  intros tau G D A x v C HWT HV HWTV HA.
  induction HWT.

  - apply Nil. auto.

  - apply EPR.

    auto.

    fold Choreography.subst.
    destruct (Insn.rebound_in A x (Insn.EPR A0 x0 B y)).
    { auto. }
    { apply IHHWT. auto. }
    
    auto.
    
    auto. 

  - eapply Send.

    apply H.
    destruct (Actor.eq_dec A A0) eqn:Heq.
    {
      pose proof (Expr.wt_subst_bang tau (ChorTEnv.find A0 G) DeltaA1 x v e (Expr.BANG tau0)) as HEWTS.
      apply HEWTS; auto.
      rewrite <- e0.
      rewrite <- extension.
      auto.
    }
    { auto. }
    
    fold Choreography.subst.
    destruct (Insn.rebound_in A x (Insn.Send A0 e B y)) eqn:Heq.
    { eapply HWT. }
    {
      apply IHHWT.
      pose proof (no_capture_add A x tau (Insn.Send A0 e B y) G) as HNCA.
      specialize (HNCA Heq B y tau0).
      apply HNCA.
      unfold Insn.bindings.
      simpl.
      auto.
      auto.
    }

    eauto.

  - eapply LetBang.

    destruct (Actor.eq_dec A A0) eqn:Heq.
    {
      pose proof (Expr.wt_subst_bang tau (ChorTEnv.find A0 G) DeltaA1 x v e (Expr.BANG tau0)) as HEWTS.
      eapply HEWTS.
      auto.
      auto.
      auto.
      auto.
      rewrite <- extension.
      rewrite <- e0.
      auto.
    }
    { auto. }
    
    fold Choreography.subst.
    destruct (Insn.rebound_in A x (Insn.LetBang A0 x0 e)) eqn:Heq.
    { eapply HWT. }
    {
      apply IHHWT.
      pose proof (no_capture_add A x tau (Insn.LetBang A0 x0 e) G) as HNCA.
      specialize (HNCA Heq A0 x0 tau0).
      apply HNCA.
      unfold Insn.bindings.
      simpl.
      auto.
      auto.
    }

    eauto.

  - eapply LetIn.

    destruct (Actor.eq_dec A A0) eqn:Heq.

    {
      pose proof (Expr.wt_subst_bang tau (ChorTEnv.find A0 G) DeltaA1 x v e tau0) as HEWTS.
      eapply HEWTS.
      auto.
      auto.
      auto.
      auto.
      rewrite <- e0.
      rewrite <- extension.
      auto.
    }
    { auto. }

    fold Choreography.subst.
    destruct (Insn.rebound_in A x (Insn.Let A0 x0 e)) eqn:Heq.
    { eapply HWT. }
    {
      apply IHHWT.
      auto.
    }
    
    auto.
    auto.

    - eapply LetPair.
    
Admitted.
    
    
Lemma wt_subst_lin : forall tau G D A x v C,
    WellTyped G D C ->
    Expr.Val v ->
    Expr.WellTyped (Var.Map.empty _) (Var.Map.empty _) v tau ->
    ChorTEnv.MapsTo A x tau D ->
    WellTyped G (Actor.Map.add A (Var.Map.remove x (ChorTEnv.find A D)) D) (Choreography.subst A x v C).
Proof.
  Admitted.
  
(* placeholder for well-formedness definition *)
Definition  WellFormed (cfg : Config.t) (C : ChorTEnv.t) : Prop := True.

Theorem preservation : forall C1 cfg1 l C2 cfg2,
  step (C1, cfg1) l (C2,cfg2) ->
  forall D1,
  WellFormed cfg1 D1 ->
  WellTyped (Actor.Map.empty _) D1 C1 ->
  exists D2,
  WellFormed cfg2 D2 /\ WellTyped (Actor.Map.empty _) D2 C2.
Proof.
Admitted.
