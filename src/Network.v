From Qoreo Require Import Base.
From Qoreo Require Expr Choreography.
From Stdlib Require Import Morphisms (* for Proper *).

Module Label := Choreography.Label.
Module Choreography := Choreography.Choreography.

From Stdlib Require Lists.List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Stdlib.Structures.Equalities.
Import Actor.Map.Tactics.

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

    Inductive step : Process.t -> Var.Map.t nat -> Config.t -> Process.t -> Var.Map.t nat -> Config.t -> Prop :=
    | LetC : forall x e P refs ρ e' refs' ρ',
        Expr.step e refs ρ e' refs' ρ' ->
        step (Insn.Let x e :: P) refs ρ (Insn.Let x e' :: P) refs' ρ'
    | LetB : forall x v P refs ρ P',
        Expr.Val v ->
        P' = Process.subst x v P ->
        step (Insn.Let x v :: P) refs ρ P' refs ρ

    | LetBangC : forall x e P refs ρ e' refs' ρ',
        Expr.step e refs ρ e' refs' ρ' ->
        step (Insn.LetBang x e :: P) refs ρ (Insn.LetBang x e' :: P) refs' ρ'
    | LetBangB : forall x e P refs ρ P',
        P' = Process.subst x e P ->
        step (Insn.LetBang x (Expr.Bang e) :: P) refs ρ P' refs ρ

    | LetPairC : forall x1 x2 e P refs ρ e' refs' ρ',
        Expr.step e refs ρ e' refs' ρ' ->
        step (Insn.LetPair x1 x2 e :: P) refs ρ (Insn.LetPair x1 x2 e' :: P) refs' ρ'
    | LetPairP : forall x1 x2 v1 v2 P ρ refs P',
        Expr.Val v1 -> Expr.Val v2 ->
        P' = Process.subst x1 v1 (Process.subst x2 v2 P) ->
        step (Insn.LetPair x1 x2 (Expr.Pair v1 v2) :: P) refs ρ P' refs ρ

    | SendC : forall e B P refs ρ e' refs' ρ',
        Expr.step e refs ρ e' refs' ρ' ->
        step (Insn.Send e B :: P) refs ρ (Insn.Send e' B :: P) refs' ρ'
    .

End Process.

Module Network.
    Definition t := Actor.Map.t (Process.t).

    Inductive step :    Network.t -> ChorEnv.t nat -> Config.t ->
                        Label.t ->
                        Network.t -> ChorEnv.t nat -> Config.t -> Prop :=

    | Loc : forall P P' refsA' N' N refs cfg A refs' cfg',
      Actor.Map.MapsTo A P N ->
      Process.step  P (ChorEnv.find A refs) cfg
                    P' refsA' cfg' ->
      N' = Actor.Map.add A P' N ->
      ChorEnv.Equal refs' (Actor.Map.add A refsA' refs) ->
      step  N refs cfg
            (Label.Loc A)
            N' refs' cfg'

    | Send : forall PA PB y N refs cfg A v B N',
      A <> B ->
      Actor.Map.MapsTo A (Insn.Send v B :: PA) N ->
      Actor.Map.MapsTo B (Insn.Receive y A :: PB) N ->
      Expr.Val v ->
      N' = Actor.Map.add A PA (Actor.Map.add B (Process.subst y v PB) N) ->
      
      step N refs cfg (Label.Send A v B) N' refs cfg

    | EPR : forall x y PA PB qA qB N refs cfg A B N' refs' cfg',
      A <> B ->
      Actor.Map.MapsTo A (Insn.EPR x B :: PA) N ->
      Actor.Map.MapsTo B (Insn.EPR y A :: PB) N ->
      ChorEnv.epr A B refs cfg = (qA, qB, refs', cfg') ->
      N' = Actor.Map.add A (Process.subst x (Expr.Var qA) PA) (
            Actor.Map.add B (Process.subst y (Expr.Var qB) PB) N) ->

      step N refs cfg (Label.EPR A B) N' refs' cfg'
    .

    Record WF (Actors : Actor.FSet.t) (N : Network.t) :=
        {
            wf_domain : forall A, Actor.FSet.In A Actors <-> Actor.Map.In A N;
        }.
    
End Network.

Definition conso {A : Type} (x : A) (xso : option (list A)) : option (list A) :=
  match xso with
  | None => None
  | Some xs => Some (x :: xs)
  end.

Fixpoint epp (p : Actor.t) (c : Choreography.t): option Process.t :=
  match c with
  | [] => Some []
  | Choreography.Insn.Send A1 e A2 x :: C =>
      match (Actor.eq_dec A1 p, Actor.eq_dec A2 p) with
      | (left _, left _)  => None
      | (left _, right _) => conso (Insn.Send e A2) (epp p C)
      | (right _, left _) => conso (Insn.Receive x A1) (epp p C)
      | _ => epp p C
      end
  | Choreography.Insn.EPR A1 x1 A2 x2 :: C =>
      match (Actor.eq_dec A1 p, Actor.eq_dec A2 p) with
      | (left _, left _)  => None
      | (left _, right _) => conso (Insn.EPR x1 A2) (epp p C)
      | (right _, left _) => conso (Insn.EPR x2 A1) (epp p C)
      | _ => epp p C
      end
  | Choreography.Insn.Let A1 x e :: C =>
      if Actor.eq_dec A1 p
      then conso (Insn.Let x e) (epp p C)
      else epp p C
  | Choreography.Insn.LetBang A1 x e :: C =>
      if Actor.eq_dec A1 p
      then conso (Insn.LetBang x e) (epp p C)
      else epp p C
  | Choreography.Insn.LetPair A1 x1 x2 e :: C =>
      if Actor.eq_dec A1 p
      then conso (Insn.LetPair x1 x2 e) (epp p C)
      else epp p C
  (* | _ => None *)
end.

(*
Inductive EPP : list Actor.t -> Choreography.t -> Network.t -> Prop :=
| epp_empty : forall C, EPP [] C (Actor.Map.empty _)
| epp_cons : forall A Actors C P N,
    epp A C = Some P ->
    EPP Actors C N ->
    EPP (A::Actors) C (Actor.Map.add A P N).
*)
Inductive EPP : Actor.t -> Choreography.t -> Process.t -> Prop :=
| EPP_nil : forall A, EPP A [] []

| EPP_send : forall D A C P B e y,
    D = A ->
    D <> B ->
    EPP D C P ->
    EPP D (Choreography.Insn.Send A e B y :: C) (Insn.Send e B :: P)
| EPP_receive : forall D B C P A e y,
    D = B ->
    D <> A ->
    EPP D C P ->
    EPP D (Choreography.Insn.Send A e B y :: C) (Insn.Receive y A :: P)

| EPP_EPR_1 : forall D A B x y C P,
    D = A ->
    D <> B ->
    EPP D C P ->
    EPP D (Choreography.Insn.EPR A x B y :: C) (Insn.EPR x B :: P)
| EPP_EPR_2 : forall D A B x y C P,
    D <> A ->
    D = B ->
    EPP D C P ->
    EPP D (Choreography.Insn.EPR A x B y :: C) (Insn.EPR y A :: P)

| EPP_Let : forall D A x e C P,
    D = A ->
    EPP D C P ->
    EPP D (Choreography.Insn.Let A x e :: C) (Insn.Let x e :: P)

| EPP_LetBang : forall D A x e C P,
    D = A ->
    EPP D C P ->
    EPP D (Choreography.Insn.LetBang A x e :: C) (Insn.LetBang x e :: P)

| EPP_LetPair : forall D A x1 x2 e C P,
    D = A ->
    EPP D C P ->
    EPP D (Choreography.Insn.LetPair A x1 x2 e :: C) (Insn.LetPair x1 x2 e :: P)

| EPP_disjoint : forall A I C P,
  ~ Actor.FSet.In A (Choreography.Insn.actors I) ->
  EPP A C P ->
  EPP A (I :: C) P
.

Lemma EPP_correct : forall A C P,
    EPP A C P <-> epp A C = Some P.
Proof.
    intros.
    split.
    * intros HEPP. 
      induction HEPP; simpl; auto;
        subst;
        try rewrite IHHEPP;
        Actor.simplify.
      destruct I; simpl in *;
        Actor.simplify.
    * revert A P.
      induction C as [ | I C]; intros A P Hepp.
      { 
        simpl in *.
        inversion Hepp; subst; clear Hepp.
        constructor.
      }
      simpl in Hepp.
      destruct (epp A C) eqn:IH.
      2:{
        destruct I; Actor.simplify; try rewrite IH in Hepp.
      }
      destruct I
        as [B1 e B2 x | B1 x1 B2 x2 | B x e | B x e | B x1 x2 e];
        Actor.simplify;
        inversion Hepp; subst; clear Hepp;
          constructor; auto;
        simpl; Actor.simplify.
Qed.


(*
Definition EPP_N (C : Choreography.t) (N : Network.t) : Prop :=
    forall A PA,
        Actor.Map.MapsTo A PA N
        ->
        (*Actor.FSet.In A (Choreography.actors C)*)
        EPP A C PA.
*)
Inductive EPP_N C : Network.t -> Prop :=
| EPP_N_empty : forall N,
  Actor.Map.Empty N ->
  EPP_N C N
| EPP_N_add : forall A PA N,
  Actor.Map.MapsTo A PA N ->
  EPP A C PA ->
  EPP_N C (Actor.Map.remove A N) ->
  EPP_N C N.


Definition eppI (D : Actor.t) (I : Choreography.Insn.t) : Process.t :=
  match I with
  | Choreography.Insn.Send A v B x =>
    if Actor.eq_dec D A then [Insn.Send v B]
    else if Actor.eq_dec D B then [Insn.Receive x A]
    else []
  | Choreography.Insn.EPR A x B y =>
    if Actor.eq_dec D A then [Insn.EPR x B]
    else if Actor.eq_dec D B then [Insn.EPR y A]
    else []
  | Choreography.Insn.Let A x e =>
    if Actor.eq_dec D A then [Insn.Let x e]
    else []
  | Choreography.Insn.LetBang A x e =>
    if Actor.eq_dec D A then [Insn.LetBang x e]
    else []
  | Choreography.Insn.LetPair A x1 x2 e =>
    if Actor.eq_dec D A then [Insn.LetPair x1 x2 e]
    else []
  end.
Lemma eppI_disjoint : forall D I,
  ~ Actor.FSet.In D (Choreography.Insn.actors I) ->
  eppI D I = [].
Proof.
  intros D I Hin; destruct I; auto; simpl in *; Actor.simplify.
Qed.


Inductive WFInsn : Choreography.Insn.t -> Prop :=
| WFSend : forall A v B x,
  A <> B -> WFInsn (Choreography.Insn.Send A v B x)
| WFEPR : forall A x B y,
  A <> B -> WFInsn (Choreography.Insn.EPR A x B y)
| WFLet : forall A x e, WFInsn (Choreography.Insn.Let A x e)
| WFLetBang : forall A x e, WFInsn (Choreography.Insn.LetBang A x e)
| WFLetPair : forall A x1 x2 e, WFInsn (Choreography.Insn.LetPair A x1 x2 e)
.
Inductive WFChoreography : Choreography.t -> Prop :=
| WFNil : WFChoreography []
| WFCons : forall I C,
  WFInsn I -> WFChoreography C -> WFChoreography (I :: C).

(*
Lemma add_ok_inversion : forall A ls,
  Actor.FSet.MSet.Raw.Ok (A :: ls) ->
  ~ SetoidList.InA eq A ls /\ Actor.FSet.MSet.Raw.Ok ls.
Proof.
  intros A ls H.
  split.
  {
    apply Actor.FSet.MSet.Raw.elements_spec2w in H.
    inversion H; auto.
  }
  unfold Actor.FSet.MSet.Raw.Ok in *.
  simpl in H.
  destruct (Actor.FSet.MSet.Raw.isok ls); auto.
  rewrite Bool.andb_false_r in H.
  discriminate.
Qed.


Lemma forallb_true : forall A (ls : list A) f,
    (forall x, List.In x ls -> f x = true) ->
    List.forallb f ls = true.
Admitted.

Lemma removeA_not_in : forall (A : Actor.t) (ls : list Actor.t),
  ~ List.In A ls ->
  SetoidList.removeA Actor.eq_dec A ls = ls.
Admitted.
Lemma lts_not_in : forall A B ls,
  Actor.FSet.MSet.Raw.Ok (B :: ls) ->
  OrderedTypeEx.String_as_OT.lts A B ->
  ~ List.In A ls.
Admitted.
*)



Lemma EPP_cons : forall A I C PA,
  WFInsn I ->
  EPP A (I :: C) PA <->
  exists PA', PA = eppI A I ++ PA' /\ EPP A C PA'.
Proof.
  intros A I C PA HI. split.
  * intros  HEPPA.
    inversion HEPPA; subst; clear HEPPA;
    simpl; Actor.simplify; simpl;
    try (eexists; split; eauto; fail).
    rewrite eppI_disjoint; auto. simpl.
    eexists. split; eauto.
  * intros [PA' [? HEPPA]]; subst.
    destruct (Actor.Map.FSetProofs.in_dec A (Choreography.Insn.actors I))
      as [Hin | Hin].
    2:{
      rewrite eppI_disjoint; auto.
      simpl.
      apply EPP_disjoint; auto.
    }
    inversion HI; subst; clear HI; simpl in *;
      Actor.simplify; simpl;
      try(constructor; auto; fail).
    destruct Hin; subst; try contradiction.
    destruct Hin; subst; try contradiction.
Qed.

(*
Lemma in_map_dec : forall {T} (A : Actor.t) (M : Actor.Map.t T),
  { Actor.Map.In A M } + { ~ Actor.Map.In A M }.
Admitted.

Lemma mapsto_dec : forall {T} (A : Actor.t) (M : Actor.Map.t T),
  { v : T & Actor.Map.MapsTo A v M } + { ~ Actor.Map.In A M }.
Admitted.
*)



(*
Definition uncons D (N : Network.t) : Process.t :=
  match Actor.Map.find D N with
  | Some (_ :: PD') => PD'
  | _ => []
  end.
Definition add_option {T} x (a : option T) (m : Actor.Map.t T) : Actor.Map.t T :=
  match a with
  | Some v => Actor.Map.add x v m
  | None => m
  end.
Definition unconsN I (N : Network.t) : Network.t :=
  match I with
  | Choreography.Insn.Send A _ B _
  | Choreography.Insn.EPR A _ B _ =>
    match Actor.Map.find A N, Actor.Map.find B N with
    |

    | Some (_ :: PA), Some (_ :: PB) =>
      Actor.Map.add A PA (Actor.Map.add B PB N)
    | None, _ | _, None => N
    end

    (*add_option A (uncons A N) (add_option B (uncons B N) N)*)
  | Choreography.Insn.Let A _ _
  | Choreography.Insn.LetBang A _ _
  | Choreography.Insn.LetPair A _ _ _ =>
    (*add_option A (uncons A N) N*)
      match Actor.Map.find A N with
      | Some (_ :: PA) => Actor.Map.add A PA N
      | _ => N
      end
  end.


Lemma unconsN_domain : forall A I (N : Network.t),
  WFInsn I ->
  Actor.Map.In A (unconsN I N) <->
  Actor.Map.In A N.
Proof.
  intros D I N Hwf.
  inversion Hwf; subst; clear Hwf; simpl;
    try (destruct (Actor.Map.find A N) as [[ | IA PA] | ] eqn:HA;
      [ reflexivity | | reflexivity ]);
    try (destruct (Actor.Map.find B N) as [[ | IB PP] | ] eqn:HB;
      [ reflexivity | | reflexivity ]);
    Actor.simplify;
    split; auto;
    try (intros [? | [? | ?]]; auto; subst; Actor.solve; fail);
    try (intros [? | ?]; auto; subst; Actor.solve; fail).
Qed.

Lemma unconsN_spec : forall A I (P : Process.t) (N : Network.t),
  WFInsn I ->
  Actor.Map.In A N ->
  Actor.Map.MapsTo A P (unconsN I N) <->
  Actor.Map.MapsTo A (eppI A I ++ P) N.
Proof.
  intros D I PD N HWF Hin.
  inversion HWF; subst; clear HWF; simpl.
  * Actor.reflect_find.
  
  
  try (destruct (Actor.Map.find A N) as [[ | IA PA] | ] eqn:HA).
      [ reflexivity | | reflexivity ]);
    try (destruct (Actor.Map.find B N) as [[ | IB PP] | ] eqn:HB;
      [ reflexivity | | reflexivity ]).
  Actor.simplify.
  intuition.

Lemma unconsN_spec : forall C I N,
  EPP_N C (unconsN I N) <->
  (forall A PA,
    Actor.Map.MapsTo A PA N ->
    EPP A (I :: C) (eppI A I ++ PA)).
Admitted.

Inductive EPP_N_ : Choreography.t -> Network.t -> Prop :=
| EPP_N_nil : forall N,
  (forall A PA, Actor.Map.MapsTo A PA N -> PA = []) ->
  EPP_N_ [] N
| EPP_N_Send : forall I C N N',
  EPP_N_ C N ->
  WFInsn I ->

  (forall A,
    Actor.Map.In A N <->
    Actor.Map.In A N'
  ) ->
  (forall A PA,
    Actor.Map.MapsTo A PA N <->
    Actor.Map.MapsTo A (eppI A I ++ PA) N'
  ) ->

  EPP_N_ (I :: C) N'
.

Lemma EPP_N_uncons : forall I C N',
  EPP_N_ (I :: C) N' <-> EPP_N_ C (unconsN I N').
Proof.
  intros.
  split.
  * intros H.
    inversion H; subst; clear H.
    inversion H3; subst; clear H3; simpl.
    + replace (add_option A (uncons A N') (add_option B (uncons B N') N')) 
        with N; auto.
      admit.
    + replace (add_option A (uncons A N') (add_option B (uncons B N') N')) 
        with N; auto.
      admit.
    + replace (add_option A (uncons A N') N')
        with N; auto.
      admit.
    + replace (add_option A (uncons A N') N')
        with N; auto.
      admit.
    + replace (add_option A (uncons A N') N')
        with N; auto.
      admit.
  * intros H.
    econstructor; eauto.
    { admit. }
    + admit (* lemma *) .
    + admit (* lemma *) .
Admitted.

Lemma EPP_N__spec : forall C N,
  EPP_N_ C N <->
  forall D PD, Actor.Map.MapsTo D PD N -> EPP D C PD.
Proof.
  intros C N. split.
  * intros HEPP_N.
    induction HEPP_N as [ | ? ? ? ? IH ? Hwf Hdom Hmapsto];
      intros D PD HD.
    { apply H in HD; subst. constructor. }
    apply EPP_cons; auto.
    destruct (mapsto_dec D N) as [[PD' HPD'] | HPD'].
    2:{
      exfalso.
      rewrite Hdom in HPD'.
      apply HPD'.
      exists PD; auto.
    }
    exists PD'.
    split.
    2:{ apply IHHEPP_N; auto. }
    eapply Actor.Map.Properties.F.MapsTo_fun; eauto.
    apply Hmapsto; auto.
  * revert N. induction C as [ | I C]; intros N H.
    + constructor.
      intros D PD HD.
      apply H in HD.
      inversion HD; subst; auto.
    + apply EPP_N_uncons.
      apply IHC; intros D PD HD.
      Search unconsN.

      apply (EPP_N_Send I C (unconsN I N) N).
      2:{ admit. }
      {
        eapply IHC.
        intros D PD HD.
        specialize (H D PD HD).
        rewrite EPP_cons in H.
        2:{ admit. }
        destruct H as [PD' [? HD']]; subst.
        auto.
      }
    
    }
  
  intros Hmapsto.
Qed.
*)

Lemma EPP_N_eq : forall N1 N2 C,
  Actor.Map.Equal N1 N2 ->
  EPP_N C N1 ->
  EPP_N C N2.
Proof.
  intros N1 N2 C Heq H1. revert N2 Heq.
  induction H1; intros N2 Heq.
  * apply EPP_N_empty.
    rewrite <- Heq; auto.
  * rewrite Heq in *.
    eapply EPP_N_add; eauto.
    apply IHEPP_N.
    Actor.simplify.
Qed.

Global Instance EPP_N_Proper :
  Proper (eq ==> Actor.Map.Equal ==> iff) EPP_N.
Proof.
  intros ? C ? N1 N2 HN; subst.
  split; intros;
    eapply EPP_N_eq; eauto.
  symmetry; auto.
Qed.

Lemma EPP_N_spec : forall C N,
  EPP_N C N <->
  forall D PD, Actor.Map.MapsTo D PD N -> EPP D C PD.
Proof.
  intros C N.
  split; intros H.
  * induction H.
    { intros D PD Hmapsto.
      apply H in Hmapsto. contradiction.
    }
    intros D PD Hmapsto.
    compare D A.
    { (* D = A *)
      replace PD with PA; auto.
      {
        Actor.solve. congruence.
      }
    }
    { (* D <> A *)
      apply IHEPP_N.
      Actor.simplify.
    }

  * induction N using Actor.Map.Properties.map_induction.
    { apply EPP_N_empty; auto. }
    rename x into A, e into PA.
    Actor.simplify.
    About EPP_N_add.
    apply (EPP_N_add C A PA).
    { Actor.simplify. }
    { apply H. Actor.simplify. }

    Actor.simplify.
    rewrite Actor.Map.Proofs.remove_not_in; auto.
    apply IHN1; auto.
    {
      intros D PD Hmaps.
      apply H.
      Actor.simplify.
      compare A D.
      {
        exfalso. Actor.solve.
      }
      right. split; auto.
    }
Qed.

Lemma EPP_disjoint_inversion : forall A I C P,
  EPP A (I :: C) P ->
  ~ Actor.FSet.In A (Choreography.Insn.actors I) ->
  EPP A C P.
Proof.
  intros A I C P HP Hin.
  inversion HP; subst; clear HP;
  simpl in Hin; Actor.simplify.
Qed.


Lemma EPP_N_cons : forall I C N ,
  EPP_N (I :: C) N <->
  (forall A PA,
    Actor.FSet.In A (Choreography.Insn.actors I) ->
    Actor.Map.MapsTo A PA N ->
    EPP A (I :: C) PA
  ) /\
  EPP_N C (setminus (Choreography.Insn.actors I) N).
Proof.
  intros I C N.
  split.
  * intros HEPP_N.
    rewrite EPP_N_spec in HEPP_N.
    split.
    + intros A PA Hin Hmapsto.
      apply HEPP_N; auto.
    + apply EPP_N_spec.
      intros D PD Hmapsto.
      Actor.simplify.
      eapply EPP_disjoint_inversion; eauto.
  * intros [HA HC].
    rewrite EPP_N_spec in *.
    intros D PD Hmapsto.
    destruct (Actor.Map.FSetProofs.in_dec D (Choreography.Insn.actors I))
      as [Hin | Hin].
    + apply HA; auto.
    + apply EPP_disjoint; auto.
      apply HC; auto.
      Actor.simplify.
Qed.

(* Correctness of EPP *)

Theorem soundness : forall C C' refs cfg refs' cfg' l N,

    Choreography.step C refs cfg l C' refs' cfg' ->
    EPP_N C N ->
    exists N', EPP_N C'  N' /\
               Network.step N refs cfg l N' refs' cfg'.
Admitted.

Require Import Stdlib.Program.Equality.

Lemma actors_subst : forall I B x v,
  Actor.FSet.Equal
    (Choreography.Insn.actors (Choreography.Insn.subst B x v I))
    (Choreography.Insn.actors I).
Proof.
  destruct I; intros; Actor.simplify.
Qed.

Lemma bind_eqb_equiv : forall p1 p2,
  Choreography.Insn.bind_eqb p1 p2 =
    if Actor.eq_dec (fst p1) (fst p2)
    then if Var.eq_dec (snd p1) (snd p2)
    then true
    else false
    else false.
Proof.
  intros [A x] [B y].
  unfold Choreography.Insn.bind_eqb, Choreography.Insn.bind_eq_dec; simpl.
  Actor.simplify.
  Var.simplify.
Qed.
#[global] Hint Rewrite bind_eqb_equiv : var_db.

Lemma EPP_subst_neq : forall C A P B x v,
    A <> B ->
    EPP A C P ->
    EPP A (Choreography.subst B x v C) P.
Proof.
  induction C as [ | I C];
    intros ? ? ? ? ? Hneq H.
  { inversion H; subst; constructor. }
  inversion H; subst; clear H; simpl;
    try (
    autorewrite with var_db;
    repeat reduce_eq_dec;
    repeat Var.Map.Tactics.reduce_eq_dec;
    simpl;
    constructor; auto; fail).

  apply EPP_disjoint.
  { rewrite actors_subst; auto. }
  destruct (Choreography.Insn.rebound_in B x I) eqn:HI; auto.
Qed.

Lemma EPP_subst_neq_bwd : forall C A P B x v,
    A <> B ->
    EPP A (Choreography.subst B x v C) P ->
    EPP A C P.
Proof.
  intros C A P B x v Hneq.
  revert P.
  induction C as [ | I C]; 
    intros P Hepp; simpl; auto.
  assert (Hdec : Actor.FSet.In A (Choreography.Insn.actors I) 
        \/ ~ Actor.FSet.In A (Choreography.Insn.actors I)).
  {
    destruct I; simpl; Var.simplify.
  }
  destruct Hdec as [Hin | Hin].
  2:{
    apply EPP_disjoint; auto.
    simpl in *.
    apply EPP_disjoint_inversion in Hepp.
    destruct (Choreography.Insn.rebound_in B x I) eqn:HB; auto.
    rewrite actors_subst; auto.
  }

  destruct I as 
    [A0 v0 B0 | A0 x0 B0 y0 | A0 x0 v0 | A0 x0 v0 | A0 x0 y0 v0];
    simpl in *.
  * simpl in Hin. autorewrite with actor_db in Hin.
    destruct Hin; subst.
    + (* A = A0 *)
      inversion Hepp; subst; clear Hepp;
      simpl in *; Actor.simplify;
      constructor; auto.
      Var.simplify; simpl in *; Actor.simplify.
    + (* A = B0 *)
      inversion Hepp; subst; clear Hepp;
      Var.simplify; simpl in *; Actor.simplify;
      constructor; auto.
  * autorewrite with var_db in Hepp; simpl in Hepp.
    autorewrite with actor_db in Hin.
    destruct Hin; subst.
    + (* A = A0 *)
      inversion Hepp; subst; clear Hepp;
      simpl in *; Actor.simplify;
      constructor; auto.
      Var.simplify.
    + (* A = B0 *)
      inversion Hepp; subst; clear Hepp;
      simpl in *; Actor.simplify;
      constructor; auto.
      Var.simplify.

  * autorewrite with var_db in Hepp; simpl in *.
    autorewrite with actor_db in Hin. subst.
  
      inversion Hepp; subst; clear Hepp;
      simpl in *; Actor.simplify;
      constructor; auto.
  * autorewrite with var_db in Hepp; simpl in *.
    autorewrite with actor_db in Hin. subst.
  
      inversion Hepp; subst; clear Hepp;
      simpl in *; Actor.simplify;
      constructor; auto.
  * autorewrite with var_db in Hepp; simpl in *.
    autorewrite with actor_db in Hin. subst.
  
      inversion Hepp; subst; clear Hepp;
      simpl in *; Actor.simplify;
      constructor; auto.
Qed. 


Lemma subst_not_in_I : forall I A x v,
  ~ Actor.FSet.In A (Choreography.Insn.actors I) ->
  Choreography.Insn.subst A x v I = I.
Proof.
  destruct I; intros; simpl in *; Actor.simplify.
Qed.
Lemma rebound_not_in_I : forall I A x,
  ~ Actor.FSet.In A (Choreography.Insn.actors I) ->
  Choreography.Insn.rebound_in A x I = false.
Proof.
  destruct I; intros; simpl in *;
    autorewrite with var_db; simpl;
    Actor.simplify.    
Qed.


Lemma EPP_subst_eq : forall A C P x v,
    EPP A C P ->
    EPP A (Choreography.subst A x v C) (Process.subst x v P).
Proof.
  intros ? ? ? ? ? H.
  induction H; subst; simpl;
    try (constructor; fail);
    autorewrite with var_db; simpl;
    Actor.simplify;
    Var.simplify;
    simpl in *; subst;
    try (constructor; auto; fail).

  rewrite subst_not_in_I; auto.
  rewrite rebound_not_in_I; auto.
  apply EPP_disjoint; auto.
Qed.


Lemma EPP_subst_eq_bwd : forall A x v C P',
  EPP A (Choreography.subst A x v C) P' ->
  exists P, EPP A C P /\ P' = Process.subst x v P.
Proof.
  intros A x v C.
  induction C as [ | I C];
    intros P' H;
    simpl in *.
  {
    inversion H; subst.
    exists []. split; auto.
  }
    assert (Hdec : Actor.FSet.In A (Choreography.Insn.actors I) 
        \/ ~ Actor.FSet.In A (Choreography.Insn.actors I)).
  {
    destruct I; simpl; Var.simplify.
  }
  destruct Hdec as [Hin | Hin].
  2:{
    apply EPP_disjoint_inversion in H; auto.
    2:{ rewrite actors_subst; auto. }
    rewrite rebound_not_in_I in H; auto.
    apply IHC in H.
    destruct H as [P [H ?]]; subst.
    exists P; split; auto.
    apply EPP_disjoint; auto.
  }

  destruct I as 
    [A0 v0 B0 y0 | A0 x0 B0 y0 | A0 x0 v0 | A0 x0 v0 | A0 x0 y0 v0];
    simpl in *;
    autorewrite with var_db in *;
    simpl in *.

  * autorewrite with actor_db in Hin.
    inversion H; subst; clear H.

    + (* A = A0 *)
      Actor.simplify.
      edestruct (IHC P) as [P0 [H0 ?]]; eauto; subst.
      exists (Insn.Send v0 B0 :: P0).
      split; auto.
      constructor; auto.

    + (* A = B0 *)
      Actor.simplify.
      Var.Map.Tactics.compare x y0.
      - (* x = y0 *)
        exists (Insn.Receive x A0 :: P).
        simpl. Var.simplify.
        split; auto.
        constructor; auto.
      
      - (* x <> y0 *)
        edestruct (IHC P) as [P0 [H0 ?]]; eauto; subst.
        exists (Insn.Receive y0 A0 :: P0).
        simpl. Var.simplify.
        split; auto.
        constructor; auto.

    + (* A <> A0 /\ B <> B0 *)
      (* contradicts Hin *)
      simpl in *. Actor.simplify.
      destruct Hin; subst; contradiction.

  * (* EPR *) 
    autorewrite with actor_db in Hin.
    inversion H; subst; clear H.

    + (* A = A0 *)
      Actor.simplify.
      Var.Map.Tactics.compare x x0.
      - (* x = y0 *)
        exists (Insn.EPR x B0 :: P).
        simpl in *. Var.simplify.
        split; auto.
        constructor; auto.

      - (* x <> x0 *)
        edestruct (IHC P) as [P0 [H0 ?]]; eauto; subst.
        exists (Insn.EPR x0 B0 :: P0).
        simpl in *. Var.simplify.
        split; auto.
        constructor; auto.

    + (* A = B0 *)
      Actor.simplify. simpl in *.
      Var.Map.Tactics.compare x y0.
      - (* x = y0 *)
        exists (Insn.EPR x A0 :: P).
        simpl. Var.simplify.
        split; auto.
        constructor; auto.
      
      - (* x <> y0 *)
        edestruct (IHC P) as [P0 [H0 ?]]; eauto; subst.
        exists (Insn.EPR y0 A0 :: P0).
        simpl. Var.simplify.
        split; auto.
        constructor; auto.

    + (* A <> A0 /\ B <> B0 *)
      (* contradicts Hin *)
      simpl in *. Actor.simplify.
      destruct Hin; subst; contradiction.

  * (* Let *)
    autorewrite with actor_db in Hin. subst.
    Actor.simplify.
    inversion H; subst; clear H.
    2:{ simpl in *. Actor.simplify. }

    Var.Map.Tactics.compare x x0.
    + (* x = x0 *)
      exists (Insn.Let x v0 :: P).
      simpl. Var.simplify.
      split; auto.
      constructor; auto.

    + (* x <> x0 *)
      edestruct (IHC P) as [P0 [H0 ?]]; eauto; subst.
      exists (Insn.Let x0 v0 :: P0).
      simpl; Var.simplify.
      split; auto.
      constructor; auto.


  * (* LetBang *)
    autorewrite with actor_db in Hin. subst.
    Actor.simplify.
    inversion H; subst; clear H.
    2:{ simpl in *. Actor.simplify. }

    Var.Map.Tactics.compare x x0.
    + (* x = x0 *)
      exists (Insn.LetBang x v0 :: P).
      simpl. Var.simplify.
      split; auto.
      constructor; auto.

    + (* x <> x0 *)
      edestruct (IHC P) as [P0 [H0 ?]]; eauto; subst.
      exists (Insn.LetBang x0 v0 :: P0).
      simpl; Var.simplify.
      split; auto.
      constructor; auto.

  
  * (* LetPair *)
    autorewrite with actor_db in Hin. subst.
    Actor.simplify.
    inversion H; subst; clear H.
    2:{ simpl in *. Actor.simplify. }

    Var.Map.Tactics.compare x x0;
      [ | Var.Map.Tactics.compare x y0 ].
    + (* x = x0 *)
      exists (Insn.LetPair x y0 v0 :: P).
      simpl in *. Var.simplify.
      split; auto.
      constructor; auto.

    + (* x = y0 *)
      exists (Insn.LetPair x0 x v0 :: P).
      simpl in *. Var.simplify.
      split; auto.
      constructor; auto.

    + (* x <> x0 /\ x <> y0 *)
      edestruct (IHC P) as [P0 [H0 ?]]; eauto; subst.
      exists (Insn.LetPair x0 y0 v0 :: P0).
      simpl; Var.simplify.
      split; auto.
      constructor; auto.
Qed.


Lemma EPP_subst_iff : forall C D PD A x v,
    EPP D (Choreography.subst A x v C) PD <->
    (D = A /\ exists PD0,
                EPP D C PD0 
                /\ PD = Process.subst x v PD0)
    \/
    (D <> A /\ EPP D C PD).
Proof.
  intros.
  split; intros H.
  * compare A D.
    + left. split; auto.
      apply EPP_subst_eq_bwd; auto.
    + right. split; auto.
      eapply EPP_subst_neq_bwd; eauto.
  * destruct H as [[? [PD0 [HPD0 ?]]] | [? HPD]]; subst.
    + apply EPP_subst_eq; auto.
    + apply EPP_subst_neq; auto. 
Qed.



(*
Definition insn_matches_label (I : Choreography.Insn.t) (l : Label.t) : bool :=
  match I, l with
  | Choreography.Insn.Send A _ B _, Label.Send A' _ B'
  | Choreography.Insn.EPR A _ B _, Label.EPR A' B' =>
    if Actor.eq_dec A A'
    then if Actor.eq_dec B B' then true else false
    else false
  | Choreography.Insn.Let A _ _, Label.Loc A'
  | Choreography.Insn.LetBang A _ _, Label.Loc A'
  | Choreography.Insn.LetPair A _ _ _, Label.Loc A' =>
    if Actor.eq_dec A A' then true else false

  | _, _ => false
  end.

(** Return the choreography C' such that C, refs -l-> C', refs'
  * if such a choreography exists.
  *)
Inductive step_label : Choreography.t -> ChorEnv.t nat ->
                       Label.t ->
                       Choreography.t -> Prop :=

| StepSend : forall A v B x C refs A' v' B' C',
  A = A' ->
  B = B' ->
  v = v' ->
  Expr.Val v ->
  C' = Choreography.subst B x v C ->
  step_label  (Choreography.Insn.Send A v B x :: C)
              refs
              (Label.Send A' v' B')
              C'

| StepEPR : forall q1 q2 A x B y C refs A' B' C',
  A = A' ->
  B = B' ->
  q1 = Var.fresh (ChorEnv.find A refs) ->
  q2 = Var.fresh (Var.Map.add x q1 (ChorEnv.find A refs)) ->

  C' = Choreography.subst A x (Expr.Var q1)
        (Choreography.subst B y (Expr.Var q2)
        C) ->

  step_label  (Choreography.Insn.EPR A x B y :: C)
              refs
              (Label.EPR A' B')
              C'

| StepLet :forall A x v C refs A' C',
  A = A' ->
  C' = Choreography.subst A x v C ->
  step_label (Choreography.Insn.Let A x v :: C)
             refs
             (Label.Loc A')
             C'

| StepLetBang : forall A x v' C refs A' C',
  A = A' ->
  C' = Choreography.subst A x v' C ->
  step_label (Choreography.Insn.LetBang A x (Expr.Bang v') :: C)
             refs
             (Label.Loc A')
             C'

| StepLetPair : forall A x1 x2 v1 v2 C refs A' C',
  A = A' ->
  C' = Choreography.subst A x1 v1 (Choreography.subst A x2 v2 C) ->
  step_label (Choreography.Insn.LetPair A x1 x2 (Expr.Pair v1 v2) :: C)
             refs
             (Label.Loc A')
             C'

| StepCons : forall I C refs l C',
  Actor.FSet.Empty
    (Actor.FSet.inter (Choreography.Label.actors l)
                      (Choreography.Insn.actors I)) ->
  step_label C refs l C' ->
  step_label (I :: C) refs l (I :: C')
.
*)

(*
Fixpoint step_label l (refs : Var.Map.t nat) C :=
  match C with
  | [] => []
  | I0 :: C' =>

    match I0 with

    | Choreography.Insn.Send A v B y =>
      if insn_matches_label I0 l
      then Choreography.subst B y v C'
      else I0 :: step_label l refs C'

    | Choreography.Insn.EPR A x B y =>
      let q1 := Var.fresh refs in
      let refs' := Var.Map.add x q1 refs in
      let q2 := Var.fresh refs' in
      let refs'' := Var.Map.add y q2 refs' in

      if insn_matches_label I0 l
      then  Choreography.subst A x (Expr.Var q1)
            (Choreography.subst B y (Expr.Var q2)
            C')
      else I0 :: step_label l refs'' C'

    | Choreography.Insn.Let A x v =>
      if insn_matches_label I0 l
      then Choreography.subst A x v C'
      else I0 :: step_label l refs C'

    | Choreography.Insn.LetBang A x (Expr.Bang v') =>
      if insn_matches_label I0 l
      then Choreography.subst A x v' C'
      else I0 :: step_label l refs C'

    | Choreography.Insn.LetPair A x1 x2 (Expr.Pair v1 v2) =>
      if insn_matches_label I0 l
      then Choreography.subst A x1 v1
          (Choreography.subst A x2 v2 C')
      else I0 :: step_label l refs C'

    | _ => I0 :: step_label l refs C'

    end
  end.
  *)

(*
(** Return the choreography C' such that C -(Send A v B y)-> C' *)
Fixpoint step_send A B (C : Choreography.t) : Choreography.t :=
    match C with
    | [] => []
    | Choreography.Insn.Send A0 v0 B0 y0 :: C' =>
        match Actor.eq_dec A A0, Actor.eq_dec B B0 with
        | left _, left _ => Choreography.subst B0 y0 v0 C'
        | _, _ => Choreography.Insn.Send A0 v0 B0 y0 :: (step_send A B C')
        end
    | I' :: C' => I' :: step_send A B C'
    end.
  *)

(*
(* Can take a step with label l *)
Inductive Ready : Choreography.t -> ChorEnv.t nat -> Config.t -> Label.t -> Prop := .
Lemma ready_spec : forall C refs cfg l,
  Ready C refs cfg l ->
  exists C' refs' cfg',
    Choreography.step C refs cfg l C' refs' cfg'.
Admitted.

Lemma step_ready : forall N refs cfg l N' refs' cfg' C,
  Network.step N refs cfg l N' refs' cfg' ->
  EPP_N C N ->
  Ready C refs cfg l.
Admitted.

Lemma EPP_N_step_deterministic :
  forall C N refs cfg l C' refs' cfg' N' refs'' cfg'',
  EPP_N C N ->
  Choreography.step C refs cfg l C' refs' cfg' ->
  Network.step N refs cfg l N' refs'' cfg'' ->
  ChorEnv.Equal refs' refs''
  /\
  cfg' = cfg'
  /\
  EPP_N C' N'.
Proof.
  intros C N refs cfg l C' refs' cfg' N' refs'' cfg''.
  intros HEPP_N HstepC HstepN.
  inversion HstepC; subst; clear HstepC.
  * (* SendC *)
    inversion HstepN; subst; clear HstepN.
    admit (* need a version for steps of processes *).
  * (* Send A v B *)
    inversion HstepN; subst; clear HstepN.
    split; auto. admit (*reflexivity.*).
    split; auto.
    apply EPP_N_spec.
    rewrite EPP_N_spec in HEPP_N.
    intros D PD Hmapsto.
    Actor.simplify.
    destruct Hmapsto as [[? ?] | [? [[? ?] | [? Hmapsto]]]];
      subst.
    + (* A = D *)
      apply EPP_subst_neq; auto.
      apply HEPP_N in H4.
      inversion H4; subst; clear H4; auto.
      { simpl in *; Actor.simplify. }
    + (* B = D *)
      apply HEPP_N in H8.
      inversion H8; subst; clear H8.
      apply EPP_subst_eq; auto.
      { simpl in *; Actor.simplify. }
    + (* A <> D /\ B <> D *)
      apply EPP_subst_neq; auto.
      apply HEPP_N in Hmapsto.
      apply EPP_disjoint_inversion in Hmapsto; auto.
      { simpl; Actor.simplify. }


  * admit.
  * (* Let *) admit.
Admitted. 
*)




  

(*
Definition uncons D (N : Network.t) : option Process.t :=
  match Actor.Map.find D N with
  | Some (_ :: PD') => Some PD'
  | _ => None
  end.
Definition add_option {T} x (a : option T) (m : Actor.Map.t T) : Actor.Map.t T :=
  match a with
  | Some v => Actor.Map.add x v m
  | None => m
  end.
Definition unconsN I (N : Network.t) :=
  match I with
  | Choreography.Insn.Send A _ B _
  | Choreography.Insn.EPR A _ B _ =>
    add_option A (uncons A N) (add_option B (uncons B N) N)
  | Choreography.Insn.Let A _ _
  | Choreography.Insn.LetBang A _ _
  | Choreography.Insn.LetPair A _ _ _ =>
    add_option A (uncons A N) N
  end.
*)

(*
Lemma uncons_mapsto : forall D PD I N,
  EPP_N (I :: C) N ->
  Actor.Map.MapsTo D PD (unconsN I N)
  <->
  Actor.Map.MapsTo D (eppI D I ++ PD) N.
Proof.
  intros D PD I N.
  destruct I as [A e B x | | | | ].
  + simpl. compare D A; compare D B; Actor.simplify.
    - repeat rewrite Actor.Map.Properties.F.find_mapsto_iff.
      unfold add_option.
      unfold uncons.
      destruct (Actor.Map.find D N) as [ [ | PD' ]| ] eqn:HD.
      simpl. repeat rewrite HD. unfold Process.t in HD.
      rewrite HD.
      admit (* false *).

      Actor.simplify.
      unfold Process.t in HD. rewrite HD.
    - 

      

      transitivity (uncons D N = PD); [ intuition | ].
      unfold uncons.
      destruct (Actor.Map.find D N) eqn:Hfind.
      2:{ }
Admitted.
Hint Rewrite uncons_mapsto : actor_db.
*)

(*
Lemma EPP_N_cons : forall I C N,
  EPP_N (I :: C) N <->
  EPP_N C (unconsN I N)
  /\ (forall A PA,
      Actor.FSet.In A (Choreography.Insn.actors I) ->
      Actor.Map.MapsTo A PA (unconsN I N) <->
      Actor.Map.MapsTo A (eppI A I ++ PA) N
      ).
Proof.
  intros I C N.
  split.
  * 
    intros HEPP_N.
    split.
    + rewrite EPP_N_spec in *.
      intros D PD Hmapsto.
      admit.
    + intros D PD Hin. 
      rewrite EPP_N_spec in *.
      admit.
  * intros [HEPP_N Hin].
    rewrite EPP_N_spec in *.
    intros D PD Hmapsto.
    admit.
    (*
    Actor.simplify.
    apply HEPP_N in Hmapsto.

    inversion Hmapsto; subst; Actor.simplify;
        simpl in *;
      try match goal with
      | [ H : _ :: _ = _ :: PD |- _ ] =>
        inversion H; subst; clear H; auto
      end.
    rewrite eppI_disjoint in *; auto.
    *)
Admitted.
*)



(*
Lemma EPP_N_cons_1 : forall C I A N,
  Actor.FSet.Equal
    (Choreography.Insn.actors I)
    (Actor.FSet.singleton A)
    ->
  EPP_N (I :: C) N
  <->
  (forall PA,
    Actor.Map.MapsTo A PA N ->
    EPP A (I :: C) PA)
  /\
  EPP_N C (Actor.Map.remove A N).
Admitted.
Lemma EPP_N_cons_2 : forall C I A B N,
  Actor.FSet.Equal
    (Choreography.Insn.actors I)
    (Actor.FSet.add A (Actor.FSet.singleton B))
    ->
  EPP_N (I :: C) N
  <->
  (forall PA,
    Actor.Map.MapsTo A PA N ->
    EPP A (I :: C) PA)
  /\
  (forall PB,
    Actor.Map.MapsTo B PB N ->
    EPP B (I :: C) PB)
  /\
  EPP_N C (Actor.Map.remove B (Actor.Map.remove A N)).
Admitted.

Ltac EPP_N_cons :=
  match goal with
  | [H : EPP_N (Choreography.Insn.Send _ _ _ _ :: _) _ |- _] =>
    let HA := fresh "HA" in
    let HB := fresh "HB" in
    rewrite EPP_N_cons_2 in H; [ | simpl; reflexivity];
    destruct H as [HA [HB H]]
  | [H : EPP_N (Choreography.Insn.EPR _ _ _ _ :: _) _ |- _] =>
    let HA := fresh "HA" in
    let HB := fresh "HB" in
    rewrite EPP_N_cons_2 in H; [ | simpl; reflexivity];
    destruct H as [HA [HB H]]
  | [ H : EPP_N (_ :: _) _ |- _ ] =>
    let HA := fresh "HA" in
    rewrite EPP_N_cons_1 in H; [ | simpl; reflexivity];
    destruct H as [HA H]
  | [ |- EPP_N (Choreography.Insn.Send ?A _ ?B _ :: _) _ ] =>
    eapply EPP_N_cons_2; [ simpl; reflexivity | ];
    let HA := fresh "HA" in
    let HB := fresh "HB" in
    repeat split; [intros ? HA | intros ? HB | ]; Actor.simplify
  | [ |- EPP_N (Choreography.Insn.EPR _ _ _ _ :: _) _ ] =>
    eapply EPP_N_cons_2; [ simpl; reflexivity | ];
    let HA := fresh "HA" in
    let HB := fresh "HB" in
    repeat split; [intros ? HA | intros ? HB | ]; Actor.simplify
  | [ |- EPP_N (_ :: _) _ ] =>
    eapply EPP_N_cons_1; [ simpl; reflexivity | ];
    let HA := fresh "HA" in
    repeat split; [intros ? HA | ]; Actor.simplify
  end.
  *)

Ltac EPP_N_cons :=
  match goal with
  | [H : EPP_N (_ :: _) _ |- _] =>
    rewrite EPP_N_cons in H;
    simpl in H; Actor.simplify
  | [ |- EPP_N (_ :: _) _ ] =>
    eapply EPP_N_cons;
    repeat split; intros; simpl; Actor.simplify
  end.

Lemma EPP_N_subst_neq : forall A x e C N,
  ~ Actor.Map.In A N ->
  EPP_N (Choreography.subst A x e C) N
  <->
  EPP_N C N.
Proof.
  intros.
  repeat rewrite EPP_N_spec.
  apply Modulus.forall_iff. intros D.
  apply Modulus.forall_iff. intros PD.
  apply Modulus.forall_iff. intros Hmapsto.
  rewrite EPP_subst_iff.
  assert (D <> A).
  {
    inversion 1; subst.
    apply H. exists PD; auto.
  }
  intuition.
Qed.

Global Instance chor_step_proper : Proper (eq ==> ChorEnv.Equal ==> eq ==> eq ==> eq ==> ChorEnv.Equal ==> eq ==> iff) (Choreography.step).
Admitted.

Lemma EPP_N_weakening : forall C N N',
  (forall A PA, Actor.Map.MapsTo A PA N' -> Actor.Map.MapsTo A PA N) ->
  EPP_N C N ->
  EPP_N C N'.
Admitted.

Lemma EPP_N_remove : forall C A N,
  EPP_N C N -> 
  EPP_N C (Actor.Map.remove A N).
Proof.
  intros.
  rewrite EPP_N_spec in *.
  intros D PD Hmapsto.
  Actor.simplify.
Qed.

Lemma subst_comm : forall A B x y v v' C,
  A <> B \/ x <> y ->
  Choreography.subst A x v (Choreography.subst B y v' C)
  = Choreography.subst B y v' (Choreography.subst A x v C).
Admitted.
Require Import Setoid.



Definition uncons A (N : Network.t) :=
  match Actor.Map.find A N with
  | Some (_ :: P) => Actor.Map.add A P N
  | _ => Actor.Map.remove A N
  end.

Lemma uncons_neq : forall A B PB N,
  A <> B ->
  Actor.Map.MapsTo B PB (uncons A N) <-> Actor.Map.MapsTo B PB N.
Proof.
  intros A B PB N Hneq.
  unfold uncons.
  destruct (Actor.Map.find A N) as [[ | IA PA] | ] eqn:Hfind;
    Actor.simplify.
Qed.
  


  (*Actor.FSet.MSet.Raw.elements_spec2w*)
  (*Actor.Map.S.MSet.Raw.isok_iff*)

(*
(* relies on being a list implementation of fset *)
Lemma fset_induction :
  forall (P : Actor.FSet.t -> Prop),
  (Proper (Actor.FSet.Equal ==> iff) P) ->
  P (Actor.FSet.empty) ->
  (forall A X, ~ Actor.FSet.In A X -> P X -> P (Actor.FSet.add A X)) ->
  (forall X, P X).
Proof.
  intros P Hproper Hempty Hadd X.
  rewrite fset_reflect.
  remember (Actor.FSet.elements X) as ls eqn:Hls.

  (*
  assert (Hdup : SetoidList.NoDupA eq ls).
  { subst. apply Actor.Map.S.elements_3w. }
  clear X Hls.
  *)

  revert X Hls.

  induction ls as [ | B ls]; intros X Hls.
  { auto. }
  simpl.
  apply Hadd; auto.
  {
    destruct X as [X Hok]; simpl in Hls.
    inversion Hls; subst; auto.
    apply add_ok_inversion in Hok.
    destruct Hok as [Hin Hok].
    rewrite Actor.Map.MProofs.FSetProperties.elements_iff.
    rewrite elems_fset_of_elems; auto.
  }
  specialize (IHls (fset_of_elems ls)).
  apply IHls.
  rewrite elems_fset_of_elems; auto.
  destruct X as [X Hok]; simpl in Hls.
  inversion Hls; subst.
  apply add_ok_inversion in Hok.
  destruct Hok; auto.
Qed.
*)

Global Instance fold_proper : Proper (eq ==> Actor.FSet.Equal ==> Actor.Map.Equal ==> Actor.Map.Equal) (@Actor.FSet.fold Network.t).
Admitted.

Lemma fold_uncons_mapsto_neq : forall X A PA N,
  ~ Actor.FSet.In A X ->
  Actor.Map.MapsTo A PA (Actor.FSet.fold uncons X N) <->
  Actor.Map.MapsTo A PA N.
Proof.
  intros X A PA N Hin. rewrite Actor.FSet.fold_1.
  remember (Actor.FSet.elements X) as ls eqn:Hls.
  assert (Hls' : SetoidList.equivlistA eq ls (Actor.FSet.elements X)).
  { rewrite Hls. reflexivity. }
  assert (Hdup : SetoidList.NoDupA eq ls).
  { rewrite Hls. apply Actor.FSet.elements_3w. }
  clear Hls.
  revert X Hls' Hdup N Hin.
  induction ls as [ | B ls]; intros X Hls Hdup N Hin.
  { reflexivity. }
  simpl.

  compare A B.
  {
    exfalso.
    apply Hin.
    apply Actor.FSet.elements_2.
    rewrite <- Hls.
    constructor; auto.
  }

  rewrite (IHls (Actor.FSet.remove B X)).
  2:{
    erewrite Actor.Map.FSetProofs.elements_cons_remove; eauto.
    { reflexivity. }
    { inversion Hdup; auto. }
    { symmetry. auto. }
  }
  2:{ inversion Hdup; auto. }
  2:{ Actor.simplify. }
  apply uncons_neq; auto.
Qed.


Lemma actor_equivlistA_eq : forall (ls1 ls2 : list Actor.t),
  Sorted.Sorted OrderedTypeEx.String_as_OT.lts ls1 ->
  Sorted.Sorted OrderedTypeEx.String_as_OT.lts ls2 ->
  SetoidList.NoDupA eq ls1 ->
  SetoidList.NoDupA eq ls2 ->
  SetoidList.equivlistA eq ls1 ls2 <-> ls1 = ls2.
Proof.
  intros ls1 ls2 Hsorted1 Hsorted2 Hdup1 Hdup2.
  split.
  * intros Heq. unfold SetoidList.equivlistA in Heq.
    admit.
  * intros. subst. reflexivity.
Admitted.


Lemma fold_uncons_mapsto_eq : forall N A PA X,
  Actor.FSet.In A X ->
  Actor.Map.MapsTo A PA (Actor.FSet.fold uncons X N) <->
  exists I, Actor.Map.MapsTo A (I :: PA) N.
Proof.
  intros N A PA X Hin.
  rewrite Actor.FSet.fold_1.
  remember (Actor.FSet.elements X) as ls eqn:Hls.

  (*
  assert (Hls' : SetoidList.equivlistA eq ls (Actor.FSet.elements X)).
  { rewrite Hls. reflexivity. }
  assert (Hdup : SetoidList.NoDupA eq ls).
  { rewrite Hls. apply Actor.FSet.elements_3w. }
  clear Hls.
  *)
  revert X Hls Hin N.
  induction ls as [ | B ls]; intros X Hls Hin N.
  {
    exfalso.
    apply Actor.FSet.elements_1 in Hin.
    rewrite <- Hls in Hin.
    inversion Hin.
  }
  simpl.
  symmetry in Hls.

  

  (*assert (Hremove : SetoidList.equivlistA eq (Actor.FSet.elements (Actor.FSet.remove B X)) ls).*)
  assert (Hremove : Actor.FSet.elements (Actor.FSet.remove B X) = ls).
  {
    set (Hsort := Actor.FSet.elements_3 X).
    rewrite Hls in Hsort.
    inversion Hsort; subst; clear Hsort.
    set (Hdup := Actor.FSet.elements_3w X).
    rewrite Hls in Hdup.
    inversion Hdup; subst; clear Hdup.

    apply actor_equivlistA_eq; auto.
    { apply Actor.FSet.elements_3. }
    { apply Actor.FSet.elements_3w. }

    apply Actor.Map.FSetProofs.elements_cons_remove; auto.
    rewrite Hls.
    reflexivity.
  }
  compare A B.
  {
    set (Hyp := fold_uncons_mapsto_neq (Actor.FSet.remove A X) A PA (uncons A N)).
    rewrite Actor.FSet.fold_1 in Hyp.

    rewrite Hremove in Hyp.
    rewrite Hyp.
    2:{ Actor.simplify. }
    clear Hyp.
    unfold uncons.
    destruct (Actor.Map.find A N) as [[ | IA PA'] | ] eqn:Hfind.
    + Actor.simplify.
      transitivity False. { intuition. }
      split; intros H; destruct H.
      Actor.solve.
      unfold Process.t in Hfind.
      rewrite Hfind in *.
      discriminate.

    + Actor.simplify.
      transitivity (PA = PA'). { intuition. }
      split.
      - intros; subst.
        exists IA. Actor.solve.
      - intros [I Hmapsto].
        Actor.reflect_find.
        unfold Process.t in Hfind.
        rewrite Hfind in Hmapsto.
        inversion Hmapsto; subst; auto.

    + rewrite <- Actor.Map.Properties.F.not_find_in_iff in Hfind.
      split; intros Hmapsto.
      - exfalso. Actor.solve.
      - destruct Hmapsto. exfalso. Actor.reflect_find.
        unfold Process.t in Hfind.
        rewrite Hfind in *. discriminate.
  }
  {
    (* A <> B, so A ∈ ls *)
    rewrite (IHls (Actor.FSet.remove B X)); auto.
    2:{ Actor.simplify. }
    split; intros [I H]; exists I;
      rewrite uncons_neq in *; auto.
  }
Qed.

Lemma EPP_N_cons_inversion : forall I C N,
  EPP_N (I :: C) N ->
  EPP_N C (Actor.FSet.fold uncons (Choreography.Insn.actors I) N).
Proof.
  intros I C N HN.
  rewrite EPP_N_spec in *.
  intros D PD HD.
  destruct (Actor.Map.FSetProofs.in_dec D (Choreography.Insn.actors I)) as [Hin | Hin].
  * rewrite fold_uncons_mapsto_eq in HD; auto.
    destruct HD as [I0 HD].
    apply HN in HD.
    inversion HD; subst; clear HD; auto.
    contradiction.
  * rewrite fold_uncons_mapsto_neq in HD; auto.
    apply HN in HD.
    eapply EPP_disjoint_inversion in HD; auto.
Qed.


Lemma completeness_local : forall PA (refs : Var.Map.t nat) cfg PA' refs' cfg',
  Process.step PA refs cfg PA' refs' cfg' -> 
  forall A N C (Θ : ChorEnv.t nat) Θ',
  EPP_N C N ->
  WFChoreography C ->
  Actor.Map.MapsTo A PA N ->
  Actor.Map.MapsTo A refs Θ ->
  (*Var.Map.Equal refs (ChorEnv.find A Θ) ->*)
  ChorEnv.Equal Θ' (Actor.Map.add A refs' Θ) ->
  
  exists C',
    Choreography.step C Θ cfg (Label.Loc A) C' Θ' cfg'
    /\
    EPP_N C' (Actor.Map.add A PA' N).
Proof.
  intros ? ? ? ? ? ? Hstep A N C Θ Θ' HEPP_N HWF Hmapsto Hrefs HΘ'.
  rewrite EPP_N_spec in HEPP_N.
  apply HEPP_N in Hmapsto.
  rewrite <- EPP_N_spec in HEPP_N.
  revert N HEPP_N.
  revert refs cfg PA' refs' cfg' Hstep Hrefs HΘ' HWF.
  induction Hmapsto;
    intros refs cfg PA' refs' cfg' Hstep Hrefs HΘ' HWF N HEPP_N;
    subst;
    try (inversion Hstep; fail).

  * (* SendC *)
    inversion Hstep; subst; clear Hstep.
    Var.simplify.
    exists (Choreography.Insn.Send A e' B y :: C).
    split.
    { econstructor; eauto.
      unfold ChorEnv.find.
      Actor.reflect_find.
      auto.
    }
    { 
      eapply (EPP_N_add _ A (Insn.Send e' B :: P)).
      { Actor.simplify. }
      { constructor; auto. }
      {
        Actor.simplify.

        EPP_N_cons.
        EPP_N_cons.
        {
          simpl in *. Actor.simplify.
          match goal with
          | [ H : Actor.Map.M.MapsTo _ _ _ |- _ ] =>
            rename H into Hmapsto'
          end.
          apply H in Hmapsto'.
          2:{ Actor.simplify. }
          inversion Hmapsto'; subst; try contradiction.
          2:{ exfalso. simpl in *. Actor.simplify. }
          constructor; auto.
        }
      }
    }

  * (* Let *)
    inversion Hstep; subst; clear Hstep.
    + (* LetC *)
      Var.simplify.
      exists (Choreography.Insn.Let A x e' :: C).
      split.
      { econstructor; eauto.
        unfold ChorEnv.find.
        Actor.reflect_find.
        auto.
      }
      {
        EPP_N_cons.
        EPP_N_cons.
        destruct H2 as [[? ?] | [? ?]]; try contradiction;
            subst.
        constructor; auto.
        apply EPP_disjoint; simpl; Actor.simplify.
        eapply EPP_disjoint_inversion.
        { apply H; auto. }
        { simpl; Actor.simplify. }
      }

    + (* LetB *)
      exists (Choreography.subst A x e C).
      split.
      {
        assert (Heq' : ChorEnv.Equal Θ' Θ).
        {
          rewrite HΘ'.
          Search ChorEnv.Equal Actor.Map.Equal.
          apply ChorEnv.actor_map_Equal.
          Search Actor.Map.add Actor.Map.MapsTo.
          apply Actor.Map.Proofs.add_mapsto; auto.
        }
        rewrite Heq'.
        eapply Choreography.LetB; eauto.
      }
      {
        eapply (EPP_N_add _ A).
        { Actor.simplify. }
        { apply EPP_subst_eq; auto. }
        {
          Actor.simplify.

          rewrite EPP_N_subst_neq; auto.
          2:{ Actor.simplify. }
          EPP_N_cons; auto.
        }
      }


  * (* LetBang *)
    inversion Hstep; subst; clear Hstep.
    + (* LetBangC *)
      Var.simplify.
      exists (Choreography.Insn.LetBang A x e' :: C).
      split.
      { econstructor; eauto.
        unfold ChorEnv.find.
        Actor.reflect_find; auto.
      }
      {
        EPP_N_cons.
        EPP_N_cons.
        destruct H2 as [[? ?] | [? ?]]; try contradiction;
            subst.
        constructor; auto.
        apply EPP_disjoint; simpl; Actor.simplify.
        eapply EPP_disjoint_inversion.
        apply H; auto.
        simpl; Actor.simplify.
      }

    + (* LetBangB *)
      exists (Choreography.subst A x e0 C).
      split.
      {
        
        assert (Heq' : ChorEnv.Equal Θ' Θ).
        {
          rewrite HΘ'.
          Search ChorEnv.Equal Actor.Map.Equal.
          apply ChorEnv.actor_map_Equal.
          Search Actor.Map.add Actor.Map.MapsTo.
          apply Actor.Map.Proofs.add_mapsto; auto.
        }
        rewrite Heq'.
        eapply Choreography.LetBangB; eauto.
      }
      {
        eapply (EPP_N_add _ A).
        { Actor.simplify. }
        { apply EPP_subst_eq; auto. }
        {
          Actor.simplify.
          rewrite EPP_N_subst_neq; auto.
          2:{ Actor.simplify. }
          EPP_N_cons; auto.
        }
      }

  * (* LetPair *) 
    inversion Hstep; subst; clear Hstep.
    + (* LetPairC *)
      Var.simplify.
      exists (Choreography.Insn.LetPair A x1 x2 e' :: C).
      split.
      { econstructor; eauto.
        unfold ChorEnv.find.
        Actor.reflect_find; auto. 
      }
      {
        EPP_N_cons.
        EPP_N_cons.
        simpl in *. Actor.simplify. subst.
        destruct H2 as [[? ?] | [? ?]]; try contradiction;
            subst.
        constructor; auto.
      }

    + (* LetPairB *)
      eexists.
      split.
      { 
        assert (Heq' : ChorEnv.Equal Θ' Θ).
        {
          rewrite HΘ'.
          Search ChorEnv.Equal Actor.Map.Equal.
          apply ChorEnv.actor_map_Equal.
          Search Actor.Map.add Actor.Map.MapsTo.
          apply Actor.Map.Proofs.add_mapsto; auto.
        }
        rewrite Heq'.
        eapply Choreography.LetPairB; eauto.
      }
      {
        eapply (EPP_N_add _ A).
        { Actor.simplify. }
        {
          apply EPP_subst_eq.
          apply EPP_subst_eq.
          auto.
        }
        {
          EPP_N_cons; auto.
          Actor.simplify.
          rewrite EPP_N_subst_neq; auto.
          2:{ Actor.simplify. }
          rewrite EPP_N_subst_neq; auto.
          { Actor.simplify. }
        }
      }

  * (* Inductive case *)

    inversion HWF; subst; clear HWF.

    set (HEPP_N_uncons := EPP_N_cons_inversion _ _ _ HEPP_N).
    eapply IHHmapsto in HEPP_N_uncons; eauto.
    destruct HEPP_N_uncons as [C' [Hstep' HEPP_N_uncons]].
    exists (I :: C').
    split.
    + apply Choreography.Delay; auto.
      simpl.
      intros B. Actor.simplify.
      intros [? Hin]; subst.
      contradiction.
    + rewrite EPP_N_spec.
      intros D PD HD.
      Actor.simplify.
      destruct HD as [[? ?] | [? HD]]; subst.
      { (* A = D *)
        apply EPP_disjoint; auto.
        rewrite EPP_N_spec in HEPP_N_uncons.
        apply HEPP_N_uncons.
        Actor.simplify.
      }
      destruct (Actor.Map.FSetProofs.in_dec D (Choreography.Insn.actors I))
        as [HinD | HinD].
      2:{ (* D not in I *)
        apply EPP_disjoint; auto.
        rewrite EPP_N_spec in HEPP_N_uncons.
        apply HEPP_N_uncons.
        Actor.simplify.
        right. split; auto.
        rewrite fold_uncons_mapsto_neq; auto.
      }
      { (* D in I but not equal to A *)
        assert (HD' : exists PD', PD = eppI D I ++ PD' /\ EPP D C PD').
        {
          Search eppI.
          rewrite EPP_N_spec in HEPP_N.
          rewrite <- EPP_cons; auto.
        }
        destruct HD' as [PD' [? HD']]; subst.
        rewrite EPP_cons; auto.
        exists PD'. split; auto.
        rewrite EPP_N_spec in HEPP_N_uncons.
        apply HEPP_N_uncons.
        Actor.simplify. right. split; auto.
        rewrite fold_uncons_mapsto_eq; auto.
        destruct I; simpl in *; Actor.simplify; simpl in *; eexists; eauto.
        all: (destruct HinD; subst; contradiction).
      }

    Unshelve.
    all: (subst; try contradiction).
    exact (Insn.Send t0 t).
    exact (Insn.EPR t0 t).
Qed.



Lemma completeness_send : forall N refs cfg A v B N' refs' cfg' C,
  WFChoreography C ->
  Network.step N refs cfg (Label.Send A v B) N' refs' cfg' ->
  EPP_N C N ->
  exists C',
    Choreography.step C refs cfg (Label.Send A v B) C' refs' cfg'  /\
    EPP_N C' N'.
Proof.
  intros N refs cfg A v B N' refs' cfg' C HWF H.
  inversion H; subst; clear H.
  generalize dependent B. generalize dependent A.
  (*generalize dependent v.*)
  revert N PA PB.
  induction HWF;
    intros N (*refs' cfg'*) PA PB (*y*) (*v Hv*) A B Hneq HA HB HEPP_N.
  {
    exfalso.
    (* absurd *)
    rewrite EPP_N_spec in HEPP_N.
    apply HEPP_N in HA.
    inversion HA.
  }

  assert (HI : I = Choreography.Insn.Send A v B y
    \/ (~ Actor.FSet.In A (Choreography.Insn.actors I)
     /\ ~ Actor.FSet.In B (Choreography.Insn.actors I))).
  {
    EPP_N_cons.
    destruct (Actor.Map.FSetProofs.in_dec A (Choreography.Insn.actors I)) as [HinA | HinA];
    destruct (Actor.Map.FSetProofs.in_dec B (Choreography.Insn.actors I)) as [HinB | HinB].
    2:{
      (* contradiction *)
      set (HinA' := H0 _ (Insn.Send v B :: PA) HinA HA).
      inversion HinA'; subst; clear HinA'; try contradiction.
      simpl in *. Actor.simplify.
    }
    2:{
      (* contradiction *)
      set (HinB' := H0 _ (Insn.Receive y A :: PB) HinB HB).
      inversion HinB'; subst; clear HinB'; try contradiction.
      simpl in *. Actor.simplify.
    }
    {
      left.
      set (HinA' := H0 _ _ HinA HA).
      set (HinB' := H0 _ _ HinB HB).
      inversion HinA'; subst; clear HinA'; try contradiction.
      inversion HinB'; subst; clear HinB'; try contradiction.
      simpl in *. Actor.simplify.
    }
    { auto. }
  }
  destruct HI as [? | [HinA HinB]]; subst.
  +
  
    EPP_N_cons.
    set (HinA' := HA). apply H0 in HinA'. 2:{ simpl; Actor.simplify. }
    set (HinB' := HB). apply H0 in HinB'. 2:{ simpl; Actor.simplify. }

    inversion HinA'; subst; clear HinA'. 2:{ simpl in *; Actor.simplify. }
    inversion HinB'; subst; clear HinB'. 2:{ simpl in *; Actor.simplify. }

    exists (Choreography.subst B y v C).
    simpl in *.
    split.
    { constructor; auto. }

    rewrite EPP_N_spec.
    intros D PD HD.
    Actor.simplify.
    destruct HD as [[? ?] | [? [[? ?] | [? HD]]]]; subst.
    { apply EPP_subst_neq; auto. }
    { apply EPP_subst_eq; auto. }
    { apply EPP_subst_neq; auto.
      rewrite EPP_N_spec in H1.
      apply H1; Actor.simplify.
    }

  + 
    assert (HEPP_N_cons : forall D PD,
      Actor.FSet.In D (Choreography.Insn.actors I) ->
      Actor.Map.MapsTo D PD N ->
      EPP D (I :: C) PD).
    { EPP_N_cons. }
    apply EPP_N_cons_inversion in HEPP_N.
    edestruct IHHWF
      as [C' [IHstep IHEPP_N]];
      [ eauto | | | eauto | ].
    { apply fold_uncons_mapsto_neq; eauto. }
    { apply fold_uncons_mapsto_neq; eauto. }

    exists (I :: C').
    split.
    { constructor; auto.
      {
        intros D. simpl. Actor.simplify.
        intuition; subst; try contradiction.
      }
    }

    rewrite EPP_N_spec in *.
    intros D PD HD.
    Actor.simplify.
    destruct HD as [[? ?] | [? [[? ?] | [? HD]]]]; subst; try contradiction.
    {
      apply EPP_disjoint; auto.
      apply IHEPP_N. Actor.simplify.
    }
    {
      apply EPP_disjoint; auto.
      apply IHEPP_N. Actor.simplify.
    }
    destruct (Actor.Map.FSetProofs.in_dec D (Choreography.Insn.actors I)) as [Hin | Hin].
    2:{ 
      apply EPP_disjoint; auto.
      apply IHEPP_N. Actor.simplify.
      right. split; auto.
      right. split; auto.
      apply fold_uncons_mapsto_neq; auto.
    }
      set (HD' := HEPP_N_cons D PD Hin HD).
      apply EPP_cons in HD'; auto.
      destruct HD' as [PD' [? HD']]; subst.
      apply EPP_cons; auto.
      exists PD'. split; auto.
      apply IHEPP_N. Actor.simplify.
      right. split; auto.
      right. split; auto.
      assert (HI : exists I', eppI D I = [I']).
      (* could make this a lemma *)
      { destruct I;
          simpl in *; autorewrite with actor_db in *;
          try (destruct Hin; subst; Actor.simplify;
                eexists; eauto; fail).
      }
      destruct HI as [I' HI].
      rewrite HI in HD. simpl in HD.
      rewrite fold_uncons_mapsto_eq; auto.
      exists I'; auto.
Qed.


Lemma EPP_N_subst_eq : forall A x v C N,
  EPP_N (Choreography.subst A x v C) N
  <->
  (forall PA, Actor.Map.MapsTo A PA N ->
            EPP A (Choreography.subst A x v C) PA)
  /\ EPP_N C (Actor.Map.remove A N).
Admitted.



Lemma EPP_deterministic : forall C A P1 P2,
  EPP A C P1 ->
  EPP A C P2 ->
  P1 = P2.
Proof.
  induction C as [ | I C]; intros A P1 P2 H1 H2.
  * inversion H1; inversion H2; subst; clear H1 H2.
    auto.
  * inversion H1; inversion H2; subst; clear H1 H2; auto;
    try discriminate;
    repeat match goal with
    | [ H : ?A <> ?A |- _ ] => contradiction
    | [ H : ?C _ = ?C _ |- _ ] => inversion H; subst; clear H
    | [ H : ?C _ _ = ?C _ _ |- _ ] => inversion H; subst; clear H
    | [ H : ?C _ _ _ = ?C _ _ _ |- _ ] => inversion H; subst; clear H
    | [ H : ?C _ _ _ _ = ?C _ _ _ _ |- _ ] => inversion H; subst; clear H
    end;
    f_equal; eauto;
    simpl in *; Actor.simplify. 
Qed.

Lemma EPP_disjoint_iff : forall A I C P,
  ~ Actor.FSet.In A (Choreography.Insn.actors I) ->
  EPP A (I :: C) P <-> EPP A C P.
Proof.
  intros. split; intros Hepp.
  { apply EPP_disjoint_inversion in Hepp; auto. }
  { apply EPP_disjoint; auto. }
Qed.

Lemma completeness_epr : forall C N refs cfg A B N' refs' cfg',
  Network.step N refs cfg (Label.EPR A B) N' refs' cfg' ->
  EPP_N C N ->
  exists C',
    Choreography.step C refs cfg (Label.EPR A B) C' refs' cfg'  /\
    EPP_N C' N'.
Proof.
  intros C; induction C as [ | I C];
    intros ? ? ? ? ? ? ? ? Hstep HEPP_N.
  {
    (* absurd *) admit.
  }

  inversion Hstep; subst; clear Hstep.
  rename H2 into HmapstoA, H3 into HmapstoB.

  rewrite EPP_N_spec in HEPP_N.
  assert (HEPPA : EPP A (I :: C) (Insn.EPR x B :: PA))
    by (apply HEPP_N; auto).
  assert (HEPPB : EPP B (I :: C) (Insn.EPR y A :: PB))
    by (apply HEPP_N; auto).
  rewrite <- EPP_N_spec in HEPP_N.

  
  assert (HI : I = Choreography.Insn.EPR A x B y
    \/ (~ Actor.FSet.In A (Choreography.Insn.actors I)
     /\ ~ Actor.FSet.In B (Choreography.Insn.actors I))).
  admit.
  destruct HI as [? | [HA HB]]; subst; simpl in *.
  +
    eexists.
    split.
    { econstructor; eauto. }
    rewrite EPP_N_subst_eq.
    split.
    { intros PA' HmapstoA'.
      Actor.simplify.
      destruct HmapstoA' as [[? ?] | [? _]]; subst.
      2:{ contradiction. }
      apply EPP_subst_eq. apply EPP_subst_neq; auto.
      inversion HEPPA; subst; auto;
        simpl in *; Actor.simplify.
    }
      
    Actor.simplify.
    rewrite EPP_N_subst_eq.
    split.
    {
      intros PB' HmapstoB'.
      Actor.simplify.
      destruct HmapstoB' as [[? ?] | [? _]]; subst.
      2:{ contradiction. }
      apply EPP_subst_eq; auto.
      inversion HEPPB; subst; auto;
        simpl in *; Actor.simplify.
    }

    Actor.simplify.
    EPP_N_cons.

  + (* A,B not in actors(I) *)

    apply EPP_disjoint_inversion in HEPPA; auto.
    apply EPP_disjoint_inversion in HEPPB; auto.

    EPP_N_cons.

    set (N' := uncons A N).

    (*
      assert that for every D ∈ I,
        exists I', EPP D (I :: C) (I' :: PD)
        in which case EPP D C PD
      let N' := N[forall D ∈ I, D ↦ PD]
    *)


    edestruct (IHC) as [C' [IHstep IHEPP_N]].
    3:{
    exists (I :: C').
    split.
    { constructor; eauto.
      intros D. simpl. Actor.simplify.
      intuition; subst; try contradiction.
    }

    (* We know this is correct for everything not in I.
      What about things in I?
    *)
    EPP_N_cons.
    2:{
      rewrite EPP_N_spec in *.
      intros D PD Hmapsto.
      apply IHEPP_N.
      admit (*Actor.simplify.*).
    }
    {
      rename A0 into D, PA0 into PD.
      destruct H3 as [[? ?] | [? [[? ?] | [? ?]]]]; subst;
        try contradiction.
      (* D <> A, D <> B, N[D] = PD *)
      (* WTS: [I::C']_D = PD *)
      (* Know: [I::C]_D = PD, so PD = eppI D I ++ [C]_D *)
      assert (HEPPD : EPP D (I :: C) PD).
      { apply H; auto. }
      assert (WFInsn I) by admit.
      apply EPP_cons in HEPPD; auto.
      destruct HEPPD as [PD' [? HEPPD]]; subst.
      apply EPP_cons; auto.
      eexists. split; eauto.


Admitted.


Theorem completeness : forall N refs cfg l N' refs' cfg',

    Network.step N refs cfg l N' refs' cfg' ->

    forall C, WFChoreography C ->
    EPP_N C N ->
    exists C', EPP_N C' N' /\
                Choreography.step C refs cfg l C' refs' cfg'.
Proof.
    intros N refs cfg l N' refs' cfg' Hstep C HWF HEPP.
    destruct l as [A v B | A B | A ].

    * (* send *)
      eapply completeness_send in Hstep; eauto.
      destruct Hstep as [C' [Hstep HEPP_N]].
      exists C'; auto.

    * (* EPR *)
      eapply completeness_epr in Hstep; eauto.
      destruct Hstep as [C' [Hstep HEPP_N]].
      exists C'; auto.
  
    * (* local step *)
      inversion Hstep; subst; clear Hstep.
      eapply completeness_local in H1; eauto;
        try reflexivity.
      destruct H1 as [C0 [Hstep HEPP_N]].
      exists C0. split; auto.

Qed.

(*
Lemma step_label_sound : forall C refs l C',
  step_label C refs l C' ->
  forall cfg, exists refs' cfg',
  Choreography.step C refs cfg l C' refs' cfg'.
Proof.
  induction C as [ | I C];
    intros refs l C' Hstep cfg.
  { inversion Hstep. }
  inversion Hstep; subst; clear Hstep.

  * exists refs; exists cfg.
    constructor; auto.

  * destruct (Config.epr (ChorEnv.find A' refs) cfg) 
      as [[[q1 q2] refsA'] cfgA'] eqn:Hepr.
  
    exists (Actor.Map.add A' refsA' refs).
    exists cfgA'.
    econstructor; simpl; auto.
    unfold ChorEnv.epr.
    unfold Config.epr in Hepr.
    destruct (Config.epr_cfg cfg) as [[q1' q2'] cfg'] eqn:Hepr'.
    inversion Hepr; subst; clear Hepr.
Admitted.
  

  
Lemma step_send_complete : forall C A v y B PA PB refs cfg C',
    EPP A C (Insn.Send v B :: PA) ->
    EPP B C (Insn.Receive y A :: PB) ->
    Expr.Val v ->
    step_label C refs (Label.Send A v B) C' ->
    Choreography.step C refs cfg (Label.Send A v B)
                      C' refs cfg.
Proof.
    induction C as [ | I C];
        intros A v y B PA PB refs cfg C' HEPPA HEPPB Hval Hstep.
    { contradict HEPPA. simpl; inversion 1. }
    inversion Hstep; subst; clear Hstep.

    inversion HEPPA; subst; clear HEPPA;
    inversion HEPPB; subst; clear HEPPB;
      simpl in *;
      Actor.simplify.
    * (* send *)
      apply Choreography.SendB; auto.
        
    * apply Choreography.Delay; auto.
        match goal with
        | [ H : Actor.FSet.Empty _ |- _ ] =>
          rename H into Hempty
        end.
    (*
      assert (Hin : ~ (Actor.FSet.In A (Choreography.Insn.actors I)) /\ ~ ).
      {
        intros Hin.
        match goal with
        | [ H : Actor.FSet.Empty _ |- _ ] =>
          specialize (H A);
          simpl in H;
          Actor.simplify
        end.
      }
        *)
      apply EPP_disjoint_inversion in HEPPA; auto.
      2:{
        specialize (Hempty A);
        simpl in *;
        Actor.simplify.
      }
      apply EPP_disjoint_inversion in HEPPB; auto.
      2:{
        specialize (Hempty B);
        simpl in *;
        Actor.simplify.
      }
      eapply IHC; eauto.
Qed.



Lemma EPP_cons : forall A I C1 C2,
  (forall P, EPP A C1 P -> EPP A C2 P) ->
  (forall P, EPP A (I :: C1) P -> EPP A (I :: C2) P).
Proof.
  intros A I C1 C2 H P H'.
  inversion H'; subst; clear H';
    try (constructor; auto; fail).
Qed.

Lemma EPP_cons_iff : forall A I C1 C2,
  (forall P, EPP A C1 P <-> EPP A C2 P) ->
  (forall P, EPP A (I :: C1) P <-> EPP A (I :: C2) P).
Proof.
  intros A I C1 C2 H P.
  split; apply EPP_cons; apply H.
Qed.

Lemma step_label_neq : forall refs l D C C' PD,
      step_label C refs l C' ->
      ~ Actor.FSet.In D (Label.actors l) ->
      EPP D C' PD <-> EPP D C PD.
Proof.
  intros ? ? ? ? ? ? Hstep.
  revert D PD.
  induction Hstep; intros D PD;
    subst; simpl; intros Hin; Actor.simplify.
  * rewrite EPP_disjoint_iff; auto.
    2:{ simpl; Actor.simplify. }
    rewrite EPP_subst_iff.
    intuition.

  * remember (Var.fresh (ChorEnv.find A' refs)) as q1.
    remember (Var.fresh (Var.Map.add x q1 (ChorEnv.find A' refs))) as q2.
  
    rewrite EPP_disjoint_iff; auto.
    2:{ simpl; Actor.simplify. }
    repeat rewrite EPP_subst_iff.
    intuition.

  * 
    rewrite EPP_disjoint_iff; auto.
    2:{ simpl; Actor.simplify. }
    repeat rewrite EPP_subst_iff.
    intuition.

  * 
    rewrite EPP_disjoint_iff; auto.
    2:{ simpl; Actor.simplify. }
    repeat rewrite EPP_subst_iff.
    intuition.

  * 
    rewrite EPP_disjoint_iff; auto.
    2:{ simpl; Actor.simplify. }
    repeat rewrite EPP_subst_iff.
    intuition.
    
  * 
    apply EPP_cons_iff.
    intros P. apply IHHstep; auto.
Qed.

Lemma step_send_EPP : forall C A B PA PB v y refs D PD,
    EPP A C (Insn.Send v B :: PA) ->
    EPP B C (Insn.Receive y A :: PB) ->
    A <> B ->
    forall C',
    step_label C refs (Label.Send A v B) C' ->

    EPP D C' PD
    <->
    (D = A /\ PD = PA)
    \/
    (D = B /\ PD = Process.subst y v PB)
    \/
    (D <> A /\ D <> B /\ EPP D C PD).
Proof.
  intros C A B PA PB v y refs D PD HA HB Hneq.
  induction C as [ | I C];
    intros C' Hstep;
    simpl in *;
    inversion Hstep; subst; clear Hstep.

  * (* substitution happens here *)
    rewrite EPP_subst_iff; auto.
    inversion HA; subst; clear HA; auto.
    2:{ (* contradiction *)
      simpl in *; Actor.simplify.
    }
    inversion HB; subst; clear HB; auto.
    2:{ (* contradiction *)
      simpl in *; Actor.simplify.
    }
    clear H3 H4 H11 H7.
    split; intros H.
    + compare D A; [ | compare D B].
      - left. split; auto.
        destruct H as [ [PD0 [P0 [HPD0 ?]]] | [? HPD0]]; subst;
          try contradiction.
        eapply EPP_deterministic; eauto.
      - right. left.
        split; auto.
        destruct H as [ [PD0 [P0 [HPD0 ?]]] | [? HPD0]]; subst;
          try contradiction.
        f_equal.
        eapply EPP_deterministic; eauto.
      - right. right.
        split; auto. split; auto.
        destruct H as [ [PD0 [P0 [HPD0 ?]]] | [? HPD0]]; subst;
          try contradiction.
        constructor; auto.
        simpl; Actor.simplify.

    + destruct H as [[? ?] | [ [? ?] | [? [? ?]] ]]; subst.
      - right. split; auto.
      - left. split; auto. exists PB. split; auto.
      - right. split; auto.
        apply EPP_disjoint_inversion in H1; auto.
        simpl; Actor.simplify.

  * (* substitution happens later *)
    assert (~ Actor.FSet.In A (Choreography.Insn.actors I)).
    {
      intros Hin;
      match goal with
      | [ H0 : Actor.FSet.Empty _ |- _ ] => 
        apply (H0 A)
      end.
      simpl; Actor.simplify.
    }
    assert (~ Actor.FSet.In B (Choreography.Insn.actors I)).
    {
      intros Hin;
      match goal with
      | [ H0 : Actor.FSet.Empty _ |- _ ] => 
        apply (H0 B)
      end.
      simpl; Actor.simplify.
    }
    clear H1.
    apply EPP_disjoint_inversion in HA; auto.
    apply EPP_disjoint_inversion in HB; auto.

    match goal with
    | [ Hstep0 : step_label C _ _ _ |- _ ] =>
      set (IH := IHC HA HB _ Hstep0); eauto;
      rename Hstep0 into Hstep
    end.

    compare D A; [ | compare D B].
    - (* D = A *)
      transitivity (EPP D C'0 PD).
      { apply EPP_disjoint_iff; auto. }
      rewrite IH.
      intuition.

    - (* D = B *)
      transitivity (EPP D C'0 PD).
      { apply EPP_disjoint_iff; auto. }
      rewrite IH.
      intuition.

    - (* D <> A /\ D <> B *)
      transitivity (EPP D (I :: C) PD).
      2:{ intuition. }

      eapply (step_label_neq refs (Label.Send A v B)).
      2:{ simpl; Actor.simplify. }
      apply StepCons; auto.
      { intros Z. simpl. Actor.simplify.
        intros [[? | ?] Hin']; subst; try contradiction.
      }
Qed.



Lemma subst_neq_inversion : forall A x v D C P,
  D <> A ->
  EPP D (Choreography.subst A x v C) P ->
  EPP D C P.
Proof.
  intros ? ? ? ? C.
  induction C as [ | I C]; intros P Hneq H;
    simpl in H;
    auto.
  inversion H; subst; clear H;
    try match goal with
    | [ Hsubst : _ = Choreography.Insn.subst _ _ _ I |- _ ] =>
    destruct I; simpl in *;
    inversion Hsubst; subst; clear Hsubst
    end.
  * Actor.Map.Tactics.compare A t.
    constructor; auto.
    Actor.simplify; auto.
    Var.simplify; auto.
  * constructor; auto.
    Actor.simplify; auto.
  * constructor; auto;
    Actor.simplify; auto;
    Var.simplify; auto.
  * constructor; auto.
    Actor.simplify; auto;
    Var.simplify; auto.
  * Actor.Map.Tactics.compare A t.
    apply EPP_Let; auto.
  * Actor.Map.Tactics.compare A t.
    constructor; auto.
  * Actor.Map.Tactics.compare A t.
    constructor; auto.
  * rewrite actors_subst in *.
    apply EPP_disjoint; auto.
    destruct (Choreography.Insn.rebound_in A x I) eqn:Hbound;
      auto.
Qed.


Lemma step_send_EPP_N : forall C A B PA PB y v N refs C',
    EPP_N C N ->
    EPP A C (Insn.Send v B :: PA) ->
    EPP B C (Insn.Receive y A :: PB) ->
    Expr.Val v ->
    A <> B ->
    step_label C refs (Label.Send A v B) C' ->
    EPP_N C' (Actor.Map.add A PA (Actor.Map.add B (Process.subst y v PB) N)).
Proof.
  intros.
  apply (EPP_N_add C' A PA);
    Actor.simplify.
  { eapply step_send_EPP; eauto. }
  apply (EPP_N_add C' B (Process.subst y v PB));
    Actor.simplify.
  { eapply step_send_EPP; eauto. }

  apply EPP_N_spec.
  intros D PD Hmapsto.
  Actor.simplify. rename H7 into Hmapsto.
  rewrite EPP_N_spec in H.
  eapply step_label_neq; eauto.
  { simpl; Actor.simplify. }
Qed.

Lemma EPP_N_subst_neq : forall A x v C N,
  EPP_N C N ->
  ~ Actor.Map.In A N ->
  EPP_N (Choreography.subst A x v C) N.
Proof.
  intros A x v C N HEPP Hin.
  rewrite EPP_N_spec in *.
  intros D PD Hmapsto.
  compare A D.
  {
    exfalso. apply Hin. exists PD; auto.
  }
  apply EPP_subst_neq; auto.
Qed.

Lemma step_let_EPP : forall A C x v PA refs D PD,
    EPP A C (Insn.Let x v :: PA) ->
    forall C',
    step_label C refs (Label.Loc A) C' ->
    EPP D C' PD
    <->
    (D = A /\ PD = Process.subst x v PA)
    \/
    (D <> A /\ EPP D C PD).
Proof.
  intros A C x v PA refs.
  induction C as [ | I N ];
    intros D PD HEPPA C' Hstep.
  { inversion Hstep; subst; clear Hstep. }
  compare A D.
  2:{
    rewrite step_label_neq; eauto.
    2:{ simpl; Actor.simplify. }
    intuition.
  }
  transitivity (PD = Process.subst x v PA).
  2:{ intuition. }
  
  assert (Hdec : Actor.FSet.In A (Choreography.Insn.actors I)
    \/ ~ Actor.FSet.In A (Choreography.Insn.actors I)).
  {
    destruct I; simpl; Actor.simplify.
  }
  destruct Hdec as [Hin | Hin].
  2:{
    apply EPP_disjoint_inversion in HEPPA; auto.
    inversion Hstep; subst; clear Hstep;
      simpl in *; Actor.simplify.
    rewrite EPP_disjoint_iff; auto.
    rewrite IHN; eauto.
    tauto.
  }
  {
    inversion Hstep; subst; clear Hstep;
    inversion HEPPA; subst; clear HEPPA;
      simpl in *; Actor.simplify.
    2:{
      match goal with
      | [ H : Actor.FSet.Empty _ |- _ ] => contradict H
      end.
      intros Hempty. apply (Hempty A0).
      Actor.simplify.
    }
    rewrite EPP_subst_iff.
    split.
      {
        intros [[_ [PD0 [? ?]]] | [? ?]];
          subst; try contradiction.
        f_equal.
        eapply EPP_deterministic; eauto.
      }
      {
        intros; subst.
        left. split; auto.
        exists PA; auto.
      }

  }
Qed.


(*
(** Return the choreography C' such that C, refs, cfg' -(EPR A x B y)-> C' in the configuration cfg *)
Fixpoint step_epr A B refs cfg (C : Choreography.t) : Choreography.t :=
    match C with
    | [] => []
    | Choreography.Insn.EPR A0 x0 B0 y0 :: C' =>
        match Actor.eq_dec A A0, Actor.eq_dec B B0 with
        | left _, left _ => 
            match ChorEnv.epr A B refs cfg with
            | (q1,q2,refs',cfg') =>
                Choreography.subst A x0 (Expr.Var q1)
                (Choreography.subst B y0 (Expr.Var q2)
                C')
            end
        | _, _ =>
            Choreography.Insn.EPR A0 x0 B0 y0 :: (step_epr A B refs cfg C')
        end
    | I' :: C' => I' :: step_epr A B refs cfg C'
    end.

Lemma step_epr_complete : forall C A x y B PA PB,
    EPP A C (Insn.EPR x B :: PA) ->
    EPP B C (Insn.EPR y A :: PB) ->
    forall refs cfg q1 q2 refs' cfg',
        ChorEnv.epr A B refs cfg = (q1,q2,refs', cfg') ->
        Choreography.step   C refs cfg
                            (Label.EPR A B)
                            (step_epr A B refs cfg C) refs' cfg'.
Admitted.

Lemma step_epr_EPP_N : forall A B C PA PB x y N refs cfg q1 q2 refs' cfg',
    EPP_N C N ->
    EPP A C (Insn.EPR x B :: PA) ->
    EPP B C (Insn.EPR y A :: PB) ->
    ChorEnv.epr A B refs cfg = (q1, q2, refs', cfg') ->
    EPP_N (step_epr A B refs cfg C)
        (Actor.Map.add A (Process.subst x (Expr.Var q1) PA)
            (Actor.Map.add B (Process.subst y (Expr.Var q2) PB) N)).
Admitted.
*)

Theorem completeness : forall N refs cfg l N' refs' cfg',

    Network.step N refs cfg l N' refs' cfg' ->

    forall C,
    EPP_N C N ->
    exists C', EPP_N C' N' /\
                Choreography.step C refs cfg l C' refs' cfg'.
Proof.
    intros N refs cfg l N' refs' cfg' Hstep.
    induction Hstep; intros C HEPP; subst.
  
    * (* local step *)
      admit.

    * (* send *)
      rewrite EPP_N_spec in HEPP.
      apply HEPP in H0.
      apply HEPP in H1.
      exists (step_send A B C).
      split.
      { apply step_send_EPP_N; auto. }
      { eapply step_send_complete; eauto. }

    * (* EPR *) 
      apply HEPP in H0; destruct H0 as [_ HEPPA].
      apply HEPP in H1; destruct H1 as [_ HEPPB].
      exists (step_epr A B refs cfg C).
      split.
      { eapply step_epr_EPP_N; eauto. }
      { eapply step_epr_complete; eauto. }

Admitted.
*)