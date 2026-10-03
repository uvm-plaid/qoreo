From Qoreo.Base Require Import Var.
From Qoreo.Expr Require Expr BaseProofs.
From Qoreo.Choreography Require Import Choreography BaseProofs.


(* A slew of Lemmas for manipulating environment mappings. *)
Module HelperLemmas.

    (* START *)

    Lemma extension : forall A G x (tau : Expr.typ),
        ChorEnv.MapsTo A x tau G <-> Var.Map.MapsTo x tau (ChorEnv.find A G).
    Proof.
      intros A G x tau.
      split.
      auto.
      auto.
    Qed.

    Lemma empty_dj : forall {X : Type} (CE1 : ChorEnv.t X) CE2 A,
        ChorEnv.Empty CE2 ->
        Var.Map.Properties.Disjoint (ChorEnv.find A CE1) (ChorEnv.find A CE2).
    Proof.
      intros X CE1 CE2 A Hempty.
      intros z [Hin1 Hin2].
      unfold ChorEnv.Empty in Hempty.
      rewrite Hempty in Hin2.
      Var.simplify.
    Qed.
        
    Lemma nin_dj : forall  {X : Type} x (M1 : Var.Map.t X) M2,
        Var.Map.Properties.Disjoint M1 M2 ->
        Var.Map.In x M2 ->
        ~ Var.Map.In x M1.
    Proof.
      intros X x M1 M2 Hdisj Hin1 Hin2.
      apply (Hdisj x); auto.
    Qed.

    Lemma remove_nin_dj : forall  {X : Type} x (M1 : Var.Map.t X) M2,
        Var.Map.Properties.Disjoint M1 (Var.Map.remove x M2) ->
        ~ Var.Map.In x M1 ->
        Var.Map.Properties.Disjoint M1 M2.
    Proof.
      intros X x M1 M2 Hdisj Hin.
      intros z [Hin1 Hin2].
      Var.Map.Tactics.compare x z.
      {
        apply (Hdisj z).
        split; auto.
        Var.simplify.
      }
    Qed.

    Lemma partition_dj : forall  {X : Type} (M : Var.Map.t X) M1 M2 M3,
        Var.Map.Properties.Disjoint M M1 ->
        Var.Map.Partition M1 M2 M3  ->
        Var.Map.Properties.Disjoint M M2.
    Proof.
      intros X M M1 M2 M3 Hdisj Hpart.
      Var.Map.Tactics.reflect_partition.
      Var.simplify.
    Qed.

    Lemma partition_concat_dj : forall  {X : Type} (M : Var.Map.t X) M1 M2 M3,
        Var.Map.Partition M1 M2 M3  ->
        Var.Map.Properties.Disjoint M M2 ->
        Var.Map.Properties.Disjoint M M3 ->
        Var.Map.Properties.Disjoint M M1.
    Proof.
      intros.
      Var.Map.Tactics.reflect_partition.
      Var.simplify.
    Qed.

    (* follows by partition_dj in case A = B, immediate otherwise *)
    Lemma partition_dj_env : forall  {X : Type} A B (CE1 : ChorEnv.t X) CE2 M1 M2,
        Var.Map.Properties.Disjoint (ChorEnv.find A CE1) (ChorEnv.find A CE2) ->
        Var.Map.Partition (ChorEnv.find B CE2) M1 M2 ->
        Var.Map.Properties.Disjoint (ChorEnv.find A CE1)
          (ChorEnv.find A (Actor.Map.add B M2 CE2)).
    Proof.
      intros X A B CE1 CE2 M1 M2 Hdisj Hpart.
      Var.Map.Tactics.reflect_partition.
      Var.simplify.
      Actor.Map.Tactics.compare A B; auto.
      rewrite Heq in Hdisj.
      Var.simplify.
    Qed.

    Lemma remove_dj : forall  (M1 : Var.Map.t Expr.typ) M2 x tau,
        Var.Map.Properties.Disjoint (Var.Map.add x tau M1) M2 -> 
        Var.Map.Properties.Disjoint M1 M2.
    Proof.
      intros M1 M2 x tau Hdisj.
      Var.simplify.
    Qed.

    Lemma remove_dj_env : forall (CE1 CE2 : ChorEnv.t Expr.typ) A B x,
        Var.Map.Properties.Disjoint (ChorEnv.find A CE1) (ChorEnv.find A CE2) -> 
        Var.Map.Properties.Disjoint
          (ChorEnv.find A (ChorEnv.remove B x CE1))
          (ChorEnv.find A CE2).
    Proof.
      intros.
      intros D. intros [Hin1 Hin2].
      
      (* Because D in find A (remove B x CE1), we know A <> B *)
      assert (A <> B).
      {
        intros ?; subst.
        unfold ChorEnv.remove, ChorEnv.find in Hin1.
        Actor.simplify.
        destruct (Actor.Map.find B CE1) as [CB1 | ] eqn:HB1.
        2:{ Var.simplify. }
        Var.simplify.
        apply (H D). split; auto.
        unfold ChorEnv.find. rewrite HB1. auto.
      }
      Var.simplify.
      destruct (Actor.eq_dec A B) as [Heq | ].
      { unfold Actor.eq in Heq. subst; contradiction. }
      apply (H D); auto.
    Qed.

    Lemma remove_add_dj_env : forall (CE1 CE2 : ChorEnv.t Expr.typ) A B x tau,
        Var.Map.Properties.Disjoint (ChorEnv.find A CE1) (ChorEnv.find A CE2) ->
        Var.Map.Properties.Disjoint
          (ChorEnv.find A (ChorEnv.remove B x CE1))
          (ChorEnv.find A (ChorEnv.add B x tau CE2)).
    Proof.
      intros.
      Var.simplify.
      Actor.Map.Tactics.compare A B; auto.
      {
        intros z [Hin1 Hin2].
        Var.simplify.
        destruct Hin2 as [? | Hin2]; [contradiction | ].
        apply (H z); auto.
      }
    Qed.

    Lemma add_empty_delta : forall A x tau (D : ChorEnv.t Expr.typ),
        ~ ChorEnv.Empty (ChorEnv.add A x tau D).
    Proof.
      intros. intros Hempty.
      unfold ChorEnv.add in Hempty.
      unfold ChorEnv.Empty in Hempty.
      specialize (Hempty A).
      ChorEnv.simplify.
      specialize (Hempty x).
      Var.simplify.
    Qed.

    Lemma empty_is_empty : forall {X : Type} A,
        Var.Map.Empty (ChorEnv.find A (Actor.Map.empty (Var.Map.t X))).
    Proof.
      intros.
      unfold ChorEnv.find.
      Actor.simplify.
      Var.simplify.
    Qed.

    Lemma empty_eq_env  : forall  {X : Type} (CE : ChorEnv.t X),
        Actor.Map.Empty CE ->
        ChorEnv.Equal CE (Actor.Map.empty (Var.Map.t X)).
    Proof.
      intros.
      unfold ChorEnv.Equal.
      intros.
      unfold ChorEnv.find.
      Actor.simplify.
      rewrite H.
      Actor.simplify.
    Qed.
      
    Lemma empty_map_empty : forall {X : Type}, Var.Map.Empty (Var.Map.empty X).
    Proof.
      intros.
      Var.simplify.
    Qed.

    Lemma empty_to_empty : forall  {X : Type} A (CE : ChorEnv.t X) (M : Var.Map.t X),
        Var.Map.Empty M ->
        Var.Map.Empty (ChorEnv.find A CE) -> 
        ChorEnv.Equal (Actor.Map.add A M CE) CE.
    Proof.
      intros. intros B.
      ChorEnv.simplify.
      rewrite H0.
      reflexivity.
    Qed.

    Lemma empty_to_empty_old : forall  {X : Type} A (M : Var.Map.t X),
        Var.Map.Empty M ->
        ChorEnv.Equal
          (Actor.Map.add A M (Actor.Map.empty (Var.Map.t X)))
          (Actor.Map.empty (Var.Map.t X)).
    Proof.
      intros. 
      pose proof (H0 := Var.Map.Proofs.empty_map_equal M H).
      rewrite H0.
      intros D. ChorEnv.simplify.
    Qed.

    Lemma find_empty : forall {X : Type} A,
        (ChorEnv.find A (Actor.Map.empty (Var.Map.t X))) =  (Var.Map.empty X).
    Proof.
      intros.
      unfold ChorEnv.find.
      Actor.simplify.
    Qed.

    Lemma empty_partition : forall (M M1 M2 : Var.Map.t Expr.typ),
        Var.Map.Empty M ->
        Var.Map.Partition M M1 M2 ->
        Var.Map.Empty M1.
    Proof.
      intros; Var.simplify.
    Qed.

    Lemma lopsided_partition : forall {X : Type} (M M1 : Var.Map.t X),
        Var.Map.Partition M (Var.Map.empty X) M1 ->
        Var.Map.Equal M M1.
    Proof.
      intros; Var.simplify.
    Qed.

    Lemma partition_lopsided : forall {X : Type} (M1 M2: Var.Map.t X),
        Var.Map.Partition M1 M1 M2 ->
        Var.Map.Equal M2 (Var.Map.empty X).
    Proof.
      intros.
      rewrite Var.Map.Proofs.partition_concat in H.
      destruct H as [Hdisj Heq].
      intros z. specialize (Heq z).
      Var.simplify.
      destruct (Var.Map.find z M1) eqn:H1; auto.
      destruct (Var.Map.find z M2) eqn:H2; auto.
      exfalso. apply (Hdisj z).
      split; Var.solve.
    Qed.

    Lemma find_add : forall {X : Type} A M (CE : ChorEnv.t X),
        ChorEnv.find A (Actor.Map.add A M CE) = M.
    Proof.
      intros.
      unfold ChorEnv.find.
      Actor.simplify.
    Qed.

    Lemma find_add_map : forall A x tau (CE : ChorEnv.t Expr.typ),
        Var.Map.Equal
          (ChorEnv.find A (ChorEnv.add A x tau CE))
          (Var.Map.add x tau (ChorEnv.find A CE)).
    Proof.
      intros.
      unfold ChorEnv.find.
      unfold ChorEnv.add.
      Actor.simplify.
    Qed.


    Lemma find_ab_neq1 : forall {X : Type} A B x tau (CE : ChorEnv.t X),
        A <> B ->
        (ChorEnv.find A (ChorEnv.add B x tau CE)) = (ChorEnv.find A CE).
    Proof.
      intros X A B x tau CE Hneq.
      unfold ChorEnv.find. unfold ChorEnv.add.
      Actor.simplify.
    Qed.

    Lemma find_ab_neq2 : forall {X : Type} A B M (CE : ChorEnv.t X),
        A <> B ->
        (ChorEnv.find A (Actor.Map.add B M CE)) = (ChorEnv.find A CE).
    Proof.
      intros.
      unfold ChorEnv.find.
      Actor.simplify.
    Qed.

    Lemma find_ab_neq3 : forall {X : Type} A B x (CE : ChorEnv.t X),
        A <> B ->
        (ChorEnv.find A (ChorEnv.remove B x CE)) = (ChorEnv.find A CE).
    Proof.
      intros X A B x CE Hneq.
      unfold ChorEnv.find. unfold ChorEnv.remove.
      Actor.simplify.
    Qed.

    Lemma find_nbeq : forall (CE : ChorEnv.t Expr.typ) A x B y tau,
        Insn.bind_eqb (A, x) (B, y) = false -> 
        ~ Var.Map.In x (ChorEnv.find A CE) ->
        ~ Var.Map.In x (ChorEnv.find A (ChorEnv.add B y tau CE)).
    Proof.
      intros CE A x B y tau Heq Hin.
      Var.simplify.
      unfold Insn.bind_eqb, Insn.bind_eq_dec in Heq; simpl in Heq.
      Actor.Map.Tactics.compare A B.
      * (* A = B*)
        Var.Map.Tactics.compare x y; try discriminate.
        (* x <> y *)
        Var.simplify.
      * (* A <> B *) auto.
    Qed.

    Lemma add_find : forall (CE : ChorEnv.t Expr.typ) A x tau,
        (ChorEnv.find A (ChorEnv.add A x tau CE)) = (Var.Map.add x tau (ChorEnv.find A CE)).
    Proof.
      intros.
      unfold ChorEnv.find, ChorEnv.add.
      Actor.simplify.
    Qed.

    Lemma remove_find : forall (CE : ChorEnv.t Expr.typ) A x,
        (ChorEnv.find A (ChorEnv.remove A x CE)) = (Var.Map.remove x (ChorEnv.find A CE)).
    Proof.
      intros.
      Var.simplify.
      Actor.simplify.
    Qed.

    Lemma add_remove : forall (CE : ChorEnv.t Expr.typ) M A x tau,
        Var.Map.MapsTo x tau M ->
        ChorEnv.Equal
          (ChorEnv.add A x tau (Actor.Map.add A (Var.Map.remove x M) CE))
          (Actor.Map.add A M CE).
    Proof.
      intros.
      unfold ChorEnv.add.
      Var.simplify. Actor.simplify.
      Var.simplify.
      rewrite Var.Map.Proofs.add_mapsto; auto.
      apply ChorEnv.actor_map_Equal.
      Actor.simplify.
    Qed.

    Lemma nin_remove : forall (M : Var.Map.t Expr.typ) x,
        ~ (Var.Map.In x (Var.Map.remove x M)).
    Proof.
      intros.
      Var.simplify.
    Qed.

    (* This is needed for dealing with classical variable shadowing *)
    Lemma nin_remove_ce : forall (CE : ChorEnv.t Expr.typ) A x B y,
        ~ (Var.Map.In x (ChorEnv.find A CE)) ->
        ~ (Var.Map.In x (ChorEnv.find A (ChorEnv.remove B y CE))).
    Proof.
      intros.
      Var.simplify. Actor.simplify.
      Var.simplify.
    Qed.

    Lemma nin_partition : forall x (M M1 M2 : Var.Map.t Expr.typ),
        ~ Var.Map.In x M ->
        Var.Map.Partition M M1 M2 ->
        ~ Var.Map.In x M1.
    Proof.
      intros.
      pose proof (Var.Map.Proofs.partition_not_in_inversion Expr.typ M M1 M2 x H0) as Hpni.
      destruct Hpni as [Hpni _].
      destruct (Hpni H).
      auto.
    Qed.

    Lemma partition_remove_all : forall (CE1 : ChorEnv.t Expr.typ) CE2 CE3 A B x,
        Var.Map.Partition (ChorEnv.find A CE1) (ChorEnv.find A CE2) (ChorEnv.find A CE3) ->
        Var.Map.Partition (ChorEnv.find A (ChorEnv.remove B x CE1))
          (ChorEnv.find A (ChorEnv.remove B x CE2))
          (ChorEnv.find A (ChorEnv.remove B x CE3)).
    Proof.
      intros.
      Var.simplify.
      Actor.simplify.
      Var.simplify.
    Qed.
      
    Lemma partition_remove : forall (Delta : Var.Map.t Expr.typ) Delta1 Delta2 x tau,
        Var.Map.Partition (Var.Map.add x tau Delta) Delta1 Delta2 ->
        ~ Var.Map.In x Delta ->
        ~ Var.Map.In x Delta1 ->
        Var.Map.Partition Delta Delta1 (Var.Map.remove x Delta2).
    Proof.
      intros Delta Delta1 Delta2 x tau Hpart H H1.
      apply Var.Map.Proofs.partition_add_inversion in Hpart; auto.
      destruct Hpart as [[Hmapsto [Hin2 Hpart]] | [Hin1 [Hmapsto2 Hpart]]].
      * contradict H1. exists tau; auto.
      * auto.
    Qed.  

    Lemma remove_add : forall x tau (Delta1 : Var.Map.t Expr.typ) Delta2,
        ~ Var.Map.In x Delta1 ->
        Var.Map.Equal Delta2 (Var.Map.add x tau Delta1) ->
        Var.Map.Equal (Var.Map.remove x Delta2) Delta1.
    Proof.
      intros.
      Var.simplify.
      apply Var.Map.Proofs.remove_not_in; auto.
    Qed.


    Lemma addadd3 :  forall (CE : ChorEnv.t Expr.typ) A x tau B M,
      A <> B -> 
      ChorEnv.Equal (Actor.Map.add B M (ChorEnv.add A x tau CE))
                    (ChorEnv.add A x tau (Actor.Map.add B M CE)).
    Proof.
      intros.
      unfold ChorEnv.add.
      Var.simplify. Actor.simplify.
      rewrite Actor.Map.Proofs.add_neq_sym; auto.
      reflexivity.
    Qed.

    Lemma addadd4 :  forall {X : Type} (CE : ChorEnv.t X) A MA B MB,
      A <> B -> 
      ChorEnv.Equal (Actor.Map.add B MB (Actor.Map.add A MA CE))
                    (Actor.Map.add A MA (Actor.Map.add B MB CE)).
    Proof.
      intros.
      rewrite Actor.Map.Proofs.add_neq_sym; auto.
      reflexivity.
    Qed.

    Lemma addadd5 : forall (CE : ChorEnv.t Expr.typ) A x taux B y tauy,
        Insn.bind_eqb (B, y) (A, x) = false ->
        ChorEnv.Equal (ChorEnv.add A x taux (ChorEnv.add B y tauy CE))
                      (ChorEnv.add B y tauy (ChorEnv.add A x taux CE)).
    Proof.
      intros.
      unfold Insn.bind_eqb, Insn.bind_eq_dec in H; simpl in H.
      Actor.simplify.
      2:{ unfold ChorEnv.add.
          rewrite Actor.Map.Proofs.add_neq_sym; auto.
          Var.simplify.
          Actor.simplify.
      }
      Var.simplify.
      unfold ChorEnv.add.
      repeat (Actor.simplify; Var.simplify).
      rewrite Var.Map.Proofs.add_neq_sym; auto.
      reflexivity.
    Qed.

    (* this lemma may help prove the preceding lemma. *)
    Lemma addadd6 : forall {X : Type} x taux y tauy (M : Var.Map.t X),
        x <> y -> 
        Var.Map.Equal (Var.Map.add y tauy (Var.Map.add x taux M))
                      (Var.Map.add x taux (Var.Map.add y tauy M)).
    Proof.
      intros.
      rewrite Var.Map.Proofs.add_neq_sym; auto.
      reflexivity.
    Qed.

    Lemma addadd8 : forall (CE : ChorEnv.t Expr.typ) A x tau M, 
        ChorEnv.Equal
          (Actor.Map.add A (Var.Map.add x tau M) CE)
          (ChorEnv.add A x tau (Actor.Map.add A M CE)).
    Proof.
      intros.
      unfold ChorEnv.add.
      repeat (Var.simplify; Actor.simplify).
    Qed.

    Lemma addadd9 : forall (CE : ChorEnv.t Expr.typ) A x taux y tauy,
        y <> x ->
        ChorEnv.Equal (ChorEnv.add A x taux (ChorEnv.add A y tauy CE))
                      (ChorEnv.add A y tauy (ChorEnv.add A x taux CE)).
    Proof.
      intros.
      assert (Insn.bind_eqb (A, y) (A, x) = false).
      destruct (Insn.bind_eqb_false (A, y) (A, x)).
      assert (~ Insn.bind_eq (A, y) (A, x)).
      unfold Insn.bind_eq.
      tauto.
      tauto.
      apply addadd5; auto.
    Qed.

    Lemma overwrite : forall (CE : ChorEnv.t Expr.typ) A x tau1 tau2,
        ChorEnv.Equal
          (ChorEnv.add A x tau1 (ChorEnv.add A x tau2 CE))
          (ChorEnv.add A x tau1 CE).
    Proof.
      intros.
      unfold ChorEnv.add.
      repeat (Actor.simplify; Var.simplify).
    Qed.

    Lemma remrem :  forall (CE : ChorEnv.t Expr.typ) A x y,
        ChorEnv.Equal
          (ChorEnv.remove A x (ChorEnv.remove A y CE))
          (ChorEnv.remove A y (ChorEnv.remove A x CE)).      
    Proof.
      intros.
      unfold ChorEnv.remove.
      repeat (Var.simplify; Actor.simplify).
      intros D. ChorEnv.simplify.
      rewrite Var.Map.Proofs.remove_swap.
      reflexivity.
    Qed.

    Lemma rmadd1 : forall (CE : ChorEnv.t Expr.typ) A x tau,
        ChorEnv.Equal
          (ChorEnv.remove A x (ChorEnv.add A x tau CE))
          (ChorEnv.remove A x CE).
    Proof.
      intros.
      unfold ChorEnv.remove, ChorEnv.add.
      repeat (Actor.simplify; Var.simplify).
    Qed.

    Lemma rmadd2 : forall (CE : ChorEnv.t Expr.typ) A B x y tau,
        Insn.bind_eqb (A, x) (B, y) = false ->
        ChorEnv.Equal
          (ChorEnv.remove B y (ChorEnv.add A x tau CE))
          (ChorEnv.add A x tau (ChorEnv.remove B y CE)).
    Proof.
      intros CE A B x y tau Heq.
      rewrite Insn.bind_eqb_false in Heq.
      unfold Insn.bind_eq in Heq; simpl in Heq.
      
      unfold ChorEnv.remove, ChorEnv.add.
      repeat (Actor.simplify; Var.simplify).

      rewrite Actor.Map.Proofs.add_neq_sym; auto.
      reflexivity.
    Qed.

    Lemma nin_mapl : forall (M : Var.Map.t Expr.typ)  x y tau,
        x <> y ->
        ~ Var.Map.In x M ->
        ~ Var.Map.In x (Var.Map.add y tau M).
    Proof.
      intros.
      Var.solve.
    Qed.

    Lemma nin_mapr : forall (M : Var.Map.t Expr.typ)  x y tau,
        x <> y ->
        ~ Var.Map.In x (Var.Map.add y tau M) ->
        ~ Var.Map.In x M.
    Proof.
      intros.
      Var.solve.
    Qed.

    Lemma nin_nxeq : forall (M : Var.Map.t Expr.typ)  x y tau,
        ~ Var.Map.In x (Var.Map.add y tau M) -> x <> y.
    Proof.
      intros.
      Var.solve.
    Qed.

    (* contrapositive of nin_mapl with mapsto rewrite *)
    Lemma map_in : forall (M : Var.Map.t Expr.typ)  x tau,
        Var.Map.MapsTo x tau M ->
        Var.Map.In x M.
    Proof.
      intros.
      Var.solve.
    Qed.
          

    Lemma nin_nbeq : forall (CE : ChorEnv.t Expr.typ) A x tau B y,
        ~ Var.Map.In y (ChorEnv.find B (ChorEnv.add A x tau CE)) ->
        Insn.bind_eqb (A, x) (B, y) = false.
    Proof.
      intros.
      apply Insn.bind_eqb_false.
      intros [? ?]; simpl in *; subst.
      repeat (Var.simplify; Actor.simplify).
    Qed.
          

    Lemma  contra_nin_nbeq : forall (CE : ChorEnv.t Expr.typ) A x tau B y,
        Insn.bind_eqb (A, x) (B, y) = true ->
        Var.Map.In y (ChorEnv.find B (ChorEnv.add A x tau CE)).
    Proof.
      intros CE A x tau B y H.
      apply Insn.bind_eqb_true in H.
      unfold Insn.bind_eq in H; simpl in H.
      destruct H; subst.
      repeat (Var.simplify; Actor.simplify).
    Qed.

    Lemma in_add : forall (M : Var.Map.t Expr.typ)  x tau,
        Var.Map.In x (Var.Map.add x tau M).
    Proof.
      intros.
      Var.simplify.
    Qed.
        
    Lemma in_beq : forall (CE : ChorEnv.t Expr.typ) A x tau,
        Var.Map.In x (ChorEnv.find A (ChorEnv.add A x tau CE)).
    Proof.
      intros.
      pose proof (contra_nin_nbeq CE A x tau A x).
      destruct (Insn.bind_eqb_true (A, x) (A, x)).
      destruct (Insn.beq (A,x) (A,x)).
      assert (Insn.bind_eqb (A, x) (A, x) = true).
      apply H1.
      apply H3.
      simpl.
      auto.
      apply (H H4). 
    Qed.

    Lemma nin_nbeq_add1 : forall (CE : ChorEnv.t Expr.typ) A x B y tau,
        Insn.bind_eqb (A, x) (B, y) = false ->
        ~ Var.Map.In x (ChorEnv.find A CE) ->
          ~ Var.Map.In x (ChorEnv.find A (ChorEnv.add B y tau CE)).
    Proof.
      intros CE A x B y tau Heq Hin.
      apply Insn.bind_eqb_false in Heq.
      unfold Insn.bind_eq in Heq; simpl in Heq.
      repeat (Var.simplify; Actor.simplify).
    Qed.

    Lemma nin_nbeq_add2 : forall (CE : ChorEnv.t Expr.typ) A x B y tau,
        Insn.bind_eqb (A, x) (B, y) = false ->
        ~ Var.Map.In x (ChorEnv.find A (ChorEnv.add B y tau CE))->
        ~ Var.Map.In x (ChorEnv.find A CE).
    Proof.
      intros CE A x B y tau Heq Hin.
      apply Insn.bind_eqb_false in Heq.
      unfold Insn.bind_eq in Heq; simpl in Heq.
      repeat (Var.simplify; Actor.simplify).
    Qed.

    Lemma nin_nbeq_add3 : forall (CE : ChorEnv.t Expr.typ) A x taux B y tauy,
        Insn.bind_eqb (A, x) (B, y) = false ->
        ChorEnv.MapsTo A x taux CE ->
        ChorEnv.MapsTo A x taux (ChorEnv.add B y tauy CE).
    Proof.
      intros CE A x taux B y tauy Heq Hin.
      apply Insn.bind_eqb_false in Heq.
      unfold Insn.bind_eq in Heq; simpl in Heq.
      unfold ChorEnv.MapsTo in *.
      repeat (Var.simplify; Actor.simplify).
      right. split; auto.
    Qed.

    Lemma ini : forall (Delta : Var.Map.t Expr.typ) Delta1 Delta2 x tau,
        Var.Map.Partition (Var.Map.add x tau Delta) Delta1 Delta2 ->
        ~ (Var.Map.In x Delta1) ->
        (Var.Map.MapsTo x tau Delta2).
    Proof.
      intros Delta Delta1 Delta2 x tau Hpart Hin.
      Var.reflect_find.
      Var.Map.Tactics.reflect_partition.
      specialize (Heq x). Var.simplify.
      rewrite Hin in Heq.
      Var.solve.
    Qed.

    Lemma inin : forall (Delta : Var.Map.t Expr.typ) Delta1 Delta2 x tau,
        Var.Map.Partition (Var.Map.add x tau Delta) Delta1 Delta2 ->
        (Var.Map.In x Delta1) ->
        (Var.Map.MapsTo x tau Delta1).
    Proof.
      intros ? ? ? ? ? Hpart Hin.
      Var.reflect_find.
      Var.Map.Tactics.reflect_partition.
      specialize (Heq x). Var.simplify.
      rewrite Hin in Heq. auto.
    Qed.

    Lemma nin : forall (Delta : Var.Map.t Expr.typ) Delta1' Delta1 Delta2 x tau,
        Var.Map.Equal (Var.Map.add x tau Delta1') Delta1 ->
        Var.Map.Partition (Var.Map.add x tau Delta) Delta1 Delta2 ->
        ~ (Var.Map.In x Delta) ->
        ~ (Var.Map.In x Delta1') ->
        ~ (Var.Map.In x Delta2) /\ Var.Map.Partition Delta Delta1' Delta2.
    Proof.
      intros ? ? ? ? ? ? Heq Hpart Hnin Hnin1. Var.simplify.
      apply Var.Map.Proofs.partition_add_inversion in Hpart; auto.
      destruct Hpart as [[? [? ?]] | [Hcontra _]].
      2:{
        contradict Hcontra.
        Var.simplify.
      }
      split; auto.
      Var.simplify.
      rewrite Var.Map.Proofs.remove_not_in in H1; auto.
    Qed.

    Lemma mapsto_destruct : forall {X : Type} x tau (M : Var.Map.t X) ,
        Var.Map.MapsTo x tau M ->
        (exists M', Var.Map.Equal M (Var.Map.add x tau M') /\ ~ Var.Map.In x M').
    Proof.
      intros.
      exists (Var.Map.remove x M).
      split.
      * Var.simplify. rewrite Var.Map.Proofs.add_mapsto; auto. reflexivity. 
      * Var.simplify.
    Qed.

    Lemma partitioning : forall  {X : Type} (M : Var.Map.t X) M0 M1 M2 M3,
        Var.Map.Partition M M1 M2 ->
        Var.Map.Partition M2 M0 M3 ->
        Var.Map.Partition (Var.Map.concat M1 M0) M1 M0 /\
          Var.Map.Partition (Var.Map.concat M1 M3) M1 M3 /\      
          Var.Map.Partition M (Var.Map.concat M1 M0) M3 /\
          Var.Map.Partition M M0 (Var.Map.concat M1 M3).
    Proof.
      intros.
      Var.Map.Tactics.reflect_partition. Var.simplify.
      split; [ | split; [ | split] ].
      * Var.Map.Tactics.reflect_partition; auto; reflexivity.
      * Var.Map.Tactics.reflect_partition; auto; reflexivity.
      * Var.Map.Tactics.reflect_partition; Var.simplify.
        rewrite Var.Map.Proofs.concat_assoc. reflexivity.
      * apply Var.Map.Properties.Disjoint_sym in H; auto.
        Var.Map.Tactics.reflect_partition; Var.simplify.
        repeat rewrite Var.Map.Proofs.concat_assoc.
        rewrite (Var.Map.Proofs.concat_sym M0 M1); auto; try reflexivity.
    Qed.

    Lemma map_partition_map : forall x tau (M : Var.Map.t Expr.typ) M1 M2,
        Var.Map.MapsTo x tau M2 ->
        Var.Map.Partition M M1 M2 ->
        Var.Map.MapsTo x tau M.
    Proof.
      intros x tau M M1 M2 HM2 Hpart.
      Var.Map.Tactics.reflect_partition.
      Var.solve.
      destruct (Var.Map.find x M1) eqn:HM1; auto.
      { (* x in M1 *)
        exfalso. apply (Hdisj x).
        split; Var.solve.
      }
    Qed.

    Lemma readd_eq: forall A x tau (CE : ChorEnv.t Expr.typ),
        Var.Map.MapsTo x tau (ChorEnv.find A CE) ->
        ChorEnv.Equal (ChorEnv.add A x tau CE) CE.
    Proof.
      intros A x tau CE Hmapsto.
      unfold ChorEnv.add, ChorEnv.find in *.
      destruct (Actor.Map.find A CE) as [ctx | ] eqn:Hfind.
      2:{ Var.simplify. }
      ChorEnv.solve.
      unfold ChorEnv.find.
      rewrite Hfind. Var.solve.
    Qed.

    Lemma remove_add_partition : forall (CE1 CE2 CE3: ChorEnv.t Expr.typ) A B x tau,
        Var.Map.Partition (ChorEnv.find A CE1)
          (ChorEnv.find A CE2) (ChorEnv.find A CE3) ->
        Var.Map.MapsTo x tau (ChorEnv.find B CE1) ->
        Var.Map.Partition (ChorEnv.find A CE1)
          (ChorEnv.find A (ChorEnv.add B x tau CE2))
          (ChorEnv.find A (ChorEnv.remove B x CE3)).
    Proof.
      intros ? ? ? ? ? ? ? Hpart Hmapsto.
      unfold ChorEnv.remove, ChorEnv.add, ChorEnv.find in *.
      Actor.simplify. Var.simplify.
        destruct (Actor.Map.find B CE1) as [ctx1 | ] eqn:HB1;
        destruct (Actor.Map.find B CE2) as [ctx2 | ] eqn:HB2;
        destruct (Actor.Map.find B CE3) as [ctx3 | ] eqn:HB3;
          Var.simplify.
      * Var.Map.Tactics.reflect_partition.
        2:{
          Var.simplify.
          intros D. Var.simplify.
          Var.reflect_find. auto.
        }

        rewrite Var.Map.MProofs.Proofs.disjoint_add_1.
        split; auto.
        { apply Var.Map.Proofs.disjoint_remove_2; auto. }
        Var.simplify.

      * Var.Map.Tactics.reflect_partition.
        2:{
          Var.simplify.
          intros y. Var.reflect_find; auto.
          destruct (Var.Map.find y ctx1); auto.
        }
        apply Var.Map.Proofs.disjoint_empty_2.

      * Var.Map.Tactics.reflect_partition.
        2:{
          Var.simplify.
          intros y. Var.reflect_find; auto.
        }
        Var.simplify. split; [ | intros [? ?]; contradiction].
        Var.simplify.
    Qed.

      
    Lemma map_subset_add' : forall A B y tau (CE1 : ChorEnv.t Expr.typ) CE2 CE3,
        ~ Var.Map.In y (ChorEnv.find B CE3) ->
        Var.Map.Partition (ChorEnv.find A CE1) (ChorEnv.find A CE2) (ChorEnv.find A CE3) ->
        Var.Map.Partition
          (ChorEnv.find A (ChorEnv.add B y tau CE1))
          (ChorEnv.find A (ChorEnv.add B y tau CE2)) (ChorEnv.find A CE3).
    Proof.
      intros.
      Var.simplify.
      Actor.Map.Tactics.compare A B; subst; auto.
      apply Var.Map.Proofs.partition_add_l; auto.
    Qed.

    Lemma map_subset_add : forall A B y tau (CE1 : ChorEnv.t Expr.typ) CE2 CE3,
        Var.Map.Partition (ChorEnv.find A CE1) (ChorEnv.find A CE2) (ChorEnv.find A CE3) ->
        Var.Map.Partition
          (ChorEnv.find A (ChorEnv.add B y tau CE1))
          (ChorEnv.find A (ChorEnv.add B y tau CE2)) (ChorEnv.find A (ChorEnv.remove B y CE3)).
    Proof.
      intros.
      Var.simplify.
      Actor.Map.Tactics.compare A B; subst; auto.
      Var.Map.Tactics.reflect_partition.
      * Var.simplify. 
        split; [ | intros [? ?]; try contradiction].
        intros z [Hin1 Hin2].
        Var.simplify.
        apply (Hdisj z); auto.
      * Var.simplify.
        rewrite Heq.
        Var.solve.
    Qed.

    Lemma add_mapsto : forall x (tau : Expr.typ) m,
        Var.Map.MapsTo x tau m ->
        Var.Map.Equal (Var.Map.add x tau m) m.
    Proof.
      intros. Var.solve.
    Qed.

    Lemma rem_empty : forall {X : Type} A x,
        ChorEnv.Equal
          (ChorEnv.remove A x (Actor.Map.empty (Var.Map.t X)))
          (Actor.Map.empty (Var.Map.t X)).
    Proof.
      intros.
      unfold ChorEnv.Equal.
      intro.
      unfold ChorEnv.remove.
      Var.simplify.
      Actor.simplify.
      Var.simplify.
    Qed.

    Lemma rem_empty2 : forall {X : Type} A x (CE : ChorEnv.t X),
        Var.Map.Empty (ChorEnv.find A CE) -> 
        ChorEnv.Equal (ChorEnv.remove A x CE) CE.
    Proof.
      intros X A x CE H.
      intros B.
      ChorEnv.simplify.
      rewrite H.
      Var.simplify.
    Qed.

    Lemma members_dj : forall A B AS1 AS2,
        Actor.FSet.Empty (Actor.FSet.inter AS1 AS2) ->
        Actor.FSet.In A AS1 -> 
        Actor.FSet.In B AS2 ->
        A <> B.
    Proof.
      intros A B AS1 AS2 Hinter HA HB Heq; subst.
      apply (Hinter B).
      Actor.simplify.
    Qed.

    Lemma inter_nin : forall A AS1 AS2,
        Actor.FSet.Empty (Actor.FSet.inter AS1 AS2) ->
        Actor.FSet.In A AS2 -> 
        ~ Actor.FSet.In A AS1.
    Proof.
      intros A AS1 AS2 Hinter Hnin HH; subst.
      apply (Hinter A).
      Actor.simplify.
    Qed.

    Lemma singleton_nin : forall A B,
        ~ Actor.FSet.In A (Actor.FSet.singleton B) ->
        A <> B.
    Proof.
      intros.
      Actor.simplify.
    Qed.

    Lemma concat_partition : forall {X : Type} (M1 M2 : Var.Map.t X),
        Var.Map.Properties.Disjoint M1 M2 ->
        Var.Map.Partition (Var.Map.concat M1 M2) M1 M2.
    Proof.
      intros.
      Var.simplify.
    Qed.

    Lemma concat_partition_eq : forall {X : Type} (M M1 M2 : Var.Map.t X),
        Var.Map.Partition M M1 M2 ->
        Var.Map.Equal (Var.Map.concat M1 M2) M.
    Proof.
      intros.
      pose proof (Var.Map.Proofs.partition_concat M M1 M2).
      destruct H0. 
      destruct (H0 H).
      rewrite <- H3.
      Var.simplify.
    Qed.

    Lemma dj_concat_dj : forall {X : Type} (M M1 M2 : Var.Map.t X),
        Var.Map.Properties.Disjoint M1 M ->
        Var.Map.Properties.Disjoint M2 M ->
        Var.Map.Properties.Disjoint M1 M2 ->
        Var.Map.Properties.Disjoint (Var.Map.concat M1 M) M2.
    Proof.
      intros.
      Var.simplify.
    Qed.

    Lemma partition_concat_assoc : forall {X : Type} (M M1 M2 M3 : Var.Map.t X),
        Var.Map.Properties.Disjoint M1 (Var.Map.concat M2 M3) ->
        Var.Map.Properties.Disjoint M2 M3 ->
        Var.Map.Partition M M1 (Var.Map.concat M2 M3) ->
        Var.Map.Partition M (Var.Map.concat M3 M1) M2.
    Proof.
      intros.
      Var.Map.Tactics.reflect_partition; Var.simplify.
      rewrite (Var.Map.Proofs.concat_sym M3 M1); auto with extra_var_db.
      rewrite <- Var.Map.Proofs.concat_assoc.
      rewrite (Var.Map.Proofs.concat_sym M2 M3); auto.
      reflexivity.
    Qed.
    (* STOP Easily(?) proven facts *)  

End HelperLemmas.



Lemma bangty_inversion : forall Gamma Delta Theta e tau,
    Expr.WellTyped Gamma Delta Theta (Expr.Bang e) (Expr.BANG tau) ->
    Expr.WellTyped Gamma Delta Theta e tau /\
      Var.Map.Equal Delta (Var.Map.empty Expr.typ) /\
      Var.Map.Equal Theta (Var.Map.empty nat).
Proof.
  intros. 
  inversion H; subst.
  split; auto.
  split.
  Var.simplify.
  Var.simplify.
Qed.

Lemma qref_ty : forall Gamma Delta Theta q idx,
    Var.Map.Empty Delta ->
    Var.Map.Singleton q idx Theta ->
    Expr.WellTyped Gamma Delta Theta (Expr.QRef q) Expr.QUBIT.
Proof.
  intros.
  eapply Expr.WTQRef; eauto.
Qed.