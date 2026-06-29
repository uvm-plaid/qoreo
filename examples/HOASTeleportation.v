From Stdlib Require Import String.
From Qoreo Require Import Base Expr Choreography.
From QoreoExamples Require Import HOASNotation.

Open Scope string_scope.
Open Scope example_scope.


Definition teleport (Alice Bob : Actor.t) (q : Var.t) : Qoreo Var.t :=
      (* Alice and Bob establish an entangled pair of qubits. *)
      do ( a , b ) ← get_entangled_pair Alice Bob ;;
      
      (* Alice performs some local operations
         and obtains classical bits x and z. *)
      do (q,a) ← Alice [-- Unitary CNOT (Pair q a) -] ;;
      do q     ← Alice [- Unitary H q -] ;;
      do x ← Alice [- Meas q -];;
      do z ← Alice [- Meas a -];;

      (* Alice sends x and z to Bob. *)
      do x ← send Alice x Bob ;;
      do z ← send Alice z Bob ;;

      (* Bob uses x and z to update his qubit. *)
      do b ← Bob [- If z (Unitary Z b) b -];;
      do b ← Bob [- If x (Unitary X b) b -];;
      ret b.

About Choreography.WellTyped.
Import Actor.Map.
Require Import Lia.

Lemma remove_empty : forall A x T,
  ChorEnv.Equal (ChorEnv.remove A x (empty (Var.Map.t T))) (empty _).
Admitted.
Hint Rewrite remove_empty : var_db.

Definition singleton {T} x (tau : T) := Var.Map.add x tau (Var.Map.empty T).
Lemma wtqvar : forall x (τ : typ),
  Expr.WellTyped (Var.Map.empty _) (Var.Map.add x τ (Var.Map.empty _)) (Var.Map.empty _) (Expr.Var x) τ.
Proof.
  intros. econstructor; eauto; Var.simplify.
Qed.
Lemma wtbit : forall Γ b,
  Expr.WellTyped Γ (Var.Map.empty _) (Var.Map.empty _) (Bit b) BIT.
Proof. intros. econstructor; eauto; Var.simplify. Qed.

Lemma wtqref : forall Γ q (idx : nat),
  Expr.WellTyped Γ (Var.Map.empty _) (Var.Map.add q idx (Var.Map.empty _)) (QRef q) QUBIT.
Proof. intros. econstructor; eauto; Var.simplify. Qed.


Ltac solve_wt :=
  match goal with
  | [ |- Expr.WellTyped _ _ _ (Expr.Var ?q) _ ] => apply wtqvar
  | [ |- Expr.WellTyped _ _ _ (Bit _) _] => apply wtbit
  | [ |- Expr.WellTyped _ _ _ (QRef _) _] => apply wtqref
  | [ |- Expr.WellTyped _ _ _ _ _] => econstructor; auto; try reflexivity
  | [ |- Choreography.WellTyped _ _ _ _] => econstructor; auto; try reflexivity

  | [ |- Var.Map.Partition _ _ _ ] => Var.Map.Tactics.reflect_partition
  | [ |- _ /\ _ ] => split; auto
  | [ |- ~ (_ \/ _)] => intros [? | ?]; subst; try contradiction
  end.


Lemma ce_add_empty : forall T (m : ChorEnv.t T) A,
  ChorEnv.Equal
    (Actor.Map.add A (Var.Map.empty _) m)
    (Actor.Map.remove A m).
Proof.
  intros T m A.
  intros B. ChorEnv.simplify.
Qed.
Hint Rewrite ce_add_empty : var_db.
Hint Rewrite @Choreography.addadd2 : var_db.

Lemma ce_remove_empty : forall A,
    ChorEnv.Equal (Actor.Map.remove A (Actor.Map.empty (Var.Map.t nat))) (Actor.Map.empty _).
Proof. intros. ChorEnv.simplify. Qed.
Hint Rewrite ce_remove_empty : var_db.

(* TODO: improve tactics for typechecking! *)
Lemma WellTyped_teleport : forall Alice Bob q C,
  Alice <> Bob ->
  q = 10 (* ensure q is fresh in teleport *) ->
  WellTyped (empty _) (ChorEnv.add Bob q QUBIT (empty _)) (empty _) C ->
  WellTyped (empty _) (ChorEnv.add Alice q QUBIT (empty _)) (empty _)
    (mk (teleport Alice Bob q) ++ C)%list.
Proof.
  intros Alice Bob q C Hneq Hfresh HWT.
  remember (mk (teleport Alice Bob q)) as C0 eqn:HC0.
  cbv in HC0. subst.

  solve_wt; ChorEnv.simplify.

  econstructor.
  { repeat (solve_wt; ChorEnv.simplify). }
  2:{
    ChorEnv.simplify.
    Var.Map.Tactics.reflect_partition.
    { apply Var.Map.Proofs.disjoint_empty_2. }
    { Var.solve. }
  }
  2:{
    Var.Map.Tactics.reflect_partition.
    apply Var.Map.Proofs.disjoint_empty_2.
    Var.solve.
  }
  2:{ Var.simplify. }
  2:{ Var.simplify. }


  ChorEnv.simplify.
  econstructor.
  { repeat (solve_wt; ChorEnv.simplify). }
  2:{
    ChorEnv.simplify.
    instantiate (1 := (Var.Map.add 3 QUBIT (Var.Map.empty typ))).
    repeat (solve_wt; ChorEnv.simplify).
  }
  2:{
    ChorEnv.simplify.
    auto with var_db.
  }
  2:{ Var.simplify. }


  ChorEnv.simplify.
  econstructor.
  { repeat solve_wt. }
  2:{
    ChorEnv.simplify.
    instantiate (1 := (Var.Map.add 3 QUBIT (Var.Map.empty typ))).
    repeat (solve_wt; ChorEnv.simplify).
  }
  2:{ ChorEnv.simplify. auto with var_db. }
  2:{ Var.simplify. }

  ChorEnv.simplify.
  match goal with
  | [ |- WellTyped _ ?D _ _ ] =>
    assert (Heq : ChorEnv.Equal D (ChorEnv.add Alice 5 (BANG BIT) (ChorEnv.add Alice 3 QUBIT (ChorEnv.add Bob 1 QUBIT (empty (Var.Map.t _))))))
  end.
  { intros D. ChorEnv.simplify. }
  rewrite Heq. clear Heq.

  econstructor.
  { repeat solve_wt. }
  2:{
    ChorEnv.simplify.
    instantiate (1 := (Var.Map.add 5 (BANG BIT) (Var.Map.empty typ))).
    repeat (solve_wt; ChorEnv.simplify).
    Search (Var.Map.add _ _ (Var.Map.add _ _ _)).
    rewrite Var.Map.Proofs.add_neq_sym; auto.
    reflexivity.
  }
  2:{ ChorEnv.simplify. auto with var_db. }
  2:{ Var.simplify. }

  ChorEnv.simplify. unfold ChorEnv.add. ChorEnv.simplify.

  econstructor; auto.
  { repeat solve_wt. }
  2:{
    ChorEnv.simplify.
    instantiate (1 := (Var.Map.add 6 (BANG BIT) (Var.Map.empty typ))).
    repeat (solve_wt; ChorEnv.simplify).
    Var.solve.
  }
  2:{ ChorEnv.simplify. auto with var_db. }

  ChorEnv.simplify.
  econstructor; auto.
  { ChorEnv.simplify.
    solve_wt.
  }
  2:{
    ChorEnv.simplify.
    instantiate (1 := (Var.Map.empty typ)).
    repeat (solve_wt; ChorEnv.simplify).
  }
  2:{ ChorEnv.simplify. auto with var_db. }


  ChorEnv.simplify.
  match goal with
  | [ |- WellTyped _ ?D _ _ ] =>
    assert (Heq : ChorEnv.Equal D (ChorEnv.add Bob 1 QUBIT (empty _)))
  end.
  { intros B. ChorEnv.simplify. }
  rewrite Heq. clear Heq.
  econstructor; auto.
  {
    ChorEnv.simplify.
    solve_wt.
    { apply Expr.WTCVar; Var.simplify; eauto with var_db. }
    { apply Expr.weakening. solve_wt. solve_wt; eauto with var_db.
      Var.simplify. repeat solve_wt; auto with var_db. lia. lia.
    } 
    { apply Expr.weakening. solve_wt.
      Var.simplify. repeat solve_wt; auto with var_db. lia. lia.
    }
    { auto with var_db. }
    { auto with var_db. }
  }
  2:{
    ChorEnv.simplify.
    auto with var_db.
  }
  2:{ ChorEnv.simplify. auto with var_db. }
  2:{ Var.simplify. }

  ChorEnv.simplify. simpl.
  econstructor; auto.
  {
    ChorEnv.simplify.
    solve_wt.
    { apply Expr.WTCVar; Var.simplify; eauto with var_db. }
    { apply Expr.weakening. solve_wt. simpl. solve_wt; eauto with var_db.
      Var.simplify. repeat solve_wt; auto with var_db. lia.
    } 
    { apply Expr.weakening. solve_wt.
      Var.simplify. repeat solve_wt; auto with var_db. lia.
    }
    { auto with var_db. }
    { auto with var_db. }
  }
  2:{
    ChorEnv.simplify.
    auto with var_db.
  }
  2:{ ChorEnv.simplify. auto with var_db. }
  2:{ Var.simplify. }

  ChorEnv.simplify.
  match goal with
  | [ |- WellTyped ?G ?D _ _ ] =>
    assert (Heq : ChorEnv.Equal G (ChorEnv.add Bob 8 BIT (ChorEnv.add Bob 7 BIT (Actor.Map.empty _))));
    [ | assert (Heq' : ChorEnv.Equal D (ChorEnv.add Bob 10 QUBIT (empty _)))]
  end.
  { intros B. ChorEnv.simplify. }
  { intros B. ChorEnv.simplify. }
  rewrite Heq, Heq'. clear Heq Heq'.

  eapply Choreography.weakening_gen with (G := empty (Var.Map.t typ)) (G0 := ChorEnv.add Bob 8 BIT (ChorEnv.add Bob 7 BIT (empty _))).
  2:{
    intros B. split. ChorEnv.simplify; auto with var_db.
    ChorEnv.simplify. repeat solve_wt; auto with var_db; lia.
  }
  auto.
Qed.

Definition choreo : Choreography.t :=
  mk (
    do q ← "alice" [- Unitary H (New (Bit false))-] ;;
    teleport "alice" "bob" q
  ).

Eval compute in choreo.

Eval compute in (Network.epp "alice" choreo).
(*
  do q ← Unitary H (New (Bit false)) ;;
  do a ← establish_entanglement Bob ;;
  do (q,a) ← Unitary CNOT (q,a) ;;
  do q ← unitary H q ;;
  do x ← Meas q ;;
  do z ← Meas a ;;
  do _ ← Send Bob x ;;
  Send Bob z
*)


Eval compute in (Network.epp "bob" choreo).
(*
  do b ← establish_entanglement Alice ;;
  do x ← Receive Alice ;;
  do z ← Receive Alice ;;
  do b ← If z (Unitary Z b) b ;;
  If x (Unitary X b) b
*)


Eval compute in (Network.epp "bob" choreo).


Definition parties : list Actor.t :=
  ["alice"; "bob"].


Import ExampleExtraction.
From Stdlib Require Import extraction.ExtrOcamlNativeString.
From Qoreo Require Import NetQasm.

Definition apps : option (list AppFile.t) :=
    ExampleExtraction.render_parties choreo parties.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Extraction "teleportation_netqasm.ml" apps.
