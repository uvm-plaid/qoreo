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

Definition fresh_in_teleport q := q = 10.

(* TODO: improve tactics for typechecking! *)
Lemma WellTyped_teleport : forall Alice Bob q C,
  Alice <> Bob ->
  fresh_in_teleport q (* ensure q is fresh in teleport *) ->
  WellTyped ChorEnv.empty (ChorEnv.add Bob q QUBIT ChorEnv.empty) ChorEnv.empty C ->
  WellTyped ChorEnv.empty (ChorEnv.add Alice q QUBIT ChorEnv.empty) ChorEnv.empty
    (mk (teleport Alice Bob q) ++ C)%list.
Proof.
  intros Alice Bob q C Hneq Hfresh HWT.
  remember (mk (teleport Alice Bob q)) as C0 eqn:HC0.
  cbv in HC0. subst.
  unfold fresh_in_teleport in Hfresh; subst.

  unfold ChorEnv.empty in *.
  solve_wt ; ChorEnv.simplify.

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
  2:{ auto. }


  ChorEnv.simplify.
  right_associate Alice. ChorEnv.simplify. 
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

  right_associate Alice. ChorEnv.simplify.
  econstructor.
  { repeat (solve_wt; ChorEnv.simplify). }
  2:{
    ChorEnv.simplify.
    instantiate (1 := (Var.Map.add 3 QUBIT (Var.Map.empty typ))).
    repeat (solve_wt; ChorEnv.simplify).
  }
  2:{ ChorEnv.simplify. auto with var_db. }
  2:{ Var.simplify. }

  right_associate Alice. ChorEnv.simplify.  

  econstructor.
  { repeat (solve_wt; ChorEnv.simplify). }
  2:{
    ChorEnv.simplify.
    instantiate (1 := (Var.Map.add 5 (BANG BIT) (Var.Map.empty typ))).
    repeat (solve_wt; ChorEnv.simplify).
    rewrite Var.Map.Proofs.add_neq_sym; auto.
    reflexivity.
  }
  2:{ ChorEnv.simplify. auto with var_db. }
  2:{ Var.simplify. }

  right_associate Alice. ChorEnv.simplify.

  econstructor; auto.
  { ChorEnv.simplify. repeat (solve_wt; ChorEnv.simplify). }
  2:{
    ChorEnv.simplify.
    instantiate (1 := (Var.Map.add 6 (BANG BIT) (Var.Map.empty typ))).
    repeat (solve_wt; ChorEnv.simplify).
    Var.solve.
  }
  2:{ ChorEnv.simplify. auto with var_db. }

  right_associate Alice. ChorEnv.simplify.
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


  right_associate Alice. ChorEnv.simplify.
Require Import Lia.
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

  unfold ChorEnv.remove. ChorEnv.simplify.

  eapply Choreography.weakening_gen with (G := Actor.Map.empty (Var.Map.t typ)) (G0 := ChorEnv.add Bob 8 BIT (ChorEnv.add Bob 7 BIT (Actor.Map.empty _))).
  2:{
    intros B. split. ChorEnv.simplify; auto with var_db.
    ChorEnv.simplify. repeat solve_wt; auto with var_db; lia.
  }

  ChorEnv.simplify.
  assert (Heq' :ChorEnv.Equal (Actor.Map.remove Alice (Actor.Map.empty (Var.Map.t typ)))
                (Actor.Map.empty (Var.Map.t typ))).
  { ChorEnv.solve. }
  rewrite Heq'; clear Heq'.

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
