From Stdlib Require Import String.
From Qoreo Require Import Base Expr Choreography.
From QoreoExamples Require Import HOASNotation.

Open Scope string_scope.
Open Scope example_scope.

Notation var A := Var.t.


(* Distributed CNOT gate *)
Definition DCNOT (Alice Bob : Actor.t) (qA : var Alice) (qB : var Bob) : Qoreo (var Alice * var Bob) :=
      (* Alice and Bob establish an entangled pair of qubits. *)
      do ( a , b ) ← get_entangled_pair Alice Bob ;;

      (* Alice entangles qA with a and measures *)
      do (qA,a) ← Alice [-- Unitary CNOT (Pair qA a) -] ;;
      do x ← Alice [- Meas a -] ;;

      (* Bob entangles qB with b and measures *)
      do (b,qB) ← Bob [-- Unitary CNOT (Pair b qB) -] ;;
      do z ← Bob [- Meas (Unitary H b) -] ;;

      (* Alice and Bob exchange bits *)
      do x ← send Alice x Bob ;;
      do z ← send Bob z Alice ;;
      
      (* Alice and Bob make corrections *)
      do qA ← Alice [- If z (Unitary Z qA) qA -] ;;
      do qB ← Bob   [- If x (Unitary X qB) qB -] ;;
      ret (qA, qB).


(* Distributed controlled unitary *)
Definition distrubuted_ctrl_U Alice Bob q tgt (ctrl_U_circ : Var.t -> Var.t -> Expr.t) : Qoreo (Var.t * Var.t) :=
    do (a,b) ← get_entangled_pair Alice Bob ;;
    do (q,a) ← Alice [-- Unitary CNOT (Pair q a) -] ;;
    do z     ← Alice [- Meas a -] ;;
    do z     ← send Alice z Bob ;;

    do tgt   ← Bob [- If z (Unitary Z tgt) tgt -] ;;

    (* controlled unitary *)
    do (b, tgt) ← Bob [-- ctrl_U_circ b tgt -];;

    do x     ← Bob [- Meas (Unitary H b) -] ;;
    do x     ← send Bob x Alice ;;
    do q     ← Alice [- If x (Unitary X q) q -];;
    ret (q, tgt).

Fixpoint fold {X} (As : list Actor.t) (qs : list Var.t) (C : Actor.t -> Var.t -> Qoreo X) (default : X) : Qoreo X :=
    match As, qs with
    | [], _ | _, [] => ret default 
    | A::As', q::qs' =>
        do default ← C A q ;;
        fold As' qs' C default
    end.
Fixpoint fmap {X} (As : list Actor.t) (qs : list Var.t) (C : Actor.t -> Var.t -> Qoreo X) : Qoreo (list X) :=
    match As, qs with
    | [], _ | _, [] => ret []
    | A::As', q::qs' =>
        do v ← C A q ;;
        do vs ← fmap As' qs' C ;;
        ret (v::vs)
    end.
Fixpoint fmap2 {X} (As : list Actor.t) (qs1 qs2 : list Var.t) (C : Actor.t -> Var.t -> Var.t -> Qoreo X) : Qoreo (list X) :=
    match As, qs1, qs2 with
    | [], _, _ | _, [], _ | _, _, [] => ret []
    | A::As', q1::qs1', q2 :: qs2' =>
        do v ← C A q1 q2 ;;
        do vs ← fmap2 As' qs1' qs2' C ;;
        ret (v::vs)
    end.

(* n-ary distributed controlled unitary on n actors. See ``A general protocol for distributed quantum gates'' by Sarvaghad-Moghaddam, Zomorodi-Moghadam, and Farouk. https://arxiv.org/pdf/1812.07798 *)
Definition distributed_n_ctrl_U (CU : list Var.t -> Var.t -> Qoreo (list Var.t * Var.t)) 
                                (As : list Actor.t) (qs : list Var.t)
                                (B : Actor.t) (tgt : Var.t)
                              : Qoreo (list Var.t * Var.t) :=

    let stage1 := fun (A : Actor.t) (q : Var.t) => (* : Qoreo (Var.t * Var.t)  *)
        do (a,b) ← get_entangled_pair A B ;;
        do (q,a) ← A [-- Unitary CNOT (Pair q a) -] ;;
        do x     ← send A (Meas a) B ;;
        do b ← B [- If x (Unitary X b) b -];;
        ret (q, b) : Qoreo (Var.t * Var.t) in

    let stage3 := fun A q b => (* : Qoreo Var.t *)
        do z ← send B (Meas (Unitary H b)) A ;;
        do q ← B [- If z (Unitary Z q) q -];;
        ret q in

    (* Stage 1:As performs local operations  *)
    do qs_bs_list ← fmap As qs stage1 ;;
    (* split up qs_bs_list : list (Var.t * Var.t) into a pair of lists *)
    let (qs, bs) := List.split qs_bs_list in

    (* Stage 2: B applies ctrl-U gate locally using bs to control tgt*)
    do (qs, tgt) ← CU bs tgt ;;

    (* Stage 3: B sends corrections back to As *)
    do qs ← fmap2 As qs bs stage3 ;;
    
    ret (qs, tgt).
    




(* Implement an n-qubit GHZ state using distributed unitaries *)
(* We assume that A performs distributed CNOT gates with its qubit q and all the actors in Bs *)
Definition DCNOTs (A : Actor.t) (q : var A) (Bs : list Actor.t) : Qoreo (var A * list Var.t).
    revert q. induction Bs as [ | B Bs' ]; intros q.
    { exact (ret (q, nil)). }
      refine(     do b ← B [- New (Bit false) -] ;;
                  do (q,b) ← DCNOT A B q b ;;
                  do (q,ls) ← IHBs' q ;;
                  ret (q,b::ls)
      ).
Defined. (* Seems to be having trouble checking termination. Frustrating. *)

Definition DGZH (As : list Actor.t) (K : list Var.t -> Qoreo unit) : Qoreo unit :=
    match As with
    | nil => ret tt
    | A :: Bs =>
        do q ← A  [- Unitary H (New (Bit false)) -];;
        do (q, ls) ← DCNOTs A q Bs ;;
        K (q :: ls)
    end.

(* Distributed variational algorithm (VQA) taken from Distributed Quantum Computing - A Survey (Caleffi) - Fig 10 *)
(* Assume we have a parameterized RY/RZ rotation gates *)
From QuantumLib Require Import Complex.
Definition RZ (theta : R) : unitary. Admitted.
Definition RY (theta : R) : unitary. Admitted.

Record dvar_params := {
    t1 : R ; t2 : R ; t3 : R ; t4 : R ; t5 : R ; t6 : R ; t7 : R ; t8 : R ; t9 : R ; t10 : R
}.


(* q1 owned by Alice, q2/q3 owned by Bob *)
(* The function `success` takes the three qubits' measurement results and returns a measurement of success *)
Definition DVQA (Alice Bob : Actor.t) (params : dvar_params) (success : Expr.t) : Qoreo unit :=
    (* Layers 1 and 2 of rotations *)
    do q1 ← Alice [- Unitary (RZ (t4 params)) (Unitary (RY (t1 params)) (New (Bit false))) -];;
    do q2 ← Bob   [- Unitary (RZ (t5 params)) (Unitary (RY (t2 params)) (New (Bit false))) -];;
    do q3 ← Bob   [- Unitary (RZ (t6 params)) (Unitary (RY (t3 params)) (New (Bit false))) -];;

    (* Establish entanglement *)
    do (a,b) ← get_entangled_pair Alice Bob ;;

    (* Alice entangles q1 with a and sends X correction to Bob *)
    do (q1,a) ← Alice [-- Unitary CNOT (Pair q1 a) -];;
    do x ← Alice [- Meas a -] ;;
    do x ← send Alice x Bob ;;
    do b ← Bob [- If x (Unitary X b) b -] ;;

    (* Bob entangles b with q2 and q3 and sends Z correction back to Alice *)
    do (b,q2) ← Bob [-- Unitary CNOT (Pair b q2) -];;
    do (b,q3) ← Bob [-- Unitary CNOT (Pair b q3) -];;
    do z ← Bob [- Meas (Unitary H b) -];;
    do z ← send Bob z Alice ;;
    do q1 ← Alice [- If z (Unitary Base.Z b) b -];;

    (* Layers 3 and 4 of rotations *)
    do q1 ← Alice [- Unitary (RZ (t8 params)) (Unitary (RY (t7 params)) q1) -];;
    do (q2,q3) ← Bob [-- Unitary CNOT (Pair q2 q3) -];;
    do q2 ← Bob [- Unitary (RY (t9 params)) q2 -];;
    do q3 ← Bob [- Unitary (RZ (t10 params)) q3 -];;

    (* Alice and Bob measure their results; Bob sends results to Alice *)
    do v1 ← Alice [- Meas q1 -] ;;
    do v2 ← send Bob (Meas q2) Alice ;;
    do v3 ← send Bob (Meas q3) Alice ;;

    do _ ← Alice [!- App (App (App success v1) v2) v3 -] ;;
    ret tt.
    

(** Entanglement swapping *)

(*
(* Assume that A & B share a bell state, and C & D share a Bell state; after entanglement-swapping, A & D will share a Bell state *)
*)