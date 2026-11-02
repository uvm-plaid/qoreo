
From Stdlib Require Import String List QArith.
From Qoreo.Base Require Import Config Var Actor.
From Qoreo.Expr Require Import Expr.
From Qoreo.Choreography Require Import Choreography.
From Qoreo.Network Require Import Network.
From Qoreo.Choreography Require Import Notation.
(*From QoreoExamples Require Import Notation.*)
(*Import ExampleExtraction.*)
From Stdlib Require Import extraction.ExtrOcamlNativeString.
From Qoreo Require Import NetQasm.

Open Scope string_scope.
Open Scope example_scope.
Open Scope Q_scope.

Import Unitary.
Import ListNotations.

Module DistributedGrover.

  Definition local_cz
      (P : Actor.t)
      (control target : Var.t)
      : Qoreo (Var.t * Var.t) :=

    do (control, target) ←
      P [-- Unitary (CRZ (1#1))
            (Pair control target) -] ;;

    do control ←
      P [- Unitary (RZ (-1#2)) control -] ;;

    ret (control, target).


  (* Implementation taken directly from: https://www.nature.com/articles/s41586-024-08404-x.pdf
    Oracle: O_a = (X^{1-a_0} \otimes X^{1-a_1}) \, CZ \, (X^{1-a_0} \otimes X^{1-a_1})
  *)
  Definition remote_cz
      (Alice Bob : Actor.t)
      (qA qB : Var.t)
      : Qoreo (Var.t * Var.t) :=

    (* Generate EPR pair *)
    do (a, b) ← get_entangled_pair Alice Bob ;;

    (* Phi+ -> Psi+ *)
    do b ← Bob [- Unitary X b -] ;;

    do (qA, a) ← local_cz Alice qA a ;;
    do (qB, b) ← local_cz Bob qB b ;;

    (* Alice measures in X basis *)
    do a ← Alice [- Unitary H a -] ;;
    do mA ← Alice [- Meas a -] ;;

    (* Bob measures in Y basis *)
    do b ← Bob [- Unitary Sdag b -] ;;
    do b ← Bob [- Unitary H b -] ;;
    do mB ← Bob [- Meas b -] ;;

    (* Exchange classical bits *)
    do mA_bob ← send Alice mA Bob ;;
    do mB_alice ← send Bob mB Alice ;;

    (* Alice applies corrections *)
    do qA ← Alice [- Unitary SGATE qA -] ;;

    do qA ← Alice [-
      Expr.If mA (Unitary Z qA) qA
    -] ;;

    do qA ← Alice [-
      Expr.If mB_alice (Unitary Z qA) qA
    -] ;;

    (* Bob applies corrections *)
    do qB ← Bob [- Unitary Sdag qB -] ;;

    do qB ← Bob [-
      Expr.If mA_bob (Unitary Z qB) qB
    -] ;;

    do qB ← Bob [-
      Expr.If mB (Unitary Z qB) qB
    -] ;;

    ret (qA, qB).


  (*
    markA markB specify the marked state. 
    We assume we have a function that produces f(x) = 1 for the state specificed by markA markB
  *)
  Definition oracle
      (Alice Bob : Actor.t)
      (markA markB : bool)
      (qA qB : Var.t)
      : Qoreo (Var.t * Var.t) :=

    do qA ←
      (if markA
       then ret qA
       else Alice [- Unitary X qA -]) ;;

    do qB ←
      (if markB
       then ret qB
       else Bob [- Unitary X qB -]) ;;

    do (qA, qB) ← remote_cz Alice Bob qA qB ;;

    (*Alice and Bob apply their corrections *)
    do qA ←
      (if markA
       then ret qA
       else Alice [- Unitary X qA -]) ;;

    do qB ←
      (if markB
       then ret qB
       else Bob [- Unitary X qB -]) ;;

    ret (qA, qB).


  Definition grover
      (Alice Bob : Actor.t)
      (markA markB : bool)
      : Qoreo (Var.t * Var.t) :=

    (* Initialize |00> *)
    do qA ← Alice [- New (Bit false) -] ;;
    do qB ← Bob [- New (Bit false) -] ;;

    (* Uniform superposition *)
    do qA ← Alice [- Unitary H qA -] ;;
    do qB ← Bob [- Unitary H qB -] ;;

    (* Generic oracle *)
    do (qA, qB) ←
      oracle Alice Bob markA markB qA qB ;;

    (* Diffusion: H X CZ X H *)
    do qA ← Alice [- Unitary H qA -] ;;
    do qB ← Bob [- Unitary H qB -] ;;

    do qA ← Alice [- Unitary X qA -] ;;
    do qB ← Bob [- Unitary X qB -] ;;

    (* Second remote CZ *)
    do (qA, qB) ← remote_cz Alice Bob qA qB ;;

    do qA ← Alice [- Unitary X qA -] ;;
    do qB ← Bob [- Unitary X qB -] ;;

    do qA ← Alice [- Unitary H qA -] ;;
    do qB ← Bob [- Unitary H qB -] ;;

    (* Final measurements *)
    do resultA ← Alice [- Meas qA -] ;;
    do resultB ← Bob [- Meas qB -] ;;

    ret (resultA, resultB).


  (* Generic distributed grover's. boolean inputs to the function mimic saying: 
  we have an f(x) that outputs 1 and 0s elsewhere
  *)
 (* Definition choreo : Choreography.t :=
    mk (
      do result ←
        grover "alice" "bob" false false ;;
      ret result
    ).

   Definition parties : list Actor.t :=
    ["alice"; "bob"].

  Definition apps : option (list AppFile.t) :=
    Notation.render_Qoreo NetSquid parties
      (do (resultA, resultB) ←
         grover "alice" "bob" false false ;;
       ret [resultA; resultB]).
*)
Definition program : Qoreo (list Var.t) :=
  do (resultA, resultB) ←
    grover "alice" "bob" false false ;;
  ret [resultA; resultB].

Definition choreo : Choreography.t :=
  mk program.

Definition parties : list Actor.t :=
  ["alice"; "bob"].

Definition apps : option (list AppFile.t) :=
  Notation.render_Qoreo NetSquid parties program.
End DistributedGrover.

Definition example_apps := DistributedGrover.apps.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Extraction "DistributedGrover.ml" example_apps.
