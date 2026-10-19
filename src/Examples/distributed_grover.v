
From Stdlib Require Import String List QArith.
From Qoreo.Base Require Import Config Var Actor.
From Qoreo.Expr Require Import Expr.
From Qoreo.Choreography Require Import Choreography.
From Qoreo.Network Require Import Network.
From Qoreo.Choreography Require Import Notation.
From Stdlib Require Import extraction.ExtrOcamlNativeString.
From Qoreo Require Import NetQasm.

Open Scope string_scope.
Open Scope example_scope.
Open Scope Q_scope.
Import Unitary.
Import ListNotations.

Module DistributedGrover.

   (* Based on the simple implementation defined by this paper:
    https://www.nature.com/articles/s41586-024-08404-
    No. of EPR pairs used here: 2
    For now, 11 is hard-coded as the marked state. TO DO: Randomize this and test *)
  Definition local_cz
      (P : Actor.t) (control target : Var.t)
      : Qoreo (Var.t * Var.t) :=

    do (control, target) ←
      P [-- Unitary (CRZ (1#1))
            (Pair control target) -] ;;

    do control ←
      P [- Unitary (RZ (-1#2)) control -] ;;

    ret (control, target).

  (* This follows from the way remote gates were implemented in the dqft example. The function was created to increase readability
  *)
  Definition remote_cz
      (Alice Bob : Actor.t)
      (qA qB : Var.t)
      : Qoreo (Var.t * Var.t) :=

    (* Generate one EPR pair *)
    do (a, b) ← get_entangled_pair Alice Bob ;;

    (* Convert Phi+ to Psi+ *)
    do b ← Bob [- Unitary X b -] ;;

    (* Local CZ between each data qubit and ancilla *)
    do (qA, a) ← local_cz Alice qA a ;;
    do (qB, b) ← local_cz Bob qB b ;;

    (* Alice: X-basis measurement *)
    do a ← Alice [- Unitary H a -] ;;
    do mA ← Alice [- Meas a -] ;;

    (* Bob: Y-basis measurement *)
    do b ← Bob [- Unitary Sdag b -] ;;
    do b ← Bob [- Unitary H b -] ;;
    do mB ← Bob [- Meas b -] ;;

    (* Exchange measurement outcomes *)
    do mA_bob ← send Alice mA Bob ;;
    do mB_alice ← send Bob mB Alice ;;

    (* Alice applies corrections *)
    do qA ← Alice [- Unitary SGATE qA -] ;;

    do qA ← Alice [- Expr.If mA
                        (Unitary Z qA)
                        qA -] ;;

    do qA ← Alice [- Expr.If mB_alice
                        (Unitary Z qA)
                        qA -] ;;

    (* Bob applies corrections *)
    do qB ← Bob [- Unitary Sdag qB -] ;;

    do qB ← Bob [- Expr.If mA_bob
                      (Unitary Z qB)
                      qB -] ;;

    do qB ← Bob [- Expr.If mB
                      (Unitary Z qB)
                      qB -] ;;

    ret (qA, qB).

  
  Definition grover
      (Alice Bob : Actor.t)
      : Qoreo (list Var.t) :=

    
    do qA ← Alice [- New (Bit false) -] ;;
    do qB ← Bob [- New (Bit false) -] ;;

    
    do qA ← Alice [- Unitary H qA -] ;;
    do qB ← Bob [- Unitary H qB -] ;;

    do (qA, qB) ← remote_cz Alice Bob qA qB ;;

    (* Diffusion operator *)
    do qA ← Alice [- Unitary H qA -] ;;
    do qB ← Bob [- Unitary H qB -] ;;

    do qA ← Alice [- Unitary X qA -] ;;
    do qB ← Bob [- Unitary X qB -] ;;

    do (qA, qB) ← remote_cz Alice Bob qA qB ;;

    do qA ← Alice [- Unitary X qA -] ;;
    do qB ← Bob [- Unitary X qB -] ;;

    do qA ← Alice [- Unitary H qA -] ;;
    do qB ← Bob [- Unitary H qB -] ;;

    do resultA ← Alice [- Meas qA -] ;;
    do resultB ← Bob [- Meas qB -] ;;

    ret [resultA; resultB].

  Definition choreo : Choreography.t :=
    mk (
      do result ← grover "alice" "bob" ;;
      ret result
    ).

  Definition parties : list Actor.t :=
    ["alice"; "bob"].

  Definition apps : option (list AppFile.t) :=
    render_Qoreo NetSquid parties (grover "alice" "bob").

End DistributedGrover.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Extraction "distributed_grover_netqasm.ml"
  DistributedGrover.apps.
