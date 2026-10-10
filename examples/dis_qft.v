From Stdlib Require Import String.
From Qoreo Require Import Base Expr Choreography.
From QoreoExamples Require Import Notation.
Import ExampleExtraction.
From Stdlib Require Import extraction.ExtrOcamlNativeString.
From Qoreo Require Import NetQasm.

Open Scope string_scope.
Open Scope example_scope.

Module DQFT.
  (* Distributed QFT example taken from: https://arxiv.org/pdf/2606.18494 *)
  
  (*Definition dqft (Alice Bob : Actor.t) : Qoreo (Var.t * (Var.t * Var.t)) := *)
  (*Definition dqft (Alice Bob : Actor.t) : Qoreo unit := *)
  Definition dqft (Alice Bob : Actor.t) (b0 b1 b2 : bool) : Qoreo unit :=
  (* I used 101 as the input here. TO DO: Automate this? *)
  do q0 ← Alice [- New (Bit b0) -] ;;
  do q1 ← Bob   [- New (Bit b1) -] ;;
  do q2 ← Bob   [- New (Bit b2) -] ;;

  do q0 ← Alice [- Unitary H q0 -] ;;

  (* This implementation only requires ONE EPR pair since we're using ancillas *)
  do (a0, a1) ← get_entangled_pair Alice Bob ;;
  (* Start Process*)
  do (q0, a0) ←
    Alice [-- Unitary CNOT (Pair q0 a0) -] ;;
  do m0 ← Alice [- Meas a0 -] ;;
  do m0_bob ← send Alice m0 Bob ;;
  do a1 ←
      Bob [- If m0_bob
                 (Unitary X a1)
                 a1 -] ;;
 
  do (a1, q1) ←
    Bob [-- Unitary CS (Pair a1 q1) -] ;;
 
  do (a1, q2) ←
    Bob [-- Unitary CT (Pair a1 q2) -] ;;
  (*H on a1*)
  do a1 ← Bob [- Unitary H a1 -] ;;
  (*Measure a1, send measurement result, apply correction*)
  do m1 ← Bob [- Meas a1 -] ;;
  do m1_alice ← send Bob m1 Alice ;;
  do q0 ←
      Alice [- If m1_alice
                 (Unitary Z q0)
                 q0 -] ;;
  (* H on q1 *)
  do q1 ← Bob [- Unitary H q1 -] ;;
  (*CS on q1, q2*)
  do (q1, q2) ←
    Bob [-- Unitary CS (Pair q1 q2) -] ;;
  (*H on q2*)
  do q2 ← Bob [- Unitary H q2 -] ;;

  do q0 ← Alice [- Meas q0 -] ;;
  do q1 ← Bob [- Meas q1 -] ;;
  do q2 ← Bob [- Meas q2 -] ;;
  do q3 ← Bob [- Pair q1 q2-];;
  ret tt.
  (*ret (q0, (q1, q2)). *)

  
 


  (* Not sure if correct, but I modified the b92 case to just run DQFT once *)
  Definition choreo : Choreography.t :=
  mk (
    do result ← dqft "alice" "bob" true false true ;;
    ret result
  ).


  Definition parties : list Actor.t :=
    ["alice"; "bob"].


  Definition apps : option (list AppFile.t) :=
    ExampleExtraction.render_parties choreo parties.
End DQFT.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Extraction "dqft_netqasm.ml" DQFT.apps.
