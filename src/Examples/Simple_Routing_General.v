From Stdlib Require Import String List.
From Qoreo Require Import Base.Config Expr.Expr Choreography.Choreography.
From Qoreo.Choreography Require Import Notation.
From Qoreo Require Import NetQasm.
From Stdlib Require Import extraction.ExtrOcamlNativeString.
Import Config.Unitary.
Import Expr.

Import ListNotations.

Open Scope string_scope.
Open Scope list_scope.
Open Scope example_scope.

Module Simple_Routing_General.
  (*Graph is a list of Paths, Paths is a list of Actors so Graph is a list of lists; To DO: Write this better?*)
  Definition Path : Type := list Actor.t.

  Definition Graph : Type := list Path.

  Definition BitString : Type := list bool.

  (*Takes in a nat m and returns a 2^m sized list containing all the binary patterns - AI wrote this encode_binary function*)
  Fixpoint encode_binary (m : nat) : list BitString :=
    match m with
    | O => [[]]
    | S width =>
        let suffixes := encode_binary width in
        List.map (cons false) suffixes ++ List.map (cons true) suffixes
    end.
  (*Takes in a list of BitStrings from encode_binary and returns the route_indexth element of it. *)
 Definition router (route_index : nat) (ids : list BitString)
    : Qoreo (option (list Expr.t)) :=
  match nth_error ids route_index with
  | Some id => ret (Some (List.map Expr.Bit id))
  | None => ret None
  end.
  (*This should give me an Expr.t*)

  (* Perform one entanglement-swapping operation *)

  Definition e_swap
      (Left Repeater Receiver : Actor.t)
      : Qoreo Choreography.t :=

    (* Generate two EPR pairs *)
    LET (a @ Left, r0 @ Repeater) ←
      get_entangled_pair Left Repeater ;;

    LET (r1 @ Repeater, target @ Receiver) ←
      get_entangled_pair Repeater Receiver ;;

    (* Bell measurement at the repeater *)

    LET@ (r0, r1) @ Repeater ←
      Repeater [- Unitary CNOT (Pair r0 r1) -] ;;

    LET r0 @ Repeater ←
      Repeater [- Unitary H r0 -] ;;

    LET! mz @ Repeater ←
      Repeater [- Meas r0 -] ;;

    LET! mx @ Repeater ←
      Repeater [- Meas r1 -] ;;

    (* Send classical measurement outcomes *)

    LET! mx_r @ Receiver ←
      send Repeater (Bang mx) Receiver ;;

    (* TO DO: Remove the buffer *)
    LET! buffer @ Receiver ←
      Receiver [- Bang (Bit true) -] ;;

    LET! ack @ Repeater ←
      send Receiver (Bang buffer) Repeater ;;

    LET! mz_r @ Receiver ←
      send Repeater (Bang mz) Receiver ;;

    (* Apply Pauli corrections *)

    LET target @ Receiver ←
      Receiver [-
        Expr.If mx_r (Unitary X target) target -] ;;

    LET target @ Receiver ←
      Receiver [-
        Expr.If mz_r (Unitary Z target) target-] ;;

    (* Return the EPR pair *)
    do left_q ← Left [- a -] ;;
    do right_q ← Receiver [- target -] ;;

    ret (Choreography.Pair left_q right_q).

  Definition e_swap_extend
      (Src Current Next : Actor.t)
      (src_q current_q : Var.t)
      : Qoreo Choreography.t :=

    (*Generate a new EPR pair
       between Current and Next.
       Current already owns current_q,
       which is entangled with Src.
    *)

    LET (r @ Current, out @ Next) ←
      get_entangled_pair Current Next ;;

    (* Bell measurement at Current *)

    LET@ (q, r) @ Current ←
      Current [-
        Unitary CNOT (Pair current_q r)-] ;;

    LET q @ Current ←
      Current [- Unitary H q -] ;;

    LET! mz @ Current ←
      Current [- Meas q -] ;;

    LET! mx @ Current ←
      Current [- Meas r -] ;;

    (* Send classical measurement bits to Next *)

    LET! mx_next @ Next ←
      send Current (Bang mx) Next ;;

    (* Remove when I add pairs *)
    LET! buffer @ Next ←
      Next [- Bang (Bit true) -] ;;

    LET! ack @ Current ←
      send Next (Bang buffer) Current ;;

    LET! mz_next @ Next ←
      send Current (Bang mz) Next ;;

    (*Apply corrections at Next *)

    LET out @ Next ←
      Next [-
        Expr.If mx_next (Unitary X out) out
      -] ;;

    LET out @ Next ←
      Next [-
        Expr.If mz_next (Unitary Z out) out
      -] ;;

    (* Return corrected qubit (If we had phi+ ad before, now this should give me phi+ ae or something) *)
    do left_q ← Src [- src_q -] ;;
    do right_q ← Next [- out -] ;;

    ret (Choreography.Pair left_q right_q).
  (*Recursively call e_swap_extend*)
  Fixpoint extend_swaps
      (Src Current : Actor.t)
      (src_q current_q : Var.t)
      (remaining : Path)
      {struct remaining} : Qoreo Choreography.t :=
    match remaining with
    | [] =>
        do left_q ← Src [- src_q -] ;;
        do right_q ← Current [- current_q -] ;;
        ret (Choreography.Pair left_q right_q)
    | Next :: rest =>
        LET (src_q' @ Src, next_q @ Next) ←
          e_swap_extend Src Current Next src_q current_q ;;
        extend_swaps Src Next src_q' next_q rest
    end.

  (* Take the encoded path and generate LET!s for each bit *)
  Fixpoint bind_route_bits
      (Router : Actor.t) (bits : list Expr.t)
      (k : list Var.t -> Qoreo Choreography.t)
      : Qoreo Choreography.t :=
    match bits with
    | [] => k []
    | bit :: rest =>
        LET! x @ Router ← Router [- Expr.Bang bit -] ;;
        bind_route_bits Router rest (fun xs => k (x :: xs))
    end.

   (*Helper to check if path id = Router's bitstring*)
   Fixpoint eq_route (bits : list Var.t) (id : BitString)
      {struct id} : Expr.t :=
    match bits, id with
    | _, [] =>
        Expr.Bit (Nat.eqb (List.length bits) 0)
    | x :: xs, b :: bs =>
        let rest_matches := eq_route xs bs in
        if b then
          Expr.If (Expr.Var x) rest_matches (Expr.Bit false)
        else
          Expr.If (Expr.Var x) (Expr.Bit false) rest_matches
    | _, _ => Expr.Bit false
    end.

  (* Every candidate path in G starts at G[0] and ends at G[-1], i.e. the end.
  Recursively constructs the Nested Choreographies that we used in Simple_Routing. *)
  Fixpoint match_path
      (Router Src Tgt : Actor.t)
      (bits : list Var.t)
      (paths : list (Path * BitString))
      {struct paths} : Qoreo Choreography.t :=
    match paths with
    | [] => get_entangled_pair Src Tgt
    | (p, id) :: rest =>
        cif Router (eq_route bits id)
          (match p with
           | Left :: Repeater :: Receiver :: remaining =>
               LET (a @ Left, target @ Receiver) ←
                 e_swap Left Repeater Receiver ;;
               extend_swaps Left Receiver a target remaining
           | [Left; Right] => get_entangled_pair Left Right
           | _ => get_entangled_pair Src Tgt
           end)
          (match_path Router Src Tgt bits rest)
    end.
  Definition create_route
      (m : nat)
      (G : Graph)
      (Src Tgt : Actor.t)
      (route_index : nat)
      : Qoreo Choreography.t :=
    if Nat.leb (List.length G) (Nat.pow 2 m) then
      let paths_with_ids := List.combine G (encode_binary m) in
      do selected ← router route_index (List.map snd paths_with_ids) ;;
      match selected with
      | Some bits =>
          bind_route_bits Src bits
            (fun vars => match_path Src Src Tgt vars paths_with_ids)
      | None => get_entangled_pair Src Tgt
      end
    else get_entangled_pair Src Tgt.

  Definition example_paths : Graph :=
    [["alice"; "bob";     "david"; "bob"]; (*tt;tf;ft;ff*)
     ["david"; "bob";     "frank"; "eve"];
     ["alice"; "charlie"; "david"; "bob"];
     ["david"; "charlie"; "frank"; "eve"]].

  Definition example_route : Qoreo Choreography.t :=
    create_route 2 example_paths "alice" "bob" 3.

  Definition choreo : Choreography.t := Notation.run example_route.

  Definition apps : option (list AppFile.t) :=
    Notation.render_Qoreo NetSquid example_route.

End Simple_Routing_General.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".

Definition example_apps := Simple_Routing_General.apps.

Extraction "Simple_Routing_General.ml" example_apps.
