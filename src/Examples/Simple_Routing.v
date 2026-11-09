
From Stdlib Require Import String.
From Qoreo Require Import Base.Config Expr.Expr Choreography.Choreography.
Import Config.Unitary.
Import Expr.

From Qoreo.Choreography Require Import Notation.

From Stdlib Require Import extraction.ExtrOcamlNativeString.
From Qoreo Require Import NetQasm.

Import List.ListNotations.
Open Scope list_scope.
Open Scope string_scope.
Open Scope example_scope.


Module Simple_Routing.
(* Adds the conditional branches to the choreography. This is the same structural modifications we had to make for ConditionalTest.v, 
i.e our function needs to be converted to type Choreography.t. 
We use s,s1,s2 so that the variable names do not conflict with each other. 
Note: This implementation was written in the old notation and will likely change. *)
Definition add_if
    (A : Actor.t)
    (condition : Expr.t)
    (C1 C2 : Qoreo unit)
    : Qoreo unit :=
  fun s =>

    let '(s1, _) :=
      C1 {|
        vars := vars s;
        chor := Choreography.Empty
      |} in

    let '(s2, _) :=
      C2 {|
        vars := vars s1;
        chor := Choreography.Empty
      |} in

    ({| (*If has the form If : Actor.t -> Expr.t -> t -> t -> t -> t *)
      vars := vars s2;
      chor :=
        Choreography.seq (chor s)
          (Choreography.If A condition
            (chor s1)
            (chor s2)
            Choreography.Empty)
    |}, tt).


  (* Teleport Alice's input qubit q to Destination through
     two repeaters: First and David.

     Route:
       Alice -> First -> David -> Destination

     We need an EPR pair between every pair of Actors on the route:
       (Alice, First)
       (First, David)
       (David, Destination)

     First performs entanglement swapping to establish
     an Alice-David Bell pair.

     David then performs entanglement swapping to establish
     an Alice-Destination Bell pair.

     Alice finally teleports q to Destination.

     The output is measured in the X basis to verify the
     test input ket + so we can expect to receive 1 everytime.
  *)
  Definition teleport_via
      (Alice First David Destination : Actor.t)
      (q : Var.t)
      : Qoreo unit :=

    (* Step 1: Generate three EPR pairs. *)
    do (a, r0) ←
      get_entangled_pair Alice First ;;

    do (r1, d0) ←
      get_entangled_pair First David ;;

    do (d1, out) ←
      get_entangled_pair David Destination ;;

    (* Step 2: 'First' repeater performs entanglement swapping.

       First owns r0 and r1.
       This establishes entanglement between Alice and David,
       up to measurement-dependent Pauli corrections.
    *)
    do (r0, r1) ←
      First [-- Unitary CNOT (Pair r0 r1) -] ;;

    do r0 ←
      First [- Unitary H r0 -] ;;

    do mz1 ←
      First [- Meas r0 -] ;;

    do mx1 ←
      First [- Meas r1 -] ;;

    (* Classically send corrections to David.*)
    
    do mx1_d ←
      send First mx1 David ;;
    do buffer ←
      David [- Bit true -] ;;

    do _ ←
      send David buffer First ;;

    do mz1_d ←
      send First mz1 David ;;


    (* David applies corrections. *)
    do d0 ← David [-
      Expr.If mx1_d (Unitary X d0) d0 -] ;;

    do d0 ← David [-
      Expr.If mz1_d (Unitary Z d0) d0 -] ;;


    (* Step 3: Do the same as above with David owning d0 and d1.
       After swapping, Alice and Destination share a Bell pair,
       up to measurement-dependent Pauli corrections.
    *)
    do (d0, d1) ←
      David [-- Unitary CNOT (Pair d0 d1) -] ;;

    do d0 ←
      David [- Unitary H d0 -] ;;

    do mz2 ←
      David [- Meas d0 -] ;;

    do mx2 ←
      David [- Meas d1 -] ;;


    (* Send the second swapping outcomes to Destination. *)
    do mx2_dest ←
      send David mx2 Destination ;;

    do buffer2 ←
      Destination [- Bit true -] ;;

    do _ ←
      send Destination buffer2 David ;;

    do mz2_dest ←
      send David mz2 Destination ;;


    (* 'Destination' applies corrections. *)
    do out ← Destination [-
      Expr.If mx2_dest (Unitary X out) out -] ;;

    do out ← Destination [-
      Expr.If mz2_dest (Unitary Z out) out -] ;;


    (* Step 4: Alice teleports her input qubit q along the route we've established. *)
    do (q, a) ←
      Alice [-- Unitary CNOT (Pair q a) -] ;;

    do q ←
      Alice [- Unitary H q -] ;;

    do tz ←
      Alice [- Meas q -] ;;

    do tx ←
      Alice [- Meas a -] ;;


    (* Send teleportation measurement outcomes to Destination. *)
    do tx_dest ←
      send Alice tx Destination ;;

    do buffer3 ←
      Destination [- Bit true -] ;;

    do _ ←
      send Destination buffer3 Alice ;;

    do tz_dest ←
      send Alice tz Destination ;;


    (* Step 5: 'Destination' applies the teleportation corrections,
       recovering the state owned by Alice.
    *)
    do out ← Destination [-
      Expr.If tx_dest (Unitary X out) out -] ;;

    do out ← Destination [-
      Expr.If tz_dest (Unitary Z out) out -] ;;


    (* Step 6: We measure here to test correctness. 
    Since we are teleporting +, we measure in the + - basis and expect to receive 1 at Destination. 
    This can be changed according to the qubit you want to send/ can be commented out.
    *)
    do out ←
      Destination [- Unitary H out -] ;;

    do result ←
      Destination [- Meas out -] ;;

    do _ ←
      send Destination result Alice ;;

    ret tt.


  (* Nested conditional routing.

     Flag 1 determines the first repeater:
       true  = Bob
       false = Charlie

     Flag 2 determines the final destination:
       true  = Eve
       false = Frank

     Paths:
       true,  true  = Alice Bob     David Eve
       true,  false = Alice Bob     David Frank
       false, true  = Alice Charlie David Eve
       false, false = Alice Charlie David Frank
  *)
  Definition simple_routing
      (Alice Bob Charlie David Eve Frank : Actor.t)
      (flag1 flag2 : bool)
      : Qoreo (list Var.t) :=

    (* Prepare Alice's input qubit.
       Here we use ket + but q can be anything.      
    *)
    do q ←
      Alice [- Unitary H (New (Bit false)) -] ;;

    (* Two Boolean routing decisions. *)
    do f1 ←
      Alice [- Bit flag1 -] ;;

    do f2 ←
      Alice [- Bit flag2 -] ;;


    (* First conditional:
       Choose Bob or Charlie as the first repeater.
    *)
    do _ ← add_if Alice (Var f1)

      (* f1 = true: use Bob.

         Nested conditional chooses Eve or Frank.
      *)
      (add_if Alice (Var f2)

        (* Path 0: true, true
           Alice -> Bob -> David -> Eve
        *)
        (teleport_via Alice Bob David Eve q)

        (* Path 1: true, false
           Alice -> Bob -> David -> Frank
        *)
        (teleport_via Alice Bob David Frank q)
      )

      (* f1 = false: use Charlie.

         Nested conditional chooses Eve or Frank.
      *)
      (add_if Alice (Var f2)

        (* Path 2: false, true
           Alice -> Charlie -> David -> Eve
        *)
        (teleport_via Alice Charlie David Eve q)

        (* Path 3: false, false
           Alice -> Charlie -> David -> Frank
        *)
        (teleport_via Alice Charlie David Frank q)
      ) ;;

    ret [].


  (* All six actors must be present for endpoint generation. *)
  Definition parties : list Actor.t :=
    ["alice"; "bob"; "charlie"; "david"; "eve"; "frank"].


  (* Change these two Booleans to select a path. *)
  Definition route_flag_1 : bool := true.
  Definition route_flag_2 : bool := true.


  Definition choreo : Choreography.t :=
    mk (
      do result ←
        simple_routing
          "alice" "bob" "charlie" "david" "eve" "frank"
          route_flag_1 route_flag_2 ;;
      ret result
    ).


  Definition apps : option (list AppFile.t) :=
    Notation.render_Qoreo NetSquid parties
      (simple_routing
        "alice" "bob" "charlie" "david" "eve" "frank"
        route_flag_1 route_flag_2).

End Simple_Routing.


Extraction Language OCaml.
Set Extraction Output Directory "extracted".

Definition example_apps := Simple_Routing.apps.

Extraction "Simple_Routing.ml" example_apps.
