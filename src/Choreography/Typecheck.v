(* Algorithmic type checking *) 

From Stdlib Require Export FSets.FMapList FSets.FSetList FSets.FMapFacts OrderedType OrderedTypeEx.
From QuantumLib Require Export Matrix Pad Quantum.
From Qoreo Require Export Expr.Expr.
From Qoreo Require Export Expr.Typecheck.
From Qoreo Require Export Choreography.Choreography.
Export Var.Map.Tactics.

Structure ltap :=
    { Df : ChorEnv.t Expr.Typ.t;
      Tf : ChorEnv.t nat;
      tf : Typ.t
    }.

Module Env.


  Definition ceMerge {T} (env1 env2 : ChorEnv.t T) :
  option (ChorEnv.t T) :=
    if ChorEnv.disjoint env1 env2
    then Some (ChorEnv.concat env1 env2)
    else None.


  Definition addDf (A : Actor.t) (x : Var.t) (tp : Expr.Typ.t) (g : ltap) :=
    {|
      Df := ChorEnv.add A x tp (Df g);
      Tf := Tf g;
      tf := tf g
    |}.
  Definition addTf (A : Actor.t) (x : Var.t) (n : nat) (g : ltap) :=
    {|
      Tf := ChorEnv.add A x n (Tf g);
      Df := Df g;
      tf := tf g
    |}.


  (* checks equivalence of two ChorEnvs wrt a given set of actors. *)
  Definition chorenv_eq_on {T}
    (cmp : T -> T -> bool) (As : Actor.FSet.t) (CE1 : ChorEnv.t T) (CE2 : ChorEnv.t T) : bool :=
    Actor.FSet.for_all (fun A => Var.Map.equal cmp (ChorEnv.find A CE1) (ChorEnv.find A CE2)) As.
End Env.
Import Env.


Module Pattern.

  Fixpoint typecheck (p : Pattern.t) (tp : Typ.t)
            : option (ChorEnv.t Expr.Typ.t * ChorEnv.t Expr.Typ.t) :=
    match p, tp with
    | Pattern.Var A x,
      Typ.Local A' tp' =>
      if Actor.eq_dec A A'
      then Some (ChorEnv.empty, ChorEnv.add A x tp' ChorEnv.empty)
      else None
    | Pattern.Bang A x,
      Typ.Local A' (Expr.Typ.BANG tp') =>
      if Actor.eq_dec A A'
      then Some (ChorEnv.add A x tp' ChorEnv.empty, ChorEnv.empty)
      else None      

    | Pattern.VarPair A x1 x2,
      Typ.Local A' (Expr.Typ.Tensor tp1 tp2) =>
      if Actor.eq_dec A A'
      then if Var.eq_dec x1 x2
      then None
      else Some (ChorEnv.empty,
                  ChorEnv.add A x2 tp2
                  (ChorEnv.add A x1 tp1
                  ChorEnv.empty))
      else None
    | Pattern.Unit, Typ.Unit =>
      Some (ChorEnv.empty, ChorEnv.empty)
    | Pattern.Pair p1 p2, Typ.Tensor tp1 tp2 =>
      match typecheck p1 tp1, typecheck p2 tp2 with
      | Some (G1,D1), Some (G2,D2) =>
        match ceMerge G1 G2, ceMerge D1 D2 with
        | Some G', Some D' => Some (G',D')
        | _, _ => None
        end
      | _, _ => None
      end
    | _, _ => None
    end.

End Pattern.

(*
Structure ltap := { Df : ChorEnv.t Expr.Typ.t; Tf : ChorEnv.t nat; tf : Typ.t }.
*)


(*
  Correctness (where D u++ D' = D'' means for all A in dom(D) u dom(D'), D''(A) = D(A) u+ D'(A)
  where u+ is disjoint union):
   Choreography.WellTyped G D (T u++ T') C <=>
      Typecheck.typecheck G (D u++ D') (T u++ T') C = Some {| Df := D', Tf := T' |}
 *)
Fixpoint typecheck (G D : ChorEnv.t Expr.Typ.t) (T : ChorEnv.t nat ) (C : Choreography.t) : option ltap :=
  match C with
  | Choreography.LetIn p C1 C2 =>

    match typecheck G D T C1 with
    | Some {| Df := D'; Tf := T'; tf := tp |} =>
      match Pattern.typecheck p tp with
      | Some (G'', D'') =>
        match ceMerge D' D'' with
        | Some D''' =>
           if ChorEnv.disjoint G G''
           then
             match typecheck (ChorEnv.concat G G'') D''' T' C2 with
             | Some result =>
               if ChorEnv.disjoint D'' result.(Df)
               then Some result
               else None
             | None => None
             end
           else None
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end

  | Choreography.Loc A e => 
    match Expr.Typecheck.typecheck (ChorEnv.find A G) (ChorEnv.find A D) (ChorEnv.find A T) e with
      | Some {| Expr.Typecheck.Df := Delta;
               Expr.Typecheck.Tf := Theta;
               Expr.Typecheck.tf := t |} =>
        Some {| Df := Actor.Map.add A Delta D;
                Tf := Actor.Map.add A Theta T;
                tf := Typ.Local A t
            |}
      | None => None
    end
  | Choreography.Unit =>
    Some {| Df := D; Tf := T; tf := Typ.Unit |}
  | Choreography.Pair C1 C2 =>
    match typecheck G D T C1 with
    | None => None
    | Some {| Df := D'; Tf := T'; tf := t1 |} =>
      match typecheck G D' T' C2 with
      | Some {| Df := D''; Tf := T''; tf := t2 |} =>
        Some {| Df := D''; Tf := T''; tf := Typ.Tensor t1 t2 |}
      | None => None
      end
    end
  | Choreography.Send A e B =>
    match Expr.Typecheck.typecheck (ChorEnv.find A G) (ChorEnv.find A D) (ChorEnv.find A T) e with
      | Some {| Expr.Typecheck.Df := Delta;
               Expr.Typecheck.Tf := Theta;
               Expr.Typecheck.tf := Expr.Typ.BANG t
              |} =>
        Some {| Df := Actor.Map.add A Delta D;
                Tf := Actor.Map.add A Theta T;
                tf := Typ.Local B (Expr.Typ.BANG t)
            |}
      | _ => None
    end
  | Choreography.EPR A B => 
    Some {| Df := D; Tf := T;
            tf := Typ.Tensor (Typ.Local A Expr.Typ.QUBIT) (Typ.Local B Expr.Typ.QUBIT)|}
  | Choreography.If A e C1 C2 =>
    match Expr.Typecheck.typecheck (ChorEnv.find A G) (ChorEnv.find A D) (ChorEnv.find A T) e with
    | Some {| Expr.Typecheck.Df := Delta;
               Expr.Typecheck.Tf := Theta;
               Expr.Typecheck.tf := Expr.Typ.BIT |} =>
      let D' := Actor.Map.add A Delta D in
      let T' := Actor.Map.add A Theta T in
      match typecheck G D' T' C1, typecheck G D' T' C2 with
      | Some {| Df := D1; Tf := T1; tf := t1 |},
        Some {| Df := D2; Tf := T2; tf := t2 |} =>
        let As := Actor.FSet.union
                  (Actor.FSet.union
                     (Actor.FSet.union (Actor.Map.domain D1) (Actor.Map.domain D2))
                     (Actor.FSet.union (Actor.Map.domain T1) (Actor.Map.domain T2)))
                  (Actor.FSet.union (Actor.Map.domain D') (Actor.Map.domain T')) in
        if (chorenv_eq_on Expr.Typ.eqb As D1 D2) &&
                   (chorenv_eq_on Nat.eqb As T1 T2)
        then  let Bs := Actor.FSet.diff As
                    (Actor.FSet.union (Choreography.actors C2) (Choreography.actors C1)) in
              if (chorenv_eq_on Expr.Typ.eqb Bs D1 D') &&
                     (chorenv_eq_on Nat.eqb Bs T1 T')
              then if Typ.eqb t1 t2
                   then Some {| Df := D1; Tf := T1; tf := t1 |}
                   else None
              else None
        else None
      | _, _ => None
      end
    | _ => None
    end
  end.


Variant typecheck_result : Type := success | failure.

Definition essentially_empty {T} (CE : ChorEnv.t T) : bool :=
  Actor.FSet.for_all 
    (fun A => Var.Map.is_empty (ChorEnv.find A CE)) 
    (Actor.Map.domain CE).

Definition toplevel_typecheck (T : ChorEnv.t nat) (C : Choreography.t) : typecheck_result :=
  match typecheck ChorEnv.empty ChorEnv.empty T C with
  | None => failure
  | Some {| Df := D; Tf := _ |} => if essentially_empty D then success else failure
  end.
