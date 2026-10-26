(* Algorithmic type checking *) 

From Stdlib Require Export FSets.FMapList FSets.FSetList FSets.FMapFacts OrderedType OrderedTypeEx.
From QuantumLib Require Export Matrix Pad Quantum.
From Qoreo Require Export Expr.Expr.
From Qoreo Require Export Expr.Typecheck.
From Qoreo Require Export Choreography.Choreography.
Export Var.Map.Tactics.

Structure ltap := { Df : ChorEnv.t Expr.Typ.t; Tf : ChorEnv.t nat }.

(* checks equivalence of two ChorEnvs wrt a given set of actors. *)
Definition chorenv_eq_on {T}
  (cmp : T -> T -> bool) (As : Actor.FSet.t) (CE1 : ChorEnv.t T) (CE2 : ChorEnv.t T) : bool :=
  Actor.FSet.for_all (fun A => Var.Map.equal cmp (ChorEnv.find A CE1) (ChorEnv.find A CE2)) As.

(*
  Correctness (where u+ is disjoint union):
   Choreography.WellTyped G D (T u+ T') C <=>
      Typecheck.typecheck G (D u+ D') (T u+ T') C = Some {| Df := D', Tf := T' |}
 *)
Fixpoint typecheck (G D : ChorEnv.t Expr.Typ.t) (T : ChorEnv.t nat ) (C : Choreography.t) : option ltap :=
  match C with
  | Choreography.Empty => Some {| Df := D; Tf := T |}
  | Choreography.Do (Insn.EPR A x B y) C =>
      if Actor.eq_dec A B then None else
        match Var.Map.find x (ChorEnv.find A D), Var.Map.find y (ChorEnv.find B D) with
        | None, None =>
            match typecheck (ChorEnv.remove B y (ChorEnv.remove A x G))
                    (ChorEnv.add B y Expr.Typ.QUBIT (ChorEnv.add A x Expr.Typ.QUBIT D)) T C
            with
            | Some {| Df := D'; Tf := _ |} as sltap =>
                match Var.Map.find x (ChorEnv.find A D'), Var.Map.find y (ChorEnv.find B D') with
                | None, None => sltap
                | _, _ => None
                end
            | None => None
            end
        | _, _ => None
        end
  | Choreography.Do (Insn.Send A e B y) C =>
      if Actor.eq_dec A B then None else
      match Expr.Typecheck.typecheck (ChorEnv.find A G) (ChorEnv.find A D) (ChorEnv.find A T) e with
      | Some {| Expr.Typecheck.Df := Delta;
               Expr.Typecheck.Tf := Theta;
               Expr.Typecheck.tf := BANG t|} =>
          typecheck (ChorEnv.add B y t G) (Actor.Map.add A Delta D) (Actor.Map.add A Theta T) C
      | _ => None           
      end 
  | Choreography.Do (Insn.LetBang A x e) C =>
      match Expr.Typecheck.typecheck (ChorEnv.find A G) (ChorEnv.find A D) (ChorEnv.find A T) e with
      | Some {| Expr.Typecheck.Df := Delta;
               Expr.Typecheck.Tf := Theta;
               Expr.Typecheck.tf := BANG t|} =>
          typecheck (ChorEnv.add A x t G) (Actor.Map.add A Delta D) (Actor.Map.add A Theta T) C
      | _ => None           
      end 
  | Choreography.Do (Insn.Let A x e) C =>
      match Expr.Typecheck.typecheck (ChorEnv.find A G) (ChorEnv.find A D) (ChorEnv.find A T) e with
      | Some {| Expr.Typecheck.Df := Delta;
               Expr.Typecheck.Tf := Theta;
               Expr.Typecheck.tf := t|} =>
          match typecheck
                  (ChorEnv.remove A x G)
                  (Actor.Map.add A (Var.Map.add x t Delta) D)
                  (Actor.Map.add A Theta T) C with
          | Some ltap as sltap =>
              match Var.Map.find x (ChorEnv.find A ltap.(Df)) with
              | None => sltap
              | _ => None
              end
          | _ => None
          end
      | _ => None           
      end 
  | Choreography.Do (Insn.LetPair A x y e) C =>
        if Var.eq_dec x y then None else
        match Expr.Typecheck.typecheck (ChorEnv.find A G) (ChorEnv.find A D) (ChorEnv.find A T) e with
        | Some {| Expr.Typecheck.Df := Delta;
                 Expr.Typecheck.Tf := Theta;
                 Expr.Typecheck.tf := Expr.Typ.Tensor t1 t2|} =>
            match typecheck
                    (ChorEnv.remove A x (ChorEnv.remove A y G))
                    (Actor.Map.add A (Var.Map.add x t1 (Var.Map.add y t2 Delta)) D)
                    (Actor.Map.add A Theta T) C with
            | Some ltap as sltap =>
                let Delta := ChorEnv.find A ltap.(Df) in
                match Var.Map.find x Delta, Var.Map.find y Delta with
                | None, None => sltap
                | _, _ => None
                end
            | _ => None
            end
        | _ => None           
        end 
  | Choreography.If A e C1 C2 C =>
      match Expr.Typecheck.typecheck (ChorEnv.find A G) (ChorEnv.find A D) (ChorEnv.find A T) e with
      | Some {| Expr.Typecheck.Df := Delta;
               Expr.Typecheck.Tf := Theta;
               Expr.Typecheck.tf := Expr.Typ.BIT|} =>
          let D' := Actor.Map.add A Delta D in
          let T' := Actor.Map.add A Theta T in
          match typecheck G D' T' C1, typecheck G D' T' C2 with
          | Some {| Df := D1; Tf := T1 |}, Some {| Df := D2; Tf := T2 |} =>
              let As :=
                Actor.FSet.union
                  (Actor.FSet.union
                     (Actor.FSet.union (Actor.Map.domain D1) (Actor.Map.domain D2))
                     (Actor.FSet.union (Actor.Map.domain T1) (Actor.Map.domain T2)))
                  (Actor.FSet.union (Actor.Map.domain D') (Actor.Map.domain T')) in
              if (chorenv_eq_on Expr.Typ.typ_eq_dec As D1 D2) &&
                   (chorenv_eq_on Nat.eqb As T1 T2) then
                let Bs :=
                  Actor.FSet.diff As
                    (Actor.FSet.union (Choreography.actors C2) (Choreography.actors C1)) in
                if (chorenv_eq_on Expr.Typ.typ_eq_dec Bs D' ChorEnv.empty) &&
                     (chorenv_eq_on Nat.eqb Bs T' ChorEnv.empty) &&
                     (chorenv_eq_on Expr.Typ.typ_eq_dec Bs D1 D') &&
                     (chorenv_eq_on Nat.eqb Bs T1 T')
                then typecheck G D1 T1 C
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
