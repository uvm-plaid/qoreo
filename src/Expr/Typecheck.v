(* Algorithmic type checking *) 

From Stdlib Require Export FSets.FMapList FSets.FSetList FSets.FMapFacts OrderedType OrderedTypeEx.
From QuantumLib Require Export Matrix Pad Quantum.
From Qoreo Require Export Expr.Expr.
Export Var.Map.Tactics.

Structure ltp := { Df : Var.Map.t Typ.t; Tf : Var.Map.t nat; tf : Expr.Typ.t }.

(*
  Invariants:
   - Var.Map.find x (Var.Map.remove x D) = None
   - Var.Map.find q (Var.Map.remove q T) = None
  Correctness (where u+ is disjoint union):
   Expr.WellTyped G D (T u+ T') e t <=>
      Typecheck.typecheck G (D u+ D') (T u+ T') e = Some {| Df := D', Tf := T', tf := t |}
 *)
Fixpoint typecheck (G D : Var.Map.t Typ.t) (T : Var.Map.t nat) (e : Expr.t) : option ltp :=
  match e with
  | Bit _ => Some {| Df := D; Tf := T; tf := BIT |}
  | QRef q =>
      match Var.Map.find q T with
      | None => None
      | Some _ => Some {| Df := D; Tf := Var.Map.remove q T; tf := QUBIT |}
      end
  | Var x =>
      match Var.Map.find x G with
      | None =>
          match Var.Map.find x D with
          | None => None
          | Some t => Some {| Df := Var.Map.remove x D; Tf := T; tf := t |}
          end
      | Some t => Some {| Df := D; Tf := T; tf := t |}
      end
  | Meas e1 =>
      match typecheck G D T e1 with
      | Some {| Df := D1; Tf := T1; tf := QUBIT |} => Some {| Df := D1; Tf := T1; tf := BIT |}
      | _ => None
      end
  | New e1 =>
      match typecheck G D T e1 with
      | Some {| Df := D1; Tf := T1; tf := BIT |} => Some {| Df := D1; Tf := T1; tf := QUBIT |}
      | _ => None
      end
  | Unitary U e1 =>
      match (typecheck G D T e1, Expr.Typ.type_of_unitary U) with
      | (Some {| Df := D1; Tf:= T1; tf := QUBIT |} as sltp1, QUBIT) => sltp1  
      | (Some {| Df := D1; Tf:= T1; tf := Tensor QUBIT QUBIT|} as sltp1,
            Tensor QUBIT QUBIT) => sltp1
      | _  => None
      end
  | Bang e =>
      match typecheck G D T e with
      | None => None
      | Some ltp => Some {| Df := ltp.(Df); Tf := ltp.(Tf); tf := BANG ltp.(tf) |}
      end
  | LetIn x e1 e2 =>
      match Var.Map.find x G with
      | Some _ => None
      | None =>
          match typecheck G D T e1 with
          | None => None
          | Some ltp1 =>
              match Var.Map.find x ltp1.(Df) with
              | Some _ => None
              | None =>
                  match typecheck G (Var.Map.add x ltp1.(tf) ltp1.(Df)) ltp1.(Tf) e2 with
                  | None => None
                  | Some ltp2 =>
                      match Var.Map.find x ltp2.(Df) with
                      | Some _ => None
                      | None => Some ltp2
                      end
                  end
              end
          end
      end
  | LetBang x e1 e2 =>
      match typecheck G D T e1 with
      | None => None
      | Some ltp1 =>
          match Var.Map.find x ltp1.(Df) with
          | Some _ => None
          | None => typecheck (Var.Map.add x ltp1.(tf) G) ltp1.(Df) ltp1.(Tf) e2 
          end
      end
  | If e1 e2 e3 =>
      match typecheck G D T e1 with
      | Some {| Df := D1; Tf := T1; tf := BIT |} =>
          match (typecheck G D1 T1 e2,
                  typecheck G D1 T1 e3) with
          | (None,_) | (_, None) => None
          | (Some ltp2, Some ltp3) =>
              if
                Var.Map.domain_eqb ltp2.(Df) ltp3.(Df) &&
                  Var.Map.domain_eqb ltp2.(Tf) ltp3.(Tf) &&
                  typ_eq_dec ltp2.(tf) ltp3.(tf)                                              
              then Some ltp2 else None
          end
      | _ => None
      end
  | Pair e1 e2 =>
      match typecheck G D T e1 with
      | None => None
      | Some ltp1 =>
          match typecheck G ltp1.(Df) ltp1.(Tf) e2 with
          | None => None
          | Some ltp2 => Some {| Df := ltp2.(Df); Tf := ltp2.(Tf); tf := Tensor ltp1.(tf) ltp2.(tf) |}
          end
      end
  | LetPair x y e1 e2 =>
      match (Var.Map.find x G, Var.Map.find y G)  with
      | (None, None) =>
          match typecheck G D T e1 with
          | Some {| Df := D1; Tf := T1; tf := Tensor t1 t2 |} =>
              match typecheck G (Var.Map.add x t1 (Var.Map.add y t2 D1)) T1 e2 with
              | Some ltp2 =>   
                  match (Var.Map.find x ltp2.(Df), Var.Map.find y ltp2.(Df))  with
                  | (None, None) => Some ltp2
                  | _ => None
                  end
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  | App e1 e2 =>
      match typecheck G D T e1 with
      | Some {| Df := D1; Tf := T1; tf := Lolli t1 t2 |} =>
          match typecheck G D1 T1 e2 with
          | Some {| Df := D2; Tf := T2; tf := t1' |} => 
              if (typ_eq_dec t1 t1') then Some {| Df := D2; Tf := T2; tf := t2 |}
              else None
          | None => None
          end
      | _ => None
      end
  | Lambda x t e =>
      match Var.Map.find x G, Var.Map.find x D with
      | None, None =>
          match typecheck G (Var.Map.add x t D) T e with
          | None => None
          | Some ltp =>
              match Var.Map.find x ltp.(Df) with
              | Some _ => None
              | None => Some ltp
              end
          end
      | _, _ => None
      end
  | Fix f x t1 t2 e =>
      match Var.Map.find x G, Var.Map.find x D with
      | None, None =>
          let G' := Var.Map.add x t1 G in
          match Var.Map.find f G', Var.Map.find f D with
          | None, None =>
              match typecheck (Var.Map.add f (Lolli (BANG t1) t2) G') D T e with
              | None => None
              | Some ltp =>
                  if
                    Var.Map.domain_eqb ltp.(Df) D &&
                      Var.Map.domain_eqb ltp.(Tf) T &&
                      typ_eq_dec ltp.(tf) t2                                              
                  then Some ltp else None
              end
          | _, _ => None
          end
      | _, _ => None
      end
  end.

Variant typecheck_result : Type := success (t : Typ.t) | failure.

Definition toplevel_typecheck (e : Expr.t) : typecheck_result :=
  match typecheck (Var.Map.empty Typ.t) (Var.Map.empty Typ.t) (Var.Map.empty nat) e with
  | None => failure
  | Some {| Df := D; Tf := T; tf := t |} =>
      if Var.Map.domain_eqb D (Var.Map.empty Typ.t) &&
           Var.Map.domain_eqb T (Var.Map.empty nat)
      then success t else failure
  end.
