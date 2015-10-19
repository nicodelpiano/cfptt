Section Ejercicio1.

(* 1.1 *)
Lemma predspec : forall n : nat,
  {m : nat | n = 0 /\ m = 0 \/ n = S m}.
Proof.
  intro.
  destruct n;
  [ exists 0; left; split
  | exists n; right
  ]; reflexivity.
Qed.

End Ejercicio1.

(* 1.2 *)
Extraction Language Haskell.
Extraction "predecesor" predspec.

Section Ejercicio3.

(* 3.1 *)
Definition Value := bool.

Inductive BoolExpr : Set :=
| bbool : bool -> BoolExpr
| or : BoolExpr -> BoolExpr -> BoolExpr
| bnot : BoolExpr -> BoolExpr.

Inductive BEval : BoolExpr -> Value -> Prop :=
| ebool : forall b : bool, BEval (bbool b) (b:Value)
| eorl : forall e1 e2 : BoolExpr, BEval e1 true -> BEval (or e1 e2) true
| eorr : forall e1 e2 : BoolExpr, BEval e2 true -> BEval (or e1 e2) true
| eorrl : forall e1 e2 : BoolExpr,
BEval e1 false -> BEval e2 false -> BEval (or e1 e2) false
| enott : forall e : BoolExpr, BEval e true -> BEval (bnot e) false
| enotf : forall e : BoolExpr, BEval e false -> BEval (bnot e) true.

Fixpoint beval (e : BoolExpr) : Value :=
  match e with
    | bbool b => b
    | or e1 e2 =>
    match beval e1, beval e2 with
      | false, false => false
      | _, _ => true
    end
    | bnot e1 => if beval e1 then false else true
  end.

Fixpoint sbeval (e : BoolExpr) : Value :=
  match e with
    | bbool b => b
    | or e1 e2 =>
    match sbeval e1 with
      | true => true
      | _ => sbeval e2
    end
    | bnot e1 => if sbeval e1 then false else true
  end.

End Ejercicio3.
