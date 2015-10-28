Extraction Language Haskell.

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
Extraction "predecesor" predspec.

Section Ejercicio2.

Inductive bintree (X:Set) :=
  Empty : bintree X
  | Branch : X -> bintree X -> bintree X -> bintree X.

Inductive mirror (X:Set) : bintree X -> bintree X -> Prop :=
  mirror_empty : mirror X (Empty X) (Empty X)
  | mirror_branch : forall (t11 t12 t21 t22 : bintree X) (x1 x2 : X),
    mirror X t11 t22 -> mirror X t12 t21 ->
      x1 = x2 -> mirror X (Branch X x1 t11 t12) (Branch X x2 t21 t22).

(* 2.1 *)
Lemma MirrorC: forall (A:Set) (t:bintree A),
{t':bintree A|(mirror A t t')}.
Proof.
  intros.
  induction t.
    exists (Empty A).
    constructor.

    destruct IHt1.
    destruct IHt2.
    exists (Branch A x x1 x0).
    constructor; trivial.
Qed.

(* 2.2 *)
Function inverse (X : Set) (b : bintree X) {struct b} : bintree X :=
  match b with
    Empty => Empty X
    | (Branch e l r) => Branch X e (inverse X r) (inverse X l)
  end.

Hint Constructors mirror.

Lemma MirrorC2: forall (A:Set) (t:bintree A),
{ t' : bintree A | (mirror A t t')}.
Proof.
  intros.
  exists (inverse A t).
  functional induction (inverse A t);
    constructor; trivial.
  (*intros.
  functional induction (inverse A t);
  [ exists (Empty A)
  | destruct IHb; destruct IHb0;
    exists (Branch A e x x0);
    constructor
  ]; trivial.*)
Qed.

(*
Lemma MirrorC2': forall (A:Set) (t:bintree A),
{ t' : bintree A | (mirror A t t') /\ t' = inverse A t}.
Proof.
  intros.
  induction t.
    simpl.
    exists (Empty A).
    split; trivial.

    simpl.
    destruct IHt1.
    destruct IHt2.
    exists (Branch A x (inverse A t2) (inverse A t1)).
    split;
    [ destruct a;
      destruct a0;
      constructor;
      [ rewrite H0 in H
      | rewrite H2 in H1
      | ]
    | ]; trivial.
Qed.
*)

End Ejercicio2.

(* 2.3 *)
Extraction "mirror_function" MirrorC2.

Section Ejercicio3.

(* 3.1 *)
Definition Value := bool.

Inductive BoolExpr : Set :=
  | bbool : bool -> BoolExpr
  | or : BoolExpr -> BoolExpr -> BoolExpr
  | bnot : BoolExpr -> BoolExpr.

Inductive BEval : BoolExpr -> Value -> Prop :=
  | ebool : forall b : bool, BEval (bbool b) (b:Value)
  | eorl : forall e1 e2 : BoolExpr,
    BEval e1 true -> BEval (or e1 e2) true
  | eorr : forall e1 e2 : BoolExpr,
    BEval e2 true -> BEval (or e1 e2) true
  | eorrl : forall e1 e2 : BoolExpr,
    BEval e1 false -> BEval e2 false -> BEval (or e1 e2) false
  | enott : forall e : BoolExpr, BEval e true -> BEval (bnot e) false
  | enotf : forall e : BoolExpr, BEval e false -> BEval (bnot e) true.

Function beval (e : BoolExpr) : Value :=
  match e with
    | bbool b => b
    | or e1 e2 =>
    match beval e1, beval e2 with
      | false, false => false
      | _, _ => true
    end
    | bnot e1 => if beval e1 then false else true
  end.

Function sbeval (e : BoolExpr) : Value :=
  match e with
    | bbool b => b
    | or e1 e2 =>
    match sbeval e1 with
      | true => true
      | _ => sbeval e2
    end
    | bnot e1 => if sbeval e1 then false else true
  end.

(**
Lemma sbevalC : forall (e : BoolExpr) (b : Value),
  { b:Value | (BEval e b) }.
Proof.
  intros.
  exists (sbeval e).
  functional induction (sbeval e).
    
  exists b.
  constructor.
  exists true.
  constructor.
  
Qed.
**)

Lemma bevalC : forall e:BoolExpr,
  { b:Value | (BEval e b) }.
Proof.
  intro.
  exists (beval e).
  induction e; simpl.
    constructor.

    case_eq (beval e1); intro.
      constructor.
      rewrite <- H.
      assumption.

      case_eq (beval e2); intro.
      apply eorr.
      rewrite <- H0.
      assumption.

      constructor.
      rewrite <- H.
      assumption.

      rewrite <- H0.
      assumption.

  case_eq (beval e); intro.
    constructor.
    rewrite <- H.
    assumption.

    constructor.
    rewrite <- H.
    assumption.
Qed.

Lemma sbevalC : forall e:BoolExpr,
  { b:Value | (BEval e b) }.
Proof.
  intro.
  exists (sbeval e).
  induction e; simpl.
    constructor.

    case_eq (sbeval e1); intro.
      constructor.
      rewrite <- H.
      assumption.

      case_eq (sbeval e2); intro.
        apply eorr.
        rewrite <- H0.
        assumption.

      constructor.
      rewrite <- H.
      assumption.
      
      rewrite <- H0.
      assumption.

  case_eq (sbeval e); intro.
    constructor.
    rewrite <- H.
    assumption.

    constructor.
    rewrite <- H.
    assumption.
Qed.

(* 3.2 *)
Hint Constructors BEval.

Lemma bevalC2 : forall e:BoolExpr,
  { b:Value | (BEval e b) }.
Proof.
  intro.
  exists (beval e).
  induction e.
    constructor.

    simpl.
    case_eq (beval e1); intro.
      constructor.
      rewrite <- H.
      trivial.

      case_eq (beval e2); intro.
        apply eorr.
        rewrite <- H0.
        trivial.

      constructor.
        rewrite <- H.
        assumption.

        rewrite <- H0.
        assumption.

    simpl.
    case_eq (beval e); intro.
      constructor.
      rewrite <- H.
      assumption.

      constructor.
      rewrite <- H.
      assumption.
Qed.

Lemma sbevalC2 : forall e:BoolExpr,
  { b:Value | (BEval e b) }.
Proof.
  intro.
  exists (sbeval e).
  induction e.
    constructor.

    simpl.
    case_eq (sbeval e1); intro.
      constructor.
      rewrite <- H.
      trivial.

      case_eq (sbeval e2); intro.
        apply eorr.
        rewrite <- H0.
        trivial.

      constructor.
        rewrite <- H.
        assumption.

        rewrite <- H0.
        assumption.

    simpl.
    case_eq (sbeval e); intro.
      constructor.
      rewrite <- H.
      assumption.

      constructor.
      rewrite <- H.
      assumption.
Qed.

End Ejercicio3.

Section Ejercicio4.

Variable A:Set.

Inductive list : Set :=
  | nil : list
  | cons : A -> list -> list.

Fixpoint append (l1 l2 : list) {struct l1} : list :=
  match l1 with
    | nil => l2
    | cons a l => cons a (append l l2)
  end.

Inductive perm : list -> list ->Prop:=
  | perm_refl: forall l, perm l l
  | perm_cons: forall a l0 l1, perm l0 l1-> perm (cons a l0)(cons a l1)
  | perm_app: forall a l, perm (cons a l) (append l (cons a nil))
  | perm_trans: forall l1 l2 l3, perm l1 l2 -> perm l2 l3 -> perm l1 l3.

Hint Constructors perm.

(* 4.1 *)
Function reverse (l : list) {struct l} : list :=
  match l with
    | nil => nil
    | cons x xs => append (reverse xs) (cons x nil)
  end.

(* 4.2 *)
Lemma Ej6_4: forall l: list, { l2: list | perm l l2 }.
Proof.
  intro.
  functional induction (reverse l);
  [ exists nil
  | destruct IHl0;
    exists (append (cons x nil) x0);
    constructor
  ]; trivial.
Qed.

Lemma Ej6_4': forall l: list, {l2: list | perm l l2}.
Proof.
  induction l.
    exists nil.
    constructor.

    destruct IHl.
    exists (cons a x).
    constructor.
    trivial.
Qed.

End Ejercicio4.

Section Ejercicio5.

Definition Le : nat -> nat -> Prop :=
  fun x y =>
    x <= y.

Definition Gt : nat -> nat -> Prop :=
  fun x y =>
    x > y.

Lemma Le_Gt_dec: forall n m:nat, {(Le n m)}+{(Gt n m)}.
Proof.
  intros.
Qed.


End Ejercicio5.