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
Qed.

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

(* 3.3 *)
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extraction "BEval" bevalC sbevalC.

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

(* exists reverse l *)
(* perm_trans *)

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

Inductive Le : nat -> nat -> Prop :=
  LeZero : forall m : nat, Le 0 m
  | LeS : forall n m : nat, Le n m -> Le (S n) (S m).

Inductive Le' : nat -> nat -> Prop :=
  LeZero' : forall n : nat, Le' n n
  | LeS' : forall n m : nat, Le' n m -> Le' n (S m).

Inductive Gt : nat -> nat -> Prop :=
  GtZero : forall m : nat, Gt (S m) 0
  | GtS : forall n m : nat, Gt n m -> Gt (S n) (S m).

Inductive Gt' : nat -> nat -> Prop :=
  GtZero' : forall n : nat, Gt' n n
  | GtS' : forall n m, Gt' n m -> Gt' (S n) m.

Function leBool (n m : nat) {struct n} : bool :=
  match n, m with
    0, _ => true
    | S k, 0 => false
    | S k1, S k2 => leBool k1 k2
  end.

(**
Function leBool : nat -> nat -> bool :=
  fun x y =>
    match Le x y with
      | True => true
      | _ => false
    end.
**)

Lemma Le_Gt_dec: forall n m:nat, {(Le n m)}+{(Gt n m)}.
Proof.
  intros.
  functional induction (leBool n m).
    left.
    apply LeZero.

    right.
    apply GtZero.

    elim IHb; intro.
      left.
      apply LeS.
      assumption.

      right.
      apply GtS.
      assumption.
Qed.

Require Import Omega.

Lemma le_gt_dec: forall n m:nat, {(le n m)}+{(gt n m)}.
Proof.
  intros.
  functional induction (leBool n m).
    left.
    omega.

    right.
    omega.

    destruct IHb.
      left.
      omega.

      right.
      omega.
Qed.

End Ejercicio5.

Section Ejercicio6.

Require Import Omega.
Require Import DecBool.
Require Import Compare_dec.
Require Import Plus.
Require Import Mult.
Require Import NPeano.

Definition spec_res_nat_div_mod (a b:nat) (qr:nat*nat) :=
  match qr with
    (q,r) => (a = b*q + r) /\ r < b
  end.

Definition ltb n m := leb (S n) m.
(**
Lemma aux6 : forall n m : nat,
  n <= m - 1 -> n < m.
Proof.
  intros.
  induction n.
    
Qed.
**)

Lemma nat_div_mod :
  forall a b:nat, not(b=0)
    -> {qr:nat*nat | spec_res_nat_div_mod a b qr}.
Proof.
  intros.
 (*  unfold spec_res_nat_div_mod. *)
  induction a.
    exists (0, 0).
    split.
      rewrite mult_0_r.
      rewrite plus_0_r.
      reflexivity.

      elim (zerop b); [ contradiction | trivial ].

    case_eq b; intros.
      contradiction.

      destruct IHa.
      destruct x.
      simpl in s.
      destruct s.
      rewrite H1.
      case_eq (ltb n1 n); intro.
        exists (n0, S n1).
        simpl.
        split.
          rewrite H0.
          simpl.
          trivial.

          unfold ltb in H3.
          apply leb_complete in H3.
          apply le_lt_n_Sm.
          trivial.

        exists (S n0, 0).
        simpl.
        split.
          rewrite H0.
          simpl.
          unfold ltb in H3.
          apply leb_iff_conv in H3.
          rewrite H0 in H2.
          apply lt_le_S in H2.
          apply lt_le_S in H3.
          apply le_S_n in H2.
          apply le_S_n in H3.
          assert (n = n1) by (apply (le_antisym n n1); trivial).
          rewrite H4.
          rewrite mult_succ_r.
          rewrite plus_0_r.
          rewrite plus_assoc.
          trivial.

          apply lt_0_Sn.
Qed.

End Ejercicio6.

Extraction "nat_div_mod" nat_div_mod.

Section Ejercicio7.

Inductive tree (A:Set) : Set :=
  | leaf : tree A
  | node : A -> tree A -> tree A -> tree A.

Inductive tree_sub (A:Set) (t:tree A) : tree A -> Prop :=
  | tree_sub1 : forall (t':tree A) (x:A),
    tree_sub A t (node A x t t')
  | tree_sub2 : forall (t':tree A) (x:A),
    tree_sub A t (node A x t' t).

Theorem well_founded_tree_sub : forall A:Set,
  well_founded (tree_sub A).
Proof.
  unfold well_founded.
  intros.
  induction a;
  constructor;
  intros;
  inversion H;
  trivial.
Qed.

End Ejercicio7.

