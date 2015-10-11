Section Ejercicio1.

Inductive list (A : Set) : Set :=
  | nil : list A
  | cons : A -> list A -> list A.

Inductive LE : nat -> nat -> Prop := 
  | Le_O : forall n : nat, LE 0 n 
  | Le_S : forall n m : nat, LE n m -> LE (S n) (S 
m).

Inductive Mem (A : Set) (a : A) : list A -> Prop :=
  | here : forall x : list A, Mem A a (cons A a x) 
  | there : forall x : list A, Mem A a x ->  
forall b : A, Mem A a (cons A b x).

(* 5.1 *)
Theorem not_sn_le_o: forall n:nat, ~ LE (S n) O.
Proof.
  unfold not.
  intros.
  inversion H.
Qed.

(* 5.2 *)
Theorem nil_empty (A:Set): forall a:A, ~ Mem A a (nil A).
Proof.
  unfold not.
  intros.
  inversion H.
Qed.

(* 5.3 *)
Theorem e53: ~ LE 4 3.
Proof.
  unfold not.
  intro.
  repeat (inversion_clear H; inversion_clear H0).
Qed.

(* 5.4 *)
Theorem e54: forall n:nat, ~ LE (S n) n.
Proof.
  unfold not.
  intros.
  induction n;
  inversion H;
  exact (IHn H2).
Qed.

(* 5.5 *)
Theorem e55: forall n m p:nat,
  LE n m /\ LE m p -> LE n p.
Proof.
  induction n.
  intros.
    apply Le_O.

    intros.
    destruct H.
    inversion H0.
    rewrite <- H1 in H.
    apply not_sn_le_o in H.
    contradiction.

    apply Le_S.
    rewrite <- H2 in H.
    inversion H.
    apply (IHn n0 m0).
    split; trivial.
Qed.

(* 5.6 *)

End Ejercicio1.

Section Ejercicio3.

Variable A : Set.
Parameter equal : A -> A -> bool.

Axiom equal1 : forall x y : A, equal x y = true -> 
x = y.
Axiom equal2 : forall x : A, equal x x <> false.

Inductive List : Set :=
  | nullL : List
  | consL : A -> List -> List.

Inductive MemL (a : A) : List -> Prop :=
  | hereL : forall x : List, MemL a (consL a x)
  | thereL : forall x : List, MemL a x -> forall b
: A, MemL a (consL b x).

(* 3.1 *)
Inductive isSet : List -> Prop :=
  | isSetNil : isSet nullL
  | isSetCons : forall (x : A) (l : List),
    ~MemL x l /\ isSet l -> isSet (consL x l).

(* 3.2 *)
Fixpoint deleteAll (x : A) (xs : List): List :=
  match xs with
    | nullL => xs
    | consL y ys =>
      if equal x y
      then deleteAll x ys
      else consL y (deleteAll x ys)
  end.

(* 3.3 *)
Lemma DeleteAllNotMember : forall (l : List) (x : A),
   ~ MemL x (deleteAll x l).
Proof.
  unfold not.
  intros.
  inversion H.
    induction l.
      inversion H.

      simpl in H, H1.
    inversion H.

    apply IHl.
    simpl in H.
    destruct (equal x a).
      trivial.

      inversion H.
      
  inversion H.
    destruct l.


  induction l.
    intros.
    inversion_clear H.

    intros.
    apply (IHl x).
    simpl in H, IHl.
    destruct (equal x a).
      trivial.

      induction l.
      simpl in H.
      simpl.

  unfold not.
  intros.
  induction l.
    simpl in H.
    inversion H.

    simpl in H.
    destruct (equal x a).
      apply (IHl H).

      
Qed.

End Ejercicio3.