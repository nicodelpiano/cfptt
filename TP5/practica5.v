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
Fixpoint deleteAll (x : A) (xs : List) : List :=
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
  induction l.
    inversion H.

    inversion H.
    simpl in H.
    remember (equal x a) as y.
    destruct y.
      exact (IHl H).

      injection H1.
      intros.
      symmetry in Heqy.
      rewrite H2 in Heqy.
      apply equal2 in Heqy.
      trivial.

    simpl in H.
    remember (equal x a) as y.
    destruct y.
      exact (IHl H).

      injection H0.
      intros.
      rewrite <- H2 in IHl.
      exact (IHl H1).
Qed.

(* 3.4 *)
Fixpoint delete (x : A) (xs : List) : List :=
  match xs with
    nullL => nullL
    | consL y ys =>
      if equal x y then ys
      else consL y (delete x ys)
  end.

Lemma setCons : forall (l : List) (x : A),
  isSet (consL x l) -> isSet l.
Proof.
  intros.
  induction l.
    apply isSetNil.

    inversion H.
    destruct H1.
    trivial.
Qed.

(* 3.5 *)
Lemma DeleteNotMember : forall (l : List) (x : A), 
isSet l -> ~ MemL x (delete x l).
Proof.
  unfold not.
  intros.
  induction l.
    inversion H0.

    simpl in H0.
    remember (equal x a) as y.
    destruct y.
    symmetry in Heqy.
    apply equal1 in Heqy.
    inversion H.
    destruct H2.
    rewrite <- Heqy in H2.
    contradiction.

    inversion H0.
    symmetry in Heqy.
    rewrite H2 in Heqy.
    apply equal2 in Heqy.
    trivial.
    apply setCons in H.
    apply IHl; trivial.
Qed.

End Ejercicio3.

Section Ejercicio4.

Variable A : Set.

Inductive AB : Set :=
   nullAB : AB
   | consAB : A -> AB -> AB -> AB.

(* 4.a *)
Inductive Pertenece : A -> AB -> Prop :=
  pertNullAB : forall (x : A) (t1 t2 : AB),
    Pertenece x (consAB x t1 t2)
  | pertConsABLeft : forall (x y: A) (t1 t2 : AB),
    Pertenece x t1 -> Pertenece x (consAB y t1 t2)
  | pertConsABRight : forall (x y: A) (t1 t2 : AB),
    Pertenece x t2 -> Pertenece x (consAB y t1 t2).

(* 4.b *)
Parameter eqGen: A -> A -> bool.

Fixpoint Borrar (ab : AB) (x : A) : AB :=
  match ab with
    nullAB => nullAB
    | consAB y lt rt =>
      if eqGen x y then nullAB
      else consAB y (Borrar lt x) (Borrar rt x)
  end.

(* 4.c *)
Axiom eqGen1 : forall x : A, ~ (eqGen x x) = false. 
(*(negb (eqGen x x)) = false.*)

Lemma e4cAux : forall (t1 t2 : AB) (a b : A),
  ~ (Pertenece a t1) /\
  ~ (Pertenece a t2) /\
  eqGen a b = false ->
  Pertenece a (consAB b t1 t2) -> False.
Proof.
  unfold not.
  intros.
  destruct H as [H1 [H2 H3]].
  inversion H0.
    rewrite H5 in H3.
    apply eqGen1 in H3.
    trivial.

    exact (H1 H5).

    exact (H2 H5).
Qed.

Lemma BorrarNoPertenece: forall (x : AB) (a : A),
  ~(Pertenece a (Borrar x a)).
Proof.
  unfold not.
  intros.
  induction x.
    inversion H.

    simpl in H.
    remember (eqGen a a0) as y.
    destruct y.
      inversion H.

      symmetry in Heqy.
      apply (e4cAux (Borrar x1 a) (Borrar x2 a) a a0);
        [ unfold not; split; [ | split]
        | ]; trivial.
Qed. 

End Ejercicio4.