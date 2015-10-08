Section Ejercicio1.

Inductive list (X:Set) : Set :=
  nil : list X
  | cons : X -> list X -> list X.

Definition nilnat: list nat := nil nat.
Definition consnat: nat -> list nat -> list nat:= cons nat.

Check(list nat).
Check(consnat 0 nilnat).

Inductive arbol (X:Set) :=
  empty : arbol X
  | branch : X -> arbol X -> arbol X -> arbol X.

Inductive bintree (X:Set) :=
  Empty : bintree X
  | Branch : X -> bintree X -> bintree X -> bintree X.

Variable f : Set -> Set.

Inductive array (X:Set) : nat -> Set :=
  emptyarr : array X 0
  | consarr : forall n: nat,
    X -> array  X n ->  array X  (n + 1).

Inductive matrix (X:Set) : nat -> nat -> Set :=
  one_col : forall n: nat, array X n -> matrix X n 1 
  | consm : forall n m: nat,
    matrix X n m -> array X n -> matrix X n (m+1).


Inductive leq : nat -> nat -> Prop :=
  le0 : forall n:nat, leq 0 n
  | leS : forall n m:nat, leq n m -> leq (S n) (S m).


(**
Fixpoint leq (n : nat) (m : nat) : bool := match n, m with
                                           | 0, _ => true
                                           | _, 0 => false
                                           | (S s), (S t) => leq s t
                                           end.

Eval compute in (leq 1 2).
**)


Inductive eq_list (X:Set) : list X -> list X -> Prop :=
  eq_list_nil : eq_list X (nil X) (nil X)
  | eq_list_cons : forall (l1 l2 : list X) (x1 x2 : X),
    x1 = x2 -> eq_list X (cons X x1 l1) (cons X x2 l2).

Inductive sorted (X:Set) (f:X->X->Prop) : list X -> Prop :=
  sorted_nil : sorted X f (nil X)
  | sorted_singleton : forall x:X, sorted X f (cons X x (nil X))
  | sorted_cons : forall (l : list X) (x1 x2 : X),
    f x1 x2 -> sorted X f (cons X x2 l) ->
      sorted X f (cons X x1 (cons X x2 l)).

Inductive mirror (X:Set) : bintree X -> bintree X -> Prop :=
  mirror_empty : mirror X (Empty X) (Empty X)
  | mirror_branch : forall (t11 t12 t21 t22 : bintree X) (x1 x2 : X),
    mirror X t11 t22 -> mirror X t12 t21 ->
      x1 = x2 -> mirror X (Branch X x1 t11 t12) (Branch X x2 t21 t22).

Inductive isomorfo (X:Set) : arbol X -> arbol X -> Prop :=
  isomorfo_empty : isomorfo X (empty X) (empty X)
  | isomorfo_branch : forall (t11 t12 t21 t22 : arbol X) (x1 x2 : X),
    isomorfo X t11 t21 -> isomorfo X t12 t22 ->
      isomorfo X (branch X x1 t11 t12) (branch X x2 t21 t22).

(**
data Tree a b = Empty | Leaf a | Branch b (Tree a b) (Tree a b)
**)

Inductive GenTree'' (A B : Set) : Set :=
  nodeGT'' : A -> GenForest'' A B -> GenTree'' A B
with
  GenForest'' (A B : Set) : Set :=
    leafGF'' : B -> GenForest'' A B
    | consGF'' : GenTree'' A B -> GenForest'' A B -> GenForest'' A B.

Inductive GenTree (A B : Set) : Set :=
  leafGT : B -> GenTree A B
  | nodeGT : A -> GenForest A B -> GenTree A B
with
  GenForest (A B : Set) : Set :=
    leafGF : GenTree A B -> GenForest A B
    | consGF : GenTree A B -> GenForest A B -> GenForest A B.

Definition tree_1 : GenTree nat bool :=
  nodeGT nat bool 1 (leafGF nat bool (leafGT nat bool true)).

Check (consGF nat bool tree_1 (leafGF nat bool (leafGT nat bool false))).
Check (leafGT nat bool true).

Definition tree'_1 := leafGT nat bool true.

Check (nodeGT nat bool 1 (leafGF nat bool tree'_1)).

Inductive GenTree' (A B : Set) : Set :=
  leafGT' : GenForest' A B -> GenTree' A B
  | nodeGT' : B -> GenForest' A B -> GenTree' A B
with
  GenForest' (A B : Set) : Set :=
    leafGF' : A -> GenForest' A B
    | consGF' : GenTree' A B -> GenForest' A B -> GenForest' A B.

Check (leafGT' nat bool
  (leafGF' nat bool 1)).

End Ejercicio1.

Section Ejercicio2.

(* Apartado 1 *)

Definition Or : bool -> bool -> bool :=
  fun b1 b2 =>
    match b1, b2 with
      true, _ => true
      | _, true => true
      | _, _ => false
    end.

Eval compute in (Or true false).

Definition And : bool -> bool -> bool :=
  fun b1 b2 =>
    match b1, b2 with
      true, _ => b2
      | false, _ => false
    end.

Eval compute in (And true false).
Eval compute in (And false true).

Definition Not : bool -> bool :=
  fun b =>
    match b with
      true => false
      | _ => true
    end.

Eval compute in (Not true).

Definition Xor : bool -> bool -> bool :=
  fun b1 b2 =>
    match b1, b2 with
      true, true => false
      | false, false => false
      | _, _ => true
    end.

(* Apartado 2 *)

Definition is_nil (A : Set) : list A -> bool :=
  fun xs =>
    match xs with
      nil => true
      | _ => false
    end.

Eval simpl in (is_nil nat (nil nat)).
Eval simpl in (is_nil nat (cons nat 1 (nil nat))).

End Ejercicio2.

Section Ejercicio3.

(* Apartado 1 *)
Fixpoint sum (n m : nat) : nat :=
    match n with
      0 => m
      | (S k) => S (sum k m)
    end.

(* Apartado 2 *)
Fixpoint prod (n m : nat) : nat :=
    match n with
      0 => 0
      | (S k) => sum (prod k m) m
    end.

Eval simpl in (prod 1000 0).
Eval simpl in (forall n: nat, prod n 0 = 0).

(* Apartado 3 *)
Fixpoint pot (n m : nat) {struct m} : nat :=
  match m with
    0 => 1
    | S k => prod n (pot n k)
  end.

Eval simpl in (pot 9 3).

(* Apartado 4 *)
Fixpoint leBool (n m : nat) : bool :=
  match n, m with
    0, _ => true
    | S k, 0 => false
    | S k1, S k2 => leBool k1 k2
  end.

Eval simpl in (leBool 44 331).

End Ejercicio3.

Section Ejercicio4.

Check nil.

(* Apartado 1 *)
Fixpoint length (A:Set) (xs:list A): nat :=
  match xs with
    nil => 0
    | cons y ys => sum 1 (length A ys)
  end.

Eval simpl in (length bool (cons bool true (nil bool))).

(* Apartado 2 *)
Fixpoint append (A:Set) (xs:list A) (ys:list A): list A :=
  match xs, ys with
    nil, _ => ys
    | cons z zs, _ => cons A z (append A zs ys)
  end.

Eval simpl in (append nat (cons nat 3 (cons nat 1 (nil nat)))
  (cons nat 2 (nil nat))).

Definition singleton (A:Set) (a:A) : list A := cons A a (nil A).

(* Apartado 3 *)
Fixpoint reverse (A:Set) (xs:list A) : list A :=
  match xs with
    nil => nil A
    | cons z zs => append A (reverse A zs) (cons A z (nil A))
  end.

Eval compute in (reverse nat (cons nat 1 (cons nat 2 (nil nat)))).

(* Apartado 4 *)
Fixpoint filter (A:Set) (f:A->bool) (xs:list A) : list A :=
  match xs with
    nil => nil A
    | cons y ys => if f y then cons A y (filter A f ys) else filter A f ys
  end.

Eval compute in
(
filter nat
  (fun x => leBool 2 x)
  (cons nat 0 (cons nat 12 (cons nat 33 (nil nat))))
).

(* Apartado 5 *)
Fixpoint map (A B:Set) (f:A -> B) (xs:list A) : list B :=
  match xs with
    nil => nil B
    | cons y ys => cons B (f y) (map A B f ys)
  end.

Eval compute in (map nat nat (fun x => x + 1) (cons nat 1 (nil nat))).

(* Apartado 6 *)
Fixpoint exists_ (A:Set) (p:A -> bool) (xs:list A) : bool :=
  match xs with
    nil => false
    | cons y ys => if p y then true else exists_ A p ys
  end.

Eval compute in
(
exists_ nat
  (fun x => leBool 4 x)
  (cons nat 0 (cons nat 5 (cons nat 1 (cons nat 12 (nil nat)))))
).

End Ejercicio4.

Section Ejercicio5.

(* Apartado 1 *)
Fixpoint inverse (X : Set) (b : bintree X) : bintree X :=
  match b with
    Empty => Empty X
    | (Branch e l r) => Branch X e (inverse X r) (inverse X l)
  end.

Eval compute in (inverse nat (Branch nat 1 (Empty nat)
  (Branch nat 2 (Empty nat) (Empty nat)))).
Eval compute in
(
  mirror nat
    (inverse nat (Branch nat 1 (Empty nat)
      (Branch nat 2 (Empty nat) (Empty nat))))
    (Branch nat 1 (Empty nat) (Branch nat 2 (Empty nat) (Empty nat)))
).

(* Apartado 2 *)

(*
Inductive GenTree (A B : Set) : Set :=
  leafGT : B -> GenTree A B
  | nodeGT : A -> GenForest A B -> GenTree A B
with
  GenForest (A B : Set) : Set :=
    leafGF : GenTree A B -> GenForest A B
    | consGF : GenTree A B -> GenForest A B -> GenForest A B.
*)

(*Fixpoint nodes (X Y : Set) (gt : GenTree X Y) : bool :=
*)  

End Ejercicio5.

Section Ejercicio6.

Definition listN := list nat.

Fixpoint nat_eq (n:nat) (m:nat) : bool :=
  match n, m with
    0, 0 => true
    | S k1, S k2 => nat_eq k1 k2
    | _, _ => false
  end.

(* 6.1 *)
Fixpoint member (n:nat) (xs:listN) : bool :=
  match xs with
    nil => false
    | cons m ys => Or (nat_eq m n) (member n ys)
  end.

Eval compute in (member 2 (cons nat 2 (cons nat 2 (nil nat)))).

(* 6.2 *)
Fixpoint delete (xs:listN) (n:nat) : listN :=
  match xs with
    nil => nil nat
    | cons m ys => if nat_eq m n then
  delete ys n else cons nat m (delete ys n)
  end.

Eval compute in (delete
  (cons nat 2 (cons nat 2 (cons nat 80 (nil nat)))) 8).

(* 6.3 *)
Fixpoint insert (x:nat) (xs:listN) {struct xs} : listN :=
  match xs with
    nil => cons nat x (nil nat)
    | cons y ys =>
    match leBool x y with
      true => cons nat x (cons nat y ys)
      | _  => cons nat y (insert x ys)
    end
  end.

Fixpoint insert_sort (xs:listN) : listN :=
  match xs with
    nil => nil nat
    | cons y ys => insert y (insert_sort ys)
  end.

Eval compute in
(
  insert_sort
    (
      (cons nat 45
      (cons nat 0
      (cons nat 93
      (cons nat 12
      (nil nat)
      ))))
    )
).

(* Generalizaciones *)

End Ejercicio6.

Section Ejercicio7.

(* 7.1 *)
Inductive Exp (A:Set) : Set :=
  atom : A -> Exp A
  | Sum : Exp A -> Exp A -> Exp A
  | Mul : Exp A -> Exp A -> Exp A
  | Minus : Exp A -> Exp A.

(* 7.2 *)
Fixpoint InterpretNat (ne : Exp nat) : nat :=
  match ne with
    atom n => n
    | Sum n1 n2 => (InterpretNat n1) + (InterpretNat n2)
    | Mul n1 n2 => (InterpretNat n1) * (InterpretNat n2)
    | Minus n => InterpretNat n
  end.

(* 7.3 *)
Fixpoint InterpretBool (be : Exp bool) : bool :=
  match be with
    atom b => b
    | Sum b1 b2 => Or (InterpretBool b1) (InterpretBool b2)
    | Mul b1 b2 => And (InterpretBool b1) (InterpretBool b2)
    | Minus b => Not (InterpretBool b)
  end.

End Ejercicio7.

Section Ejercicio8.

(* 8.1 *)
Theorem andAsoc : forall p q r: bool,
  And (And p q) r = And p (And q r).
Proof.
  destruct p; reflexivity.
Qed.

Theorem orAsoc : forall p q r: bool,
  Or (Or p q) r = Or p (Or q r).
Proof.
  destruct p;
  destruct q;
  destruct r;
  reflexivity.
Qed.

Theorem andConmut : forall p q : bool, And p q = And q p.
Proof.
  destruct p;
  destruct q;
  reflexivity.
Qed.

Theorem orConmut : forall p q : bool, Or p q = Or q p.
Proof.
  destruct p;
  destruct q;
  reflexivity.
Qed.

(* 8.2 *)
Lemma LAnd : forall a b : bool, (And a b = true) <->
  (a = true /\ b = true).
Proof.
  destruct a;
  destruct b;
  compute;
  split;
  intro;
  [split | | split |destruct H as [_ H] |split
  |destruct H as [H _] |split |destruct H as [H _] ];
  trivial.
Qed.

(* 8.3 *)
Lemma LOr1 : forall a b : bool, Or a b = false <->
  a = false /\ b = false.
Proof.
  destruct a;
  destruct b;
  compute;
  split;
  intro;
  [split |destruct H as [_ H] | split |destruct H as [H _]
  |split |destruct H as [_ H] | split |split ];
  trivial.
Qed.

(* 8.4 *)
Lemma LOr2 : forall a b : bool, Or a b = true
  <-> a = true \/ b = true.
Proof.
  destruct a;
  destruct b;
  compute;
  split;
  intro;
  [right | | left |
  |right | | right | elim H; intros];
  trivial.
Qed.

(* 8.5 *)
Lemma LXor : forall a b : bool, Xor a b = true <-> a <> b.
Proof.
  intuition.
  destruct a; rewrite <- H0 in H; discriminate.
  destruct a; destruct b; compute;
    [elim H | | | elim H]; trivial.
Qed.

(* 8.6 *)
Lemma LNot : forall b : bool, Not (Not b) = b.
Proof.
  destruct b; trivial.
Qed.

End Ejercicio8.

Section Ejercicio9.

Lemma SumO : forall n : nat, sum n 0 = n.
Proof.
  apply nat_ind; [ | intros; simpl; rewrite H ]; trivial.
Qed.

Lemma SumS : forall n m : nat, sum n (S m) = sum (S n) m.
Proof.
  intro.
  elim n; simpl; [ | intros; rewrite -> H]; trivial.
Qed.

Lemma SumConm : forall n m : nat, sum n m = sum m n.
Proof.
  intro.
  elim n; simpl; [ | intros; rewrite -> H]; trivial.
Qed.

Lemma SumAsoc : forall n m p : nat, sum n (sum m p) = sum (sum n m) p.
Proof.
  intro.
  elim n; simpl; [ | intros; rewrite -> H ]; trivial.
Qed.

Check prod.

Lemma Prod0 : forall m : nat, prod m 0 = 0.
Proof.
  induction m;
  [ | simpl; rewrite IHm ]; trivial.
Qed.

Lemma ProdS : forall n m : nat,
  prod n (S m) = sum (prod n m) n.
Proof.
  intros.
  induction n.
    trivial.

    simpl.
    rewrite IHn.
    rewrite SumConm.
    rewrite SumAsoc.
    simpl.
    rewrite SumConm.
    rewrite SumAsoc.
    rewrite SumConm.
    rewrite (SumConm n m).
    rewrite SumAsoc.
    trivial.
Qed.

Lemma ProdConm : forall n m : nat, prod n m = prod m n.
Proof.
  intros.
  induction n;
  [ symmetry; apply Prod0
  |
    rewrite ProdS;
    simpl;
    rewrite IHn;
    trivial ].
Qed.

Lemma ProdDistr : forall n m p : nat,
  prod n (sum m p) = sum (prod n m) (prod n p).
Proof.
  intros.
  induction n;
  [ |
    simpl;
    rewrite IHn;
    rewrite SumAsoc;
    rewrite SumAsoc;
    rewrite <- (SumAsoc (prod n m) m (prod n p));
    rewrite (SumConm m (prod n p));
    rewrite <- (SumAsoc (prod n m) (prod n p) m)
  ]; trivial.
Qed.

Lemma ProdAsoc : forall n m p : nat, prod n (prod m p) = 
prod (prod n m) p.
Proof.
  intros.
  induction n;
  [ |
    simpl;
    rewrite IHn;
    rewrite (ProdConm (sum (prod n m) m) p);
    rewrite ProdDistr;
    rewrite ProdConm;
    rewrite (ProdConm m p)
  ]; trivial.
Qed.

End Ejercicio9.

Section Ejercicio10.

Lemma L1 : forall (A : Set) (l : list A), append A l (nil
 A) = l.
Proof.
  intros.
  induction l;
  [ |
    simpl;
    rewrite IHl
  ]; trivial.
Qed.

Lemma L2 : forall (A : Set) (l : list A) (a : A), ~(cons 
A a l) = nil A.
Proof.
  unfold not.
  intros.
  discriminate H.
Qed.

Lemma L3 : forall (A : Set) (l m : list A) (a : A), 
cons A a (append A l m) = append A (cons A a l) m.
Proof.
  intros.
  induction l; [ | simpl ]; trivial.
Qed.

Lemma L4 : forall (A : Set) (l m : list A), 
length A (append A l m) = sum (length A l) (length 
A m).
Proof.
  intros.
  induction l;
  [ | simpl; rewrite IHl]; trivial.
Qed.

Lemma L5 : forall (A : Set) (l : list A),
  length A (reverse A l) = length A l.
Proof.
  intros.
  induction l;
  [ trivial
  | simpl;
    rewrite <- IHl;
    rewrite L4;
    simpl;
    apply SumConm
  ].
Qed.

(* Lema auxiliar, asociatividad del append *)
Lemma AppendAsoc : forall (A : Set) (l m n : list A),
  append A (append A l m) n = append A l (append A m n).
Proof.
  intros.
  induction l;
  [ | simpl; rewrite IHl ]; trivial.
Qed.

Lemma L6 : forall (A : Set) (l m : list A),
 reverse A (append A l m) = append A (reverse A m) (reverse A l).
Proof.
  intros.
  induction l; simpl;
  [ rewrite L1
  | rewrite IHl;
    rewrite AppendAsoc
  ]; trivial.
Qed.

End Ejercicio10.

Section Ejercicio11.

Lemma  L7 : forall (A B : Set) (l m : list A) (f : A -> B),
  map A B f (append A l m) = append B (map A B f l) (map A B f m).
Proof.
  intros.
  induction l;
  [ |
    simpl;
    rewrite IHl
  ]; trivial.
Qed.

Lemma L8 : forall (A : Set) (l m : list A) (P : A -> bool),
  filter A P (append A l m) = append A (filter A P l) (filter A P m).
Proof.
  intros.
  induction l;
  [ |
    simpl;
    rewrite IHl;
    case (P x)
  ]; trivial.
Qed.

Lemma L9 : forall (A : Set) (l m n : list A),
  append A l (append A m n) = append A (append A l m) n.
Proof.
  intros.
  induction l;
  [ |
    simpl;
    rewrite IHl
  ]; trivial.
Qed.

Lemma L10 : forall (A : Set) (l : list A),
reverse A (reverse A l) = l.
Proof.
  intros.
  induction l;
  [ | simpl; rewrite L6; rewrite IHl ]; trivial.
Qed.

End Ejercicio11.

Section Ejercicio12.

Fixpoint filterMap (A B : Set) (P : B -> bool) (f : A -> B)
  (l : list A) {struct l} : list B :=
    match l with
    | nil => nil B
    | cons a l1 =>
      match P (f a) with
      | true => cons B (f a) (filterMap A B P f l1)
      | false => filterMap A B P f l1
      end
    end.

Lemma FusionFilterMap :
  forall (A B : Set) (P : B -> bool) (f : A -> B) (l : list A), 
    filter B P (map A B f l) = filterMap A B P f l.
Proof.
  intros.
  induction l;
  [ | simpl; case (P (f x)); rewrite IHl ]; trivial.
Qed.

End Ejercicio12.

Section Ejercicio18.
 
Variable A : Set. 
Inductive Tree_ : Set := 
  | nullT : Tree_ 
  | consT : A -> Tree_ -> Tree_ -> Tree_.

(* 18.1 *)
Inductive isSubTree: Tree_ -> Tree_ -> Prop :=
  | isSubTree0 : forall t: Tree_, isSubTree t t
  | isSubTree1 : forall (t1 t2 t3: Tree_) (x: A),
    isSubTree t1 t2 -> isSubTree t1 (consT x t2 t3)
  | isSubTree2 : forall (t1 t2 t3: Tree_) (x: A),
    isSubTree t1 t3 -> isSubTree t1 (consT x t2 t3).

(* 18.2 *)
Lemma isSubTreeReflex : forall t: Tree_,
  isSubTree t t.
Proof.
  apply isSubTree0.
Qed.

(* 18.3 *)
Lemma isSubTreeTrans : forall t1 t2 t3: Tree_,
  isSubTree t1 t2 /\ isSubTree t2 t3 -> isSubTree t1 t3.
Proof.
  intros.
  destruct H.
  induction H0;
  [ |
    apply isSubTree1;
    apply IHisSubTree
    |
    apply isSubTree2;
    apply IHisSubTree
  ]; trivial.
Qed.

End Ejercicio18.

Section Ejercicio16.

Check nil.

(*Inductive posfijo (A : Set) : list A -> list A -> Prop :=
  posfijoE : forall n : list A, posfijo A (nil A) n
  | posfijoL : forall n m: list A,
    (exists l : list A, m = append A l n) -> posfijo A n m.
*)

Inductive posfijo (A : Set) : list A -> list A -> Prop :=
  posfijoE : forall n : list A, posfijo A (nil A) n
  | posfijoL : forall n m: list A, forall x y: A,
    posfijo A n m -> posfijo A (cons A x n) (cons A y m).

(* 16.2 *)
Lemma aux16 (A : Set) : forall l : list A,
  posfijo A l l.
Proof.
  induction l.
    apply posfijoE.

    apply posfijoL.
    trivial.
Qed.

Lemma e162a (A : Set) : forall l1 l2 l3 : list A,
  l2 = append A l3 l1 -> posfijo A l1 l2.
Proof.
  induction l1.
    intros.
    apply posfijoE.

    intros.
    rewrite H.
    destruct l3.
      simpl.
      apply posfijoL.
      apply aux16.

      simpl.
      apply posfijoL.
      simpl in H.
      apply (IHl1 (append A l3 (cons A x l1)) (append A l3 (cons A x (nil A)))).
      rewrite <- (L9 A l3 (cons A x (nil A)) l1).
      simpl.
      trivial.
Qed.

Lemma aux162 (A : Set) : forall (l : list A) (x : A),
  append A (cons A x (nil A)) l = (cons A x l).
Proof.
  intros.
  simpl.
  trivial.
Qed.

Lemma e162b (A : Set) : forall l1 l2 : list A,
  posfijo A l1 l2 -> (exists l3 : list A, l2 = append A l3 l1).
Proof.
  intros.
  induction H.
    exists n.
    symmetry.
    apply (L1 A n).

    elim IHposfijo.
    intros xs H1.
    
    
Qed.

End Ejercicio16.