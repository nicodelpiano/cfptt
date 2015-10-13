Section Definiciones.

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

(* Apartado 3 *)
Fixpoint pot (n m : nat) {struct m} : nat :=
  match m with
    0 => 1
    | S k => prod n (pot n k)
  end.

(* Apartado 4 *)
Fixpoint leBool (n m : nat) : bool :=
  match n, m with
    0, _ => true
    | S k, 0 => false
    | S k1, S k2 => leBool k1 k2
  end.

Inductive list (X:Set) : Set :=
  nil : list X
  | cons : X -> list X -> list X.

(* Apartado 1 *)
Fixpoint length (A:Set) (xs:list A): nat :=
  match xs with
    nil => 0
    | cons y ys => sum 1 (length A ys)
  end.

(* Apartado 2 *)
Fixpoint append (A:Set) (xs:list A) (ys:list A): list A :=
  match xs, ys with
    nil, _ => ys
    | cons z zs, _ => cons A z (append A zs ys)
  end.

(* Apartado 3 *)
Fixpoint reverse (A:Set) (xs:list A) : list A :=
  match xs with
    nil => nil A
    | cons z zs => append A (reverse A zs) (cons A z (nil A))
  end.

(* Apartado 4 *)
Fixpoint filter (A:Set) (f:A->bool) (xs:list A) : list A :=
  match xs with
    nil => nil A
    | cons y ys => if f y then cons A y (filter A f ys) else filter A f ys
  end.

(* Apartado 5 *)
Fixpoint map (A B:Set) (f:A -> B) (xs:list A) : list B :=
  match xs with
    nil => nil B
    | cons y ys => cons B (f y) (map A B f ys)
  end.

(* Apartado 6 *)
Fixpoint exists_ (A:Set) (p:A -> bool) (xs:list A) : bool :=
  match xs with
    nil => false
    | cons y ys => if p y then true else exists_ A p ys
  end.

End Definiciones.

Section Ejercicio9.

(* 9.1 *)
Lemma SumO : forall n : nat, sum n 0 = n.
Proof.
  apply nat_ind; [ | intros; simpl; rewrite H ]; trivial.
Qed.

(* 9.2 *)
Lemma SumS : forall n m : nat, sum n (S m) = sum (S n) m.
Proof.
  intro.
  elim n; simpl; [ | intros; rewrite -> H]; trivial.
Qed.

(* 9.3 *)
Lemma SumConm : forall n m : nat, sum n m = sum m n.
Proof.
  intro.
  elim n; simpl; [ | intros; rewrite -> H]; trivial.
Qed.

(* 9.4 *)
Lemma SumAsoc : forall n m p : nat, sum n (sum m p) = sum (sum n m) p.
Proof.
  intro.
  elim n; simpl; [ | intros; rewrite -> H ]; trivial.
Qed.

(* Lemas auxiliares para resolver 9.5 *)
Lemma Prod0 : forall m : nat, prod m 0 = 0.
Proof.
  induction m;
  [ | simpl; rewrite IHm ]; trivial.
Qed.

Lemma ProdS : forall n m : nat,
  prod n (S m) = sum (prod n m) n.
Proof.
  intros.
  induction n;
  [ |
    rewrite SumConm;
    simpl;
    rewrite SumS;
    rewrite SumAsoc;
    rewrite IHn;
    rewrite (SumConm (prod n m) n)
  ]; trivial.
Qed.

(* 9.5 *)
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

(* 9.7 *)
Lemma ProdDistr : forall n m p : nat,
  prod n (sum m p) = sum (prod n m) (prod n p).
Proof.
  intros.
  induction n;
  [ |
    simpl;
    rewrite IHn;
    do 2 rewrite <- SumAsoc;
    rewrite (SumConm m (sum (prod n p) p));
    rewrite <- (SumAsoc (prod n p) p m);
    rewrite (SumConm m p)
  ]; trivial.
Qed.

(* 9.6 *)
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

(* 10.1 *)
Lemma L1 : forall (A : Set) (l : list A), append A l (nil
 A) = l.
Proof.
  intros.
  induction l;
  [ | simpl; rewrite IHl ]; trivial.
Qed.

(* 10.2 *)
Lemma L2 : forall (A : Set) (l : list A) (a : A), ~(cons 
A a l) = nil A.
Proof.
  unfold not.
  intros.
  discriminate H.
Qed.

(* 10.3 *)
Lemma L3 : forall (A : Set) (l m : list A) (a : A), 
cons A a (append A l m) = append A (cons A a l) m.
Proof.
  intros.
  destruct l; trivial.
Qed.

(* 10.4 *)
Lemma L4 : forall (A : Set) (l m : list A), 
length A (append A l m) = sum (length A l) (length 
A m).
Proof.
  intros.
  induction l;
  [ | simpl; rewrite IHl]; trivial.
Qed.

(* 10.5 *)
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

(* 10.6 *)
Lemma L6 : forall (A : Set) (l m : list A),
 reverse A (append A l m) = append A (reverse A m) (reverse A l).
Proof.
  intros.
  induction l; simpl;
  [ rewrite L1
    |
    rewrite IHl;
    rewrite AppendAsoc
  ]; trivial.
Qed.

End Ejercicio10.

Section Ejercicio11.

(* 11.1 *)
Lemma  L7 : forall (A B : Set) (l m : list A) (f : A -> B),
  map A B f (append A l m) = append B (map A B f l) (map A B f m).
Proof.
  intros.
  induction l;
  [ | simpl; rewrite IHl ]; trivial.
Qed.

(* 11.2 *)
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

(* 11.3 *)
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

(* 11.4 *)
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

Section Ejercicio16.

(* 16.1 *)
Inductive posfijo (A: Set): list A -> list A -> Prop :=
  posfijoE : forall l: list A, posfijo A l l
  | posfijoL : forall (l1 l2: list A) (x: A),
    posfijo A l1 l2 -> posfijo A l1 (cons A x l2).

(* 16.2 *)
Lemma e162a (A : Set) : forall l1 l2 l3 : list A,
  l2 = append A l3 l1 -> posfijo A l1 l2.
Proof.
  intros.
  rewrite H.
  clear H.
  induction l3;
  simpl;
  [ apply posfijoE
    |
    apply posfijoL;
    trivial
  ].
Qed.

Lemma e162b (A: Set): forall l1 l2: list A,
  posfijo A l1 l2 -> (exists l3: list A, l2 = append A l3 l1).
Proof.
  intros.
  induction H;
  [ exists (nil A)
    |
    elim IHposfijo;
    intros;
    exists (cons A x x0);
    rewrite H0
   ]; simpl; trivial.
Qed.

(* 16.3 *)
Fixpoint ultimo (A: Set) (xs: list A) {struct xs}: list A :=
  match xs with
    nil => nil A
    | cons y nil => xs
    | cons y ys => ultimo A ys
  end.

Eval simpl in (ultimo nat (cons nat 1 (cons nat 2 (cons nat 3 (nil nat))))).

(* 16.4 *)
Lemma e164 (A: Set):
  forall l: list A, posfijo A (ultimo A l) l.
Proof.
  intro.
  induction l;
  simpl;
  [ apply posfijoE
    |
    destruct l;
      [ apply posfijoE
        |
        apply posfijoL
      ];
      trivial
   ].
Qed.

End Ejercicio16.

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

Section Ejercicio19.

(* 19.1 *)
Variable A: Set.

Inductive ACom: nat -> Set :=
  | leafACom: A -> ACom 0
  | consACom: forall n: nat, A -> ACom n -> ACom n -> ACom (S n).

Variable a: A.

Check (leafACom a).

(* 19.2 *)
Fixpoint h (n: nat) (t: ACom n): nat :=
    match t with
      leafACom _ => 1
      | consACom n0 x t1 t2 => h n0 t1 + h n0 t2
    end.

Eval simpl in (h 0 (leafACom a)).

(* 19.3 *)

Parameter poten: nat -> nat -> nat.

Axiom potO : forall n : nat, poten (S n) 0 = 1.  
(*  n0 = 1 ∀ n>0  *) 
Axiom potS : forall m: nat, poten 2 (S m) = sum (poten 2 m) (poten 2 m). 
(*  2m+1 = 2m + 2m  *)

Lemma e193: forall (n: nat) (t: ACom n),
  h n t = poten 2 n.
Proof.
  intros.
  induction t;
  [ rewrite potO
    |
    simpl;
    rewrite (potS n)
  ]; auto.
Qed.

End Ejercicio19.

Section Ejercicio20.

Definition max: nat -> nat -> nat :=
  fun n m =>
    if leBool m n then n else m.

(* 20.1 *)
Inductive AB (A: Set): nat -> Set :=
  | emptyAB: AB A 0
  | branchAB: forall n k: nat,
  A -> AB A n -> AB A k -> AB A (S (max n k)).

(* 20.2 *)
Fixpoint camino (A: Set) (n: nat) (t: AB A n): list A :=
  match t with
    emptyAB => nil A
    | branchAB n1 n2 x t1 t2 =>
      if leBool n2 n1
      then cons A x (camino A n1 t1)
      else cons A x (camino A n2 t2)
  end.

(* Prueba de ejemplo *)
Definition e := emptyAB nat.
Definition t1 := branchAB nat 0 0 1 e e.
Definition t2 := branchAB nat 1 1 2 t1 t1.
Definition t3 := branchAB nat 1 2 3 t1 t2.
Definition t4 := branchAB nat 1 0 4 t1 e.
Definition t5 := branchAB nat 1 2 5 t1 t4.
Definition t6 := branchAB nat 3 3 6 t3 t5.

Eval simpl in (camino nat 0 e).
Eval simpl in (camino nat 3 t5).
Eval simpl in (camino nat 4 t6).

(* 20.3 *)
Lemma e203 (A: Set): forall (n: nat) (t: AB A n),
  length A (camino A n t) = n.
Proof.
  intros.
  induction t; simpl;
  [ |
    unfold max;
    case (leBool k n);
    simpl;
      [ rewrite IHt1 | rewrite IHt2 ]
   ]; trivial.
Qed.

End Ejercicio20.