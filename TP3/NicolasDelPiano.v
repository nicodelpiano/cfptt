Section Ejercicio3.

Variable A B C: Set.

(* 3.1 3.2 3.3 *)
(* a la Haskell *)
Definition apply (f : A -> B)(a : A) : B := f a.
Definition o (f : A -> B)(g : B -> C) : A -> C := fun x => g (f x).
Definition twice (f : A -> A)(a : A) := f (f a).

(* con funciones lambda *)
Definition apply' := fun (f: A -> B) (x : A) => f x.
Definition o' := fun (f : A -> B) (g : B -> C) => (fun (x : A) => g (f x)).
Definition twice' := fun (f: A -> A) (x: A) => f (f x).

(* 3.4 *)
(* Redefino los operadores de arriba para que sean aplicables
   a cualquier conjunto *)
Definition apply'' : forall (A B: Set), (A -> B) -> A -> B
  := fun A B f x => f x.
Definition o'' : forall (A B C: Set), (A -> B) -> (B -> C) -> A -> C
  := fun A B C f g x => g (f x).
Definition twice'' : forall (A : Set), (A -> A) -> A -> A
  := fun A f x => f (f x).

End Ejercicio3.

Section Ejercicio5.

Variable A B C: Set.

(* 5.1 *)
Definition opI : forall A : Set, A -> A
  := fun A x => x.

Definition opK : forall A B : Set, A -> B -> A
  := fun A B x y => x.

Definition opS : forall A B C : Set, (A -> B -> C) -> (A -> B) -> A -> C
  := fun A B C f g x => (f x) (g x).

(* 5.2 *)
Lemma e52 : (opS A (A -> A) A) (opK A (A -> A)) (opK A A) = (opI A).
Proof.
lazy delta beta.
reflexivity.

Qed.

End Ejercicio5.

Section Ejercicio7.

(* 7.1 *)
Definition Bool := forall X : Set, X -> X -> X.
Definition t (X : Set) (p : X) (q : X) := p.
Definition f (X : Set) (p : X) (q : X) := q.

(* 7.2 *)
Definition If (c then' else' : Bool) : Bool
  := fun (X:Set) (x y:X) => (c X) (then' X x y) (else' X x y).

(* 7.3 *)
Definition Not (b : Bool) : Bool := If b f t.

Lemma CorrecNot : (Not t) = f /\ (Not f) = t.
Proof.
lazy.
split; reflexivity.
Qed.

(* 7.4 *)
Definition And (a b: Bool): Bool := If a b f.
Definition And' (a b: Bool): Bool := If a b a.

(* 7.5 *)
Infix "&" := And (left associativity, at level 94).

Lemma CorrecAnd : (t & t) = t /\ (f & t) = f /\ (t & f) = f.
Proof.
split; [idtac|split]; lazy; reflexivity.
Qed.

End Ejercicio7.

(* Ejercicio8 *)

Section ArrayNat.

Parameter ArrayNat : forall n:nat, Set.
Parameter empty    : ArrayNat 0.
Parameter add      : forall n:nat, nat -> ArrayNat n -> ArrayNat (n + 1).

(* 8.1 *)
Check (add 0 (S 0) empty).

(* 8.2 *)
(* Vector de 2 *)
Check ((add (S 0) 0 (add 0 0 empty))).

(* Vector de 4 *)
Check
(add (S (S (S 0))) 0
  (add (S (S 0)) (S 0)
    ((add (S 0) 0
      (add 0 (S 0) empty))))).

(* 8.3 *)
Parameter Concat : forall n m:nat, ArrayNat n -> ArrayNat m -> ArrayNat(n + m).

(* 8.4 *)
Parameter Zip : forall n:nat, ArrayNat n -> ArrayNat n
                -> (nat -> nat -> nat) -> ArrayNat n.

(* 8.5 *)
Check ArrayNat.

(* 8.6 *)
Parameter Array  : forall (t:Set) (n:nat), Set.
Parameter empty' : forall (t:Set), Array t 0.
Parameter add'   : forall (t:Set) (n:nat), t -> Array t n -> Array t (n + 1).
Parameter Zip'   : forall (t:Set) (n:nat), Array t n -> Array t n ->
(t -> t -> t) -> Array t n.

(* 8.7 *) 
Parameter ArrayBool : forall n:nat, Array bool n.

End ArrayNat.

Section Ejercicio11.

(* 11.1 *)
Parameter AVLNat : forall n : nat, Set.

(* Empty tree *)
Parameter emptyAVL : AVLNat 0.

(* 11.2 *)
(* Constructores *)
Parameter addAVL1 : forall (n: nat),
                    nat -> AVLNat n -> AVLNat n -> AVLNat (S n).
Parameter addAVL2 : forall (n: nat),
                    nat -> AVLNat n -> AVLNat (S n) -> AVLNat (S (S n)).
Parameter addAVL3 : forall (n: nat),
                    nat -> AVLNat (S n) -> AVLNat n -> AVLNat (S (S n)).

(* 11.3 *)
Definition avl2 := addAVL2 0 0 emptyAVL (addAVL1 0 0 emptyAVL emptyAVL).
(* Deberia tener tipo AVLNat 2 *)
Check (avl2).

(* 11.4 *)
Parameter AVL : forall (t: Set) (n:nat), Set.

(* Empty tree *)
Parameter emptyAVL' : forall (t:Set), AVL t 0.

(* Constructores *)
Parameter addAVL1' : forall (t:Set) (n: nat),
                     t -> AVL t n -> AVL t n -> AVL t (S n).
Parameter addAVL2' : forall (t:Set) (n: nat),
                     t -> AVL t n -> AVL t (S n) -> AVL t (S (S n)).
Parameter addAVL3' : forall (t:Set) (n: nat),
                     t -> AVL t (S n) -> AVL t n -> AVL t (S (S n)).
 
End Ejercicio11.

Section Ejercicio13.

Variable A B C: Prop.

Lemma Ej313_1 : (A -> B -> C) -> A -> (A -> C) -> B -> C.
Proof.
  intros f a g b.
  exact (g a).
Qed.

Lemma Ej313_2 : A -> ~ ~ A.
Proof.
  unfold not.
  intros.
  exact (H0 H).
Qed.

Lemma Ej313_3 : (A -> B -> C) -> A -> B -> C.
Proof.
     exact (fun f x y => f x y).
Qed.

Lemma Ej313_4 : (A -> B) -> ~ (A /\ ~ B).
Proof.
  unfold not.
  intros.
  elim H0; intros.
  exact (H2 (H H1)).
Qed.

End Ejercicio13.

Section Ejercicio14.

Variable U : Set.
Variable e : U.
Variable A B : U -> Prop.
Variable P : Prop.
Variable R : U -> U -> Prop.

Lemma Ej314_1 : (forall x : U, A x -> B x)
                -> (forall x : U, A x)
                -> forall x : U, B x.
Proof.
  intros.
  exact (H x (H0 x)).
Qed.

Lemma Ej314_2 : forall x : U, A x -> ~ (forall x : U, ~ A x).
Proof.
  unfold not.
  intros.
  exact (H0 x H).
Qed.

Lemma Ej314_3 : (forall x : U, P -> A x) -> P -> forall x : U, A x.
Proof.
  intros.
  exact (H x H0).
Qed.

Lemma Ej314_4 : (forall x y : U, R x y) -> forall x : U, R x x.
Proof.
  exact (fun f => (fun (x : U) => f x x)).
Qed.

Lemma Ej314_5 : (forall x y: U, R x y -> R y x)
                -> forall z : U, R e z -> R z e.
Proof.
  exact (fun f z => f e z).
Qed.

End Ejercicio14.