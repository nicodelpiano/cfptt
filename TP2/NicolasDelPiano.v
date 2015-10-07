Section Ejercicio3.

Variable U   : Set.
Variable A B : U -> Prop.
Variable P Q : Prop.
Variable R S : U -> U -> Prop.

Hypothesis H1: forall x:U, (R x x).
Hypothesis H2: forall x y z:U, (R x y) /\ (R x z) -> (R y z).

Theorem reflexiva: forall x : U, R x x.
Proof.
auto.
Qed.

Theorem simetrica: forall x y : U, R x y -> R y x.
Proof.
intros.
apply (H2 x y x).
split; [ assumption | trivial ].
Qed.

Theorem transitiva: forall x y z : U, R x y /\ R y z -> R x z.
Proof.
intros.
apply (H2 y x z).
split; [ apply simetrica | idtac ]; elim H; auto.
Qed.

End Ejercicio3.

Section Ejercicio5.

Variable nat      : Set.
Variable S        : nat -> nat.
Variable a b c    : nat.
Variable odd even : nat -> Prop.
Variable P Q      : nat -> Prop.
Variable f        : nat -> nat.

Theorem e51: forall x:nat, exists y:nat, (P(x)->P(y)).
Proof.
intros.
exists x.
trivial.
Qed.

Theorem e52: exists x:nat, (P x)
                            -> (forall y:nat, (P y)->(Q y))
                               -> (exists z:nat, (Q z)).
Proof.
exists a.
intros.
exists a.
apply ((H0 a) H).
Qed.

Theorem e53: even(a) -> (forall x:nat, (even(x)->odd (S(x)))) -> exists y: nat, odd(y).
Proof.
intros.
exists (S a).
apply ((H0 a) H).
Qed.


Theorem e54: (forall x:nat, P(x) /\ odd(x) ->even(f(x)))
                            -> (forall x:nat, even(x)->odd(S(x)))
                            -> even(a)
                            -> P(S(a))
                            -> exists z:nat, even(f(z)).
Proof.
intros.
exists (S a).
apply (H (S a)).
split; [ idtac | apply (H0 a)]; assumption.
Qed.

End Ejercicio5.

Section Ejercicio7.

Variable U   : Set.
Variable A B : U -> Prop.

Theorem e71: (forall x:U, ((A x) /\ (B x)))
                       -> (forall x:U, (A x)) /\ (forall x:U, (B x)).
Proof.
intro; split; intro num; apply (H num).
Qed.

Theorem e72: (exists x:U, (A x \/ B x))->(exists x:U, A x )\/(exists x:U, B x).
Proof. 
intro; elim H; intros; elim H0; intro; [left | right]; exists x; assumption.
Qed.

End Ejercicio7.

Section Ejercicio8.

Variable U  : Set.

Variable R : U -> U -> Prop.
Variable T : U -> Prop.
Variable V : U -> Prop.

Theorem ej8_1 : (exists y : U, forall x : U, R x y) -> (forall x : U, exists y : U, R x y).
Proof.
intros.
elim H.
intros.
exists x0.
apply (H0 x).
Qed.

Theorem ej8_2: (exists y:U, True)/\(forall x:U, (T x) \/ (V x)) ->  
(exists z:U, (T z)) \/ (exists w:U, (V w)).
Proof.
intros.
apply e72.
elim H.
intros.
elim H0.
intros.
exists x.
trivial.
Qed.


(**
  Ejercicio 2.8.3
  La condicion (exists y:U, True) es necesaria ya que se necesita proveer
  un testigo de U para poder probar la existencia de al menos un elemento
  que cumpla T o V.
  En la siguiente demostración pruebo que (exists y:U, True) es condición necesaria
  para demostrar el teorema de arriba.
**)
Theorem ej8_3: (exists z:U, (T z)) \/ (exists w:U, (V w)) -> (exists y:U, True).
Proof.
intros.
elim H; intro; elim H0; intros; exists x; trivial.
Qed.

End Ejercicio8.

Section Ejercicio9.
Require Import Classical.
Variables U : Set.
Variables A : U -> Prop.

Lemma not_ex_not_forall: (~exists x :U, ~A x) -> (forall x:U, A x).
Proof.
unfold not.
intros.
elim (classic (A x));intro; [ | elim H; exists x ]; assumption.
Qed.

Lemma not_forall_ex_not: (~forall x :U, A x) -> (exists x:U,  ~A x).
Proof.
unfold not.
intros.
elim (classic (exists x : U, not (A x))); [ trivial | intro ].
assert (forall x:U, A x); [ apply not_ex_not_forall | elim H ]; assumption.
Qed.

End Ejercicio9.

Section Ejercicio10y11.

Variable nat : Set.
Variable  O  : nat.
Variable  S  : nat -> nat.

Axiom disc   : forall n:nat, ~O=(S n).
Axiom inj    : forall n m:nat, (S n)=(S m) -> n=m.

Variable sum prod : nat->nat->nat.
Axiom sum0   : forall n :nat, (sum n O)=n.
Axiom sumS   : forall n m :nat, (sum n (S m))=(S (sum n m)).
Axiom prod0  : forall n :nat, (prod n O)=O.
Axiom prodS  : forall n m :nat, (prod n (S m))=(sum n (prod n m)).


Lemma L10_1: (sum (S O) (S O)) = (S (S O)).
Proof.
rewrite sumS.
rewrite sum0.
reflexivity.
Qed.

Lemma L10_2: forall n :nat, ~(O=n /\ (exists m :nat, n = (S m))).
Proof.
unfold not.
intros.
elim H.
intros.
elim H1.
rewrite <- H0.
apply disc.
Qed.

Lemma prod_neutro: forall n :nat, (prod n (S O)) = n.
Proof.
intros.
rewrite prodS.
rewrite prod0.
apply sum0.
Qed.

Lemma diff: forall n:nat, ~(S (S n))=(S O).
Proof.
unfold not.
intros.
cut (O = S n); [ apply disc | symmetry; apply inj; assumption ].
Qed.

Axiom induccion: forall (P : nat -> Prop) , P O -> (forall x , P
x -> P (S x)) -> forall x , P x .

Variable le : nat->nat->Prop.
Axiom leinv: forall n m:nat, (le n m) -> n=O \/
      (exists p:nat, (exists q:nat, n=(S p)/\ m=(S q) /\ (le p q))).

Lemma notle_s_o: forall n:nat, ~(le (S n) O).
Proof.
unfold not.
intros.
elim (leinv (S n) O); intros;
  [ apply (disc n); auto
  | elim H0;
    intros;
    elim H1;
    intros;
    elim H2;
    elim (disc x0);
    elim H2;
    intros;
    elim H4;
    trivial
  | assumption].
Qed.

End Ejercicio10y11.