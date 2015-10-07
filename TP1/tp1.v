(* Practica 1 *)

Section P1.
Variables A B C:Prop.

(* Ej 1.1 *)
Theorem e11: A->A.
Proof.
intro.
assumption.
Qed.

(* Ej 1.2 *)
Theorem e12: A->B->A.
Proof.
intros.
assumption.
Qed.

(* Ej 1.3 *)
Theorem e13: (A->(B->C))->(A->B)->(A->C).
Proof.
intros.
apply H.
assumption.
apply H0.
assumption.
Qed.

(*Ej 2.1 *)
Theorem e21: (A->B)->(B->C)->A->C.
Proof.
intros.
apply H0.
apply H.
assumption.
Qed.

(*Ej 2.2 *)
Theorem e22: (A->B->C)->B->A->C.
Proof.
intros.
apply H;assumption.
Qed.

(*Ej 3.1 *)
Theorem e31: A->A->A.
Proof.
intros.
exact H.
Qed.

(*Ej 3.1 b *)
Theorem e31b: A->A->A.
Proof.
intros.
exact H0.
Qed.

(* Ej 3.2 *)
Theorem e32: (A->B->C)->A->(A->C)->B->C.
Proof.
intros.
apply H;assumption.
Qed.

(* Ej 3.2b *)
Theorem e32b: (A->B->C)->A->(A->C)->B->C.
Proof.
intros.
exact (H H0 H2).
Qed.

(* Ej 4.1 *)
Theorem e41: A -> ~~A.
Proof.
unfold not.
intros.
exact (H0 H).
Qed.

(* Ej 4.2 *)
Theorem e42: A -> B -> (A /\ B).
Proof.
intros.
split;assumption.
Qed.

(* Ej 4.3 *)
Theorem e43: (A->B->C) -> (A/\B->C).
Proof.
intros.
elim H0.
assumption.
Qed.

(* Ej 4.4 *)
Theorem e44: A->(A\/B).
Proof.
left.
assumption.
Qed.

(* Ej 4.5 *)
Theorem e45: B->(A\/B).
Proof.
right.
assumption.
Qed.

(* Ej 4.6 *)
Theorem e46: (A \/ B) -> (B \/ A).
Proof.
intro.
elim H; intro.
  right.
  assumption.

  left.
  assumption.
Qed.

(* Ej 4.7 *)
Theorem e47: (A->C)->(B->C)->A\/B->C.
Proof.
intros.
elim H1; assumption.
Qed.

(* Ej 4.8 *)
Theorem e48: False->A.
Proof.
intro.
elim H.
Qed.

(* Ej 5.1 *)
Theorem e51: (A->B)-> ~B-> ~A.
Proof.
intros.
unfold not.
intro.
absurd B.
  assumption.

  exact (H H1).
Qed.

(* Ej 5.2 *)
Theorem e52: ~(A/\~A).
Proof.
unfold not.
intro.
elim H.
intros.
exact (H1 H0).
Qed.

(* Ej 5.3 *)
Theorem e53: (A->B)-> ~(A/\~B).
Proof.
unfold not.
intros.
absurd B.
  unfold not.
  apply H0.

  apply H.
  apply H0.
Qed.

(* Ej 5.4 *)
Theorem e54: (A/\B)->~(A->~B).
Proof.
intro.
unfold not.
intro.
apply H0; apply H.
Qed.

(* Ej 5.5 *)
Theorem e55: (~A /\ ~~A) -> False.
Proof.
intro.
apply H.
apply H.
Qed.

(* Ej 6.1 *)
Theorem e61: (A\/B) -> ~(~A/\~B).
Proof.
unfold not.
intros.
elim H0.
intros.
elim H; assumption.
Qed.

(* Ej 6.2 *)
Theorem e62: A\/B <-> B\/A.
Proof.
split; intro; elim H; intro;[right | left | right | left];assumption.
Qed.

(* Ej 6.3 *)
Theorem e63: A\/B -> ((A->B)->B).
Proof.
intros.
elim H; intro;[exact (H0 H1) | assumption].
Qed.

End P1.

Section Logica_Clasica.
Variables A B C: Prop.

(* Ej 7.1 *)
Theorem e71: A \/ ~A -> ~~A->A.
Proof.
intros.
elim H; intro; [|absurd (~A)];assumption.
Qed.

(* Ej 7.2 *)
Theorem e72: A\/~A -> ((A->B) \/ (B->A)).
Proof.
intros.
elim H; intro.
  right.
  intro.
  assumption.

  left.
  intro.
  absurd A; assumption.
Qed.

(* Ej 7.3 *)
Theorem e73: (A \/ ~A) -> ~(A /\ B) -> ~A \/ ~B.
Proof.
unfold not.
intros.
elim H; intro.
  right.
  intro.
  apply H0.
  split; assumption.

  left.
  assumption.

Qed.

Require Import Classical.
Check classic.

(* Ej 8.1 *)
Theorem e81: ~~A->A.
Proof.
intro.
elim (classic A); intro; [|elim H];assumption.
Qed.

(* Ej 8.2 *)
Theorem e82: (A->B)\/(B ->A).
Proof.
elim (classic A); intro.
  right.
  intro.
  assumption.

  left.
  intro.
  elim H.
  assumption.
Qed.

(* Ej 8.3 *)
Theorem e83: ~(A/\B)-> ~A \/ ~B.
Proof.
unfold not.
intro.
elim (classic A); intro.
  right.
  intro.
  apply H.
  split; assumption.

  left.
  intro.
  elim H0.
  assumption.
Qed.

End Logica_Clasica.

Section ejercicio11.

(* Ej 11 *)
(* Definiciones *)
Variable PF:Prop. (*el paciente tiene fiebre*)
Variable PA:Prop. (*el paciente tiene piel amarillenta*)
Variable PH:Prop. (*el paciente tiene hepatitis*)
Variable PR:Prop. (*el paciente tiene rubeola*)

Hypothesis Regla1: PF \/ PA -> PH \/ PR.
Hypothesis Regla2: PR -> PF.
Hypothesis Regla3: PH /\ ~PR -> PA.

Theorem ej11: (~PA /\ PF) -> PR.
Proof.
intro.
elim H.
intros.
elim (classic PR); intro.
  assumption.

  elim Regla1; [intro; elim H0; apply Regla3; split | intro | left]; assumption.
Qed.

End ejercicio11.