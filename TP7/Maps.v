Set Implicit Arguments.

Section Maps.

(* Tipo option *)
Inductive option (T : Type) : Type :=
  | Some : T -> option T
  | None : option T
.

(* Defino el tipo y notacion de las funciones parciales *)
Definition partial (A B : Set) := A -> option B.

(* "Bind" para option, con la salvedad que retorna el valor 'False' en caso de
  contener un None alguno de sus terminos, lo cual corta la computacion *)
Function bindapp (A : Set) (el : option A) (f : A -> Prop) : Prop :=
  match el with
    | None => False
    | Some x => f x
  end
.

Function update_partial (A B : Set) (p : partial A B)
  (a_eq : forall pa1 pa2 : A, {pa1 = pa2} + {pa1 <> pa2}) (a : A) (b : B) : partial A B :=
    fun (x : A) => if a_eq x a then Some b else p x
.

End Maps.

Infix "|->" := partial (at level 62, left associativity) : maps_scope.
Infix ">>=" := bindapp (at level 62, left associativity) : maps_scope.
(* Notation "m '[' a ']'" := (m a) (at level 62) : maps_scope. *)