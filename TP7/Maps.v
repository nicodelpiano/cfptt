Section Maps.

(* Tipo option *)
Inductive option (T : Type) : Type :=
  | Some : T -> option T
  | None : option T
.

(* Defino el tipo y notacion de las funciones parciales *)
Definition partial (A B : Set) := A -> option B.

End Maps.

Infix "|->" := partial (at level 62, left associativity) : maps_scope.