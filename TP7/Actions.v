(*******************************************************************
 * Este archivo especifica las acciones
 * (Como transformadores de estado)
 ******************************************************************)

Require Import State.

Section Actions.

(* Contexto global *)
Parameter ctxt : context.

(* Ejercicio 2 *)

Inductive action : Set :=
  | read : vadd -> action
  | write : vadd -> value -> action
  | chmod : action
.

(* Ejercicio 3 *)

(* 'va_mapped_to_ma' expresa que la dirección virtual 'va' esta mapeada
   en la memoria a una direccion de maquina 'ma' para un OS en un estado dado
*)
Definition va_mapped_to_ma (s : state) (va : vadd) (ma : madd) : Prop :=
  
.

Definition isRW () : Prop :=
  
.


End Actions.