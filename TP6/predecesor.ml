type nat =
| O
| S of nat

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

(** val predspec : nat -> nat **)

let predspec = function
| O -> O
| S n0 -> n0

