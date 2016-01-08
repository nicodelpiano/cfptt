(*******************************************************************
 * Este archivo especifica las acciones
 * (Como transformadores de estado)
 ******************************************************************)

Require Import State.
Require Import Maps.

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

(* 
  'va_mapped_to_ma' expresa que la dirección virtual 'va' esta mapeada
   en la memoria a una direccion de maquina 'ma' para un OS en un estado dado
*)
Definition va_mapped_to_ma (s : state) (va : vadd) (ma : madd) : Prop :=
  (oss s) (active_os s) >>= (fun actual_os : os =>
    (hypervisor s) (active_os s) >>= (fun map_p_to_m : padd |-> madd =>
      map_p_to_m (curr_page actual_os) >>= (fun actual_ma : madd =>
        (memory s) ma >>= (fun mp : page =>
          exists map_v_to_m : vadd |-> madd,
            page_content mp = PT map_v_to_m /\
              map_v_to_m va >>= (fun ma' : madd => ma' = ma)
  ))))
.

Definition isRW (s : state) (ma : madd) : Prop :=
  (memory s) ma >>= (fun mp : page =>
    exists ov : option value, page_content mp = RW ov
  )
.

(* 
  The precondition of the action read va requires that va is accessible by the active OS,
  that there exists a machine address ma to which va is mapped,
  that the active OS is running and that the page indexed by the machine address ma is readable/writable.
*)
Definition Pre (s : state) (a : action) : Prop :=
  match a with
    | read va =>
      (ctxt_vadd_accessible ctxt) va = true
      /\ aos_activity s = running
      /\ exists ma : madd, va_mapped_to_ma s va ma
        /\ isRW s ma
    | write va val =>
      (ctxt_vadd_accessible ctxt) va = true
      /\ aos_activity s = running
      /\ exists ma : madd, va_mapped_to_ma s va ma
        /\ isRW s ma
    | chmod =>
      aos_activity s = waiting
      /\ (oss s) (active_os s) >>= (fun res : os => hcall res = None Hyperv_call)
  end
.

Definition Post (s : state) (a : action) (s' : state) :=
  match a with
    | read _ => s = s'
    | write va val =>
      exists ma : madd, va_mapped_to_ma s va ma
      /\ memory s' = update_partial (memory s) madd_eq ma (Page (RW (Some val)) (Osi (active_os s)))
      /\ aos_exec_mode s' = aos_exec_mode s
      /\ aos_activity s' = aos_activity s
      /\ oss s' = oss s
      /\ active_os s' = active_os s
      /\ hypervisor s' = hypervisor s
    | chmod =>
      ((ctxt_oss ctxt) (active_os s) = true
        /\ aos_exec_mode s' = svc
        /\ aos_activity s' = running
        /\ memory s' = memory s
        /\ oss s' = oss s
        /\ active_os s' = active_os s
        /\ hypervisor s' = hypervisor s
      )
      \/
      ((ctxt_oss ctxt) (active_os s) = false
        /\ aos_exec_mode s' = usr
        /\ aos_activity s' = running
        /\ memory s' = memory s
        /\ oss s' = oss s
        /\ active_os s' = active_os s
        /\ hypervisor s' = hypervisor s
      )
  end
.
        




End Actions.