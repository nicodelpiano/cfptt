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

(* Definition isRW (pc : content) : Prop :=
  match pc with
    | RW _ => True
    | _ => False
  end
. *)

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
        
(* Ejercicio 5 *)

(*
  if the hypervisor or a trusted OS is running the
  processor must be in supervisor mode
*)
Definition condicion3 (s : state) : Prop :=
  ((aos_activity s = running /\ (ctxt_oss ctxt) (active_os s) = true)
  \/ aos_activity s = waiting) (* esto es para decir que el hypervisor esta corriendo *)
    -> aos_exec_mode s = svc
.

(*
  the hypervisor maps an OS physical address to a machine address owned by
  that same OS. This mapping is also injective
*)
Definition condicion5 (s : state) : Prop :=
  forall (osi : os_ident) (pa : padd),
    ((hypervisor s) osi >>= (fun hso : padd |-> madd =>
      hso pa >>= (fun ma : madd =>
        (memory s) ma >>= (fun mp : page =>
          page_owned_by mp = Osi osi
    ))))
    /\
    forall (pa2 : padd),
      (hypervisor s) osi >>= (fun hso : padd |-> madd =>
        ~ (hso pa = None madd) /\ hso pa = hso pa2 -> pa = pa2)
.

(*
  all page tables of an OS o
  map accessible virtual addresses to pages owned by o and not accessible ones to
  pages owned by the hypervisor
*)
Definition condicion6 (s : state) : Prop :=
  forall (osi : os_ident),
    (oss s) osi >>= (fun actual_os : os =>
      (hypervisor s) osi >>= (fun hso : padd |-> madd =>
        hso (curr_page actual_os) >>= (fun ma : madd =>
          (memory s) ma >>= (fun mp : page =>
            exists va_to_ma : vadd |-> madd, page_content mp = PT va_to_ma
            /\ forall va : vadd, va_to_ma va >>= (fun ma' : madd =>
                 (memory s) ma' >>= (fun mp' : page =>
                   (ctxt_vadd_accessible ctxt va = true -> page_owned_by mp' = Osi osi)
                   /\ (ctxt_vadd_accessible ctxt va = false -> page_owned_by mp' = Hyp)
    ))))))
.

Definition valid_state (s : state) : Prop :=
  condicion3 s /\ condicion5 s /\ condicion6 s
.

(* Ejercicio 4 *)

Inductive one_step_exec (s : state) (a : action) (s' : state) : Prop :=
  | ose : valid_state s -> Pre s a -> Post s a s' -> one_step_exec s a s'
.

(* Ejercicio 6 *)

Lemma PreservaIII : forall (s s' : state) (a : action), one_step_exec s a s' -> condicion3 s'.
Proof.
  destruct a; intro.
    inversion H.
    inversion H0.
    inversion H2.
    rewrite <- H5.
    trivial.

    inversion H.
    inversion H0.
    inversion H2.
    inversion H1.
    unfold condicion3.
    intro.
    destruct H5 as [_ [_ [AOSE [AOSA [_ [AOS _]]]]]].
    elim H3.
      trivial.

      elim H8; intro.
        left.
        rewrite <- AOSA.
        rewrite <- AOS.
        trivial.

        right.
        rewrite <- AOSA.
        trivial.

    inversion H.
    inversion H0.
    inversion H2.
      inversion H1.
      unfold condicion3.
      intro.
      destruct H5 as [_ [AOSE _]].
      trivial.

      unfold condicion3.
      intro.
      elim H6; intro.
        destruct H7 as [_ CO'].
        destruct H5 as [CO [_ [_ [_ [_ [AOS _]]]]]].
        rewrite AOS in CO'.
        rewrite CO in CO'.
        discriminate.

        destruct H5 as [_ [_ [AOSA _]]].
        rewrite AOSA in H7.
        discriminate.
Qed.

End Actions.