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
  exists actual_os : os, (oss s) (active_os s) = Some actual_os /\
    exists pa_to_ma : padd |-> madd, (hypervisor s) (active_os s) = Some pa_to_ma /\
      exists ma' : madd, pa_to_ma (curr_page actual_os) = Some ma' /\
        exists mp : page, (memory s) ma' = Some mp /\
          exists va_to_ma : vadd |-> madd, page_content mp = PT va_to_ma /\
            va_to_ma va = Some ma
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
        
(* Ejercicio 5 *)

(*
  if the hypervisor or a trusted OS is running the
  processor must be in supervisor mode
*)
Definition condicionIII (s : state) : Prop :=
  ((aos_activity s = running /\ (ctxt_oss ctxt) (active_os s) = true)
  \/ aos_activity s = waiting) (* esto es para decir que el hypervisor esta corriendo *)
    -> aos_exec_mode s = svc
.

(*
  the hypervisor maps an OS physical address to a machine address owned by
  that same OS. This mapping is also injective
*)
Definition condicionV (s : state) : Prop :=
  forall (osi : os_ident) (pa : padd) (pa_to_ma : padd |-> madd),
    ((hypervisor s) osi = Some pa_to_ma
    -> (exists ma : madd, pa_to_ma pa = Some ma
       /\ (exists mp : page, (memory s) ma = Some mp /\ page_owned_by mp = Osi osi)))
    /\ forall (pa2 : padd),
       pa_to_ma pa = pa_to_ma pa2 -> pa = pa2
.

(*
  all page tables of an OS o
  map accessible virtual addresses to pages owned by o and not accessible ones to
  pages owned by the hypervisor
*)
Definition condicionVI (s : state) : Prop :=
  forall (osi : os_ident) (mp : page) (va_to_ma : vadd |-> madd) (va : vadd),
    page_owned_by mp = Osi osi
    /\ page_content mp = PT va_to_ma
    /\ (exists ma : madd, (memory s) ma = Some mp)
    -> (exists ma' : madd, va_to_ma va = Some ma'
                           /\ (exists mp' : page, (memory s) ma' = Some mp'
                              /\ (ctxt_vadd_accessible ctxt va = true -> page_owned_by mp' = Osi osi)
                              /\ (ctxt_vadd_accessible ctxt va = false -> page_owned_by mp' = Hyp)
   ))
.

Definition valid_state (s : state) : Prop :=
  condicionIII s /\ condicionV s /\ condicionVI s
.

(* Ejercicio 4 *)

Inductive one_step_exec (s : state) (a : action) (s' : state) : Prop :=
  | ose : valid_state s -> Pre s a -> Post s a s' -> one_step_exec s a s'
.

(* Ejercicio 6 *)

Lemma PreservaIII : forall (s s' : state) (a : action), one_step_exec s a s' -> condicionIII s'.
Proof.
  destruct a; intro; inversion H; inversion H0; inversion H1;
  [ inversion H2;
    rewrite <- H7;
    trivial
  |
    inversion H2;
    unfold condicionIII;
    intro;
    destruct H7 as [_ [_ [AOSE [AOSA [_ [AOS _]]]]]];
    elim H3;
    [ | elim H8; rewrite <- AOSA;
      [ left; rewrite <- AOS | right ]
    ]; trivial
   |
    inversion H2; unfold condicionIII; intro; destruct H7 as [CO [AOSE [AOSA [_ [_ [AOS _]]]]]];
    [ trivial
      | elim H8; intro;
      [ destruct H7 as [_ CO']; rewrite AOS in CO'; rewrite CO in CO'
        | rewrite AOSA in H7
        ]; discriminate
    ]
  ].
Qed.

(* Ejercicio 7 *)

Lemma Read_Isolation : forall (s s' : state) (va : vadd),
  one_step_exec s (read va) s'
    -> exists ma : madd, va_mapped_to_ma s va ma
       /\ exists pg : page,
           (memory s) ma = Some pg /\ page_owned_by pg = Osi (active_os s)
.
Proof.
  intros.
  do 2 destruct H.
  destruct H2.
  destruct H0 as [VA_ACC [AOSA EMA]].
  elim EMA.
  intros.
  destruct H0.
  exists x.
  split.
    trivial.

    unfold va_mapped_to_ma in H0.
    destruct H0 as [actual_os [AOs [pa_to_ma [PaMa [ma' [MA' [mp [MP [va_to_ma [VTM VTM2]]]]]]]]]].

    unfold condicionV in H2.
    destruct (H2 (active_os s) (curr_page actual_os) pa_to_ma); clear H2.
    assert (     exists ma : madd,
       pa_to_ma (curr_page actual_os) = Some ma /\
       (exists mp0 : page,
          memory s ma = Some mp0 /\ page_owned_by mp0 = Osi (active_os s))) by exact (H0 PaMa); clear H0.
    destruct H2 as [ma [PaMa' [mp0 [MP0 MP1]]]].

    rewrite MA' in PaMa'.
    injection PaMa'; intro; clear PaMa'.

    rewrite H0 in MP.
    rewrite MP in MP0.
    injection MP0; intro; clear MP0.
    rewrite <- H2 in MP1.

    unfold condicionVI in H3.
    destruct (H3 (active_os s) mp va_to_ma va).
    split; [ | split];trivial.
    exists ma.
    trivial.
    
    destruct H6.
    elim H7; intros.
    destruct H8.
    destruct H9.
    rewrite H6 in VTM2.
    injection VTM2; intro; clear VTM2.
    rewrite <- H11.
    exists x1.
    split; [trivial | apply (H9 VA_ACC)].
Qed.

End Actions.