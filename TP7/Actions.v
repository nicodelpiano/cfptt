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
        (memory s) actual_ma >>= (fun mp : page =>
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
Definition condicionVI (s : state) : Prop :=
  forall (osi : os_ident) (ma : madd),
    (memory s) ma >>= (fun mp : page => page_owned_by mp = Osi osi ->
      exists vama : vadd |-> madd, page_content mp = PT vama ->
        forall va : vadd, vama va >>= (fun ma' : madd =>
          (memory s) ma' >>= (fun mp' : page => 
            (ctxt_vadd_accessible ctxt va = true -> page_owned_by mp' = Osi osi)
            /\ (ctxt_vadd_accessible ctxt va = false -> page_owned_by mp' = Hyp)
    )))
.

Definition condicionVI' (s : state) : Prop :=
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

Definition assert1 (s : state) : Prop :=
  oss s (active_os s) >>=
     (fun actual_os : os =>
      hypervisor s (active_os s) >>=
      (fun hso : padd |-> madd =>
       hso (curr_page actual_os) >>=
       (fun ma : madd =>
        memory s ma >>=
        (fun mp : page =>
         exists va_to_ma : vadd |-> madd,
           page_content mp = PT va_to_ma /\
           (forall va0 : vadd,
            va_to_ma va0 >>=
            (fun ma' : madd =>
             memory s ma' >>=
             (fun mp' : page =>
              (ctxt_vadd_accessible ctxt va0 = true ->
               page_owned_by mp' = Osi (active_os s)) /\
              (ctxt_vadd_accessible ctxt va0 = false ->
               page_owned_by mp' = Hyp))))))))
.

Definition assert2 (s : state) (x0 : vadd |-> madd) (va : vadd) : Prop :=
  match x0 va with
      | Some x0 =>
          match memory s x0 with
          | Some x1 =>
              (ctxt_vadd_accessible ctxt va = true ->
               page_owned_by x1 = Osi (active_os s)) /\
              (ctxt_vadd_accessible ctxt va = false ->
               page_owned_by x1 = Hyp)
          | None => False
          end
      | None => False
      end
.

Lemma Read_Isolation : forall (s s' : state) (va : vadd),
  one_step_exec s (read va) s' ->
    exists (ma : madd), va_mapped_to_ma s va ma /\
      (memory s) ma >>= (fun pg : page => page_owned_by pg = Osi (active_os s)).
Proof.
  intros.
  inversion_clear H.
  destruct H0 as [C1 [C2 C3]].
  destruct H1 as [CT [AOS EMA]].
  inversion H2; clear H2.
  destruct EMA as [MA [VtoM ISRW]].
  exists MA.
  rewrite <- H.
  split.
    trivial.

    unfold bindapp.
    unfold va_mapped_to_ma, bindapp in VtoM.
    case_eq (oss s (active_os s)); intros.
      rewrite H0 in VtoM.
      case_eq (hypervisor s (active_os s)); intros.
        rewrite H1 in VtoM.
        case_eq (p (curr_page o)); intros.
          rewrite H2 in VtoM.
          case_eq (memory s m); intros.
            rewrite H3 in VtoM.
            destruct VtoM as [x []].
            case_eq (x va); intros.
              rewrite H6 in H5.
              unfold condicionVI in C3.
              assert (assert1 s) by exact (C3 (active_os s)); clear C3; unfold assert1 in H7.
              unfold bindapp in H7.
              rewrite H0,H1,H2,H3 in H7.
              elim H7; intros; clear H7.
              elim H8; intros; clear H8.
              assert (assert2 s x0 va) by exact (H9 va); unfold assert2 in H8; clear H9.
                rewrite H4 in H7.
                injection H7; intro.
                rewrite <- H9, H6 in H8.
                rewrite <- H5.
                  case_eq (memory s m0); intros.
                  rewrite H10 in H8.
                  destruct H8.
                  exact (H8 CT).

                  rewrite H10 in H8; trivial.

            rewrite H6 in H5; contradiction.

          rewrite H3 in VtoM; contradiction.

        rewrite H2 in VtoM; contradiction.

      rewrite H1 in VtoM; contradiction.

    rewrite H0 in VtoM; contradiction.
Qed.

End Actions.