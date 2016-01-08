(*******************************************************************
 * Este archivo especifica el estado.
 * 
 ******************************************************************)

Require Import Maps.
Open Scope maps_scope.

Section State.

(** Identificadores de OSs e Hypercalls *)

Parameter os_ident : Set.
Parameter os_ident_eq : forall oi1 oi2 : os_ident, {oi1 = oi2} + {oi1 <> oi2}.

Parameter Hyperv_call: Set.

(* Memoria y direcciones *)

(* Direcciones Virtuales. *)
Parameter vadd: Set.
Parameter vadd_eq : forall va1 va2 : vadd, {va1 = va2} + {va1 <> va2}.

(** Direcciones de Máquina. *)
Parameter madd :  Set.
Parameter madd_eq : forall ma1 ma2 : madd, {ma1 = ma2} + {ma1 <> ma2}.

(** Direcciones Físicas : 
Los sitemas operativos utilizan este tipo de direcciones para ver regiones de memoriea
contigua. Estos no ven direcciones de máquina. *)
Parameter padd: Set.
Parameter padd_eq : forall pa1 pa2 : padd, {pa1 = pa2} + {pa1 <> pa2}.

(** Memory values. *)
Parameter value: Set.
Parameter value_eq:forall val1 val2 : value, {val1 = val2} + {val1 <> val2}.


(* Environment *)
Record context : Set :=
  Context
    {(** una dirección virtual es accesible, i.e. no está reserveda 
         por el Hypervisor *)
       ctxt_vadd_accessible: vadd -> bool;
     (** guest Oss (Confiable/No Confiable) **)
       ctxt_oss : os_ident -> bool
    }.

(* Ejercicio 1 *)

(** Formalizing States *)

(* Operating systems *)
Record os : Set :=
  Os
    {
      curr_page : padd;
      hcall : option Hyperv_call
    }
.

Definition oss_map := os_ident |-> os.

(* Execution modes *)
Inductive exec_mode : Set :=
  | usr : exec_mode
  | svc : exec_mode
.

Inductive os_activity : Set :=
  | running : os_activity
  | waiting : os_activity
.

(* Memory mappings *)

(* Page *)
Inductive content : Set :=
  | RW : option value -> content
  | PT : (vadd |-> madd) -> content
  | Other : content
.

Inductive page_owner : Set :=
  | Hyp : page_owner
  | Osi : os_ident -> page_owner
  | No_Owner : page_owner
.

Record page : Set :=
  Page
    {
      page_content : content;
      page_owned_by : page_owner
    }
.

Definition hypervisor_map := os_ident |-> (padd |-> madd).

Definition system_memory := madd |-> page.

(* States *)

Record state : Set :=
  State
    {
      active_os : os_ident; (* which is the active operating system *)
      aos_exec_mode : exec_mode; (* corresponding execution mode *)
      aos_activity : os_activity; (* corresponding processor mode *)
      oss : oss_map; (* stores the information of the guest operating systems of the
platform *)
      hypervisor : hypervisor_map; (* formalizes the memory model *)
      memory : system_memory (* formalizes the memory model *)
    }
.

End State.