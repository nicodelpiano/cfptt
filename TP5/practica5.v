Section Ejercicio1.

Inductive list (A : Set) : Set :=
  | nil : list A
  | cons : A -> list A -> list A.

Inductive LE : nat -> nat -> Prop := 
  | Le_O : forall n : nat, LE 0 n 
  | Le_S : forall n m : nat, LE n m -> LE (S n) (S 
m).

Inductive Mem (A : Set) (a : A) : list A -> Prop :=
  | here : forall x : list A, Mem A a (cons A a x) 
  | there : forall x : list A, Mem A a x ->  
forall b : A, Mem A a (cons A b x).

(* 1.1 *)
Theorem not_sn_le_o: forall n:nat, ~ LE (S n) O.
Proof.
  unfold not.
  intros.
  inversion H.
Qed.

(* 1.2 *)
Theorem nil_empty (A:Set): forall a:A, ~ Mem A a (nil A).
Proof.
  unfold not.
  intros.
  inversion H.
Qed.

(* 1.3 *)
Theorem e13: ~ LE 4 3.
Proof.
  unfold not.
  intro.
  repeat (inversion_clear H; inversion_clear H0).
Qed.

(* 1.4 *)
Theorem e14: forall n:nat, ~ LE (S n) n.
Proof.
  unfold not.
  intros.
  induction n;
  inversion H;
  exact (IHn H2).
Qed.

(* 1.5 *)
Theorem e15: forall n m p:nat,
  LE n m /\ LE m p -> LE n p.
Proof.
  induction n.
  intros.
    constructor.

    intros.
    destruct H.
    inversion H0.
    rewrite <- H1 in H.
    apply not_sn_le_o in H.
    contradiction.

    constructor.
    rewrite <- H2 in H.
    inversion H.
    apply (IHn n0 m0).
    split; trivial.
Qed.

(* 5.6 *)

End Ejercicio1.

Section Ejercicio3.

Variable A : Set.
Parameter equal : A -> A -> bool.

Axiom equal1 : forall x y : A, equal x y = true -> 
x = y.
Axiom equal2 : forall x : A, equal x x <> false.

Inductive List : Set :=
  | nullL : List
  | consL : A -> List -> List.

Inductive MemL (a : A) : List -> Prop :=
  | hereL : forall x : List, MemL a (consL a x)
  | thereL : forall x : List, MemL a x -> forall b
: A, MemL a (consL b x).

(* 3.1 *)
Inductive isSet : List -> Prop :=
  | isSetNil : isSet nullL
  | isSetCons : forall (x : A) (l : List),
    ~MemL x l /\ isSet l -> isSet (consL x l).

(* 3.2 *)
Fixpoint deleteAll (x : A) (xs : List) : List :=
  match xs with
    | nullL => xs
    | consL y ys =>
      if equal x y
      then deleteAll x ys
      else consL y (deleteAll x ys)
  end.

(* 3.3 *)
Lemma DeleteAllNotMember : forall (l : List) (x : A),
   ~ MemL x (deleteAll x l).
Proof.
  unfold not.
  intros.
  induction l;
    inversion H;
    simpl in H;
    remember (equal x a) as y;
    destruct y;
    [ exact (IHl H)
    | injection H1;
      intros;
      symmetry in Heqy;
      rewrite H2 in Heqy;
      apply equal2 in Heqy;
      trivial
    | exact (IHl H)
    | injection H0;
      intros;
      rewrite <- H2 in IHl;
      exact (IHl H1) 
    ].
Qed.

(* 3.4 *)
Fixpoint delete (x : A) (xs : List) : List :=
  match xs with
    nullL => nullL
    | consL y ys =>
      if equal x y then ys
      else consL y (delete x ys)
  end.

Lemma setCons : forall (l : List) (x : A),
  isSet (consL x l) -> isSet l.
Proof.
  intros.
  induction l.
    apply isSetNil.

    inversion H.
    destruct H1.
    trivial.
Qed.

(* 3.5 *)
Lemma DeleteNotMember : forall (l : List) (x : A), 
isSet l -> ~ MemL x (delete x l).
Proof.
  unfold not.
  intros.
  induction l.
    inversion H0.

    simpl in H0.
    remember (equal x a) as y.
    destruct y.
    symmetry in Heqy.
    apply equal1 in Heqy.
    inversion H.
    destruct H2.
    rewrite <- Heqy in H2.
    contradiction.

    inversion H0;
    [ symmetry in Heqy;
      rewrite H2 in Heqy;
      apply equal2 in Heqy
    | apply setCons in H; apply IHl]; trivial.
Qed.

End Ejercicio3.

Section Ejercicio4.

Variable A : Set.

Inductive AB : Set :=
   nullAB : AB
   | consAB : A -> AB -> AB -> AB.

(* 4.a *)
Inductive Pertenece : A -> AB -> Prop :=
  pertNullAB : forall (x : A) (t1 t2 : AB),
    Pertenece x (consAB x t1 t2)
  | pertConsABLeft : forall (x y: A) (t1 t2 : AB),
    Pertenece x t1 -> Pertenece x (consAB y t1 t2)
  | pertConsABRight : forall (x y: A) (t1 t2 : AB),
    Pertenece x t2 -> Pertenece x (consAB y t1 t2).

(* 4.b *)
Parameter eqGen: A -> A -> bool.

Fixpoint Borrar (ab : AB) (x : A) : AB :=
  match ab with
    nullAB => nullAB
    | consAB y lt rt =>
      if eqGen x y then nullAB
      else consAB y (Borrar lt x) (Borrar rt x)
  end.

(* 4.c *)
Axiom eqGen1 : forall x : A, ~ (eqGen x x) = false. 
(*(negb (eqGen x x)) = false.*)

Lemma e4cAux : forall (t1 t2 : AB) (a b : A),
  ~ (Pertenece a t1) ->
  ~ (Pertenece a t2) ->
  eqGen a b = false ->
  Pertenece a (consAB b t1 t2) -> False.
Proof.
  unfold not.
  intros.
  inversion H2;
  [ rewrite H5 in H1;
    apply eqGen1 in H1;
    trivial
  | exact (H H5)
  | exact (H0 H5) ].
Qed.

Lemma BorrarNoPertenece: forall (x : AB) (a : A),
  ~(Pertenece a (Borrar x a)).
Proof.
  unfold not.
  intros.
  induction x;
  [ inversion H
  | simpl in H;
    remember (eqGen a a0) as y;
    destruct y;
      [ inversion H
      | symmetry in Heqy;
        apply (e4cAux (Borrar x1 a) (Borrar x2 a) a a0)
      ]; trivial].
Qed. 

(* 4.d *)
Inductive SinRepetidos : AB -> Prop :=
  nullABNoRep : SinRepetidos nullAB
  | consABNoRep : forall (a : A) (t1 t2 : AB),
    (SinRepetidos t1
    /\ SinRepetidos t2
    /\ (forall (x : A), Pertenece x t1 -> ~ Pertenece x t2)
    /\ (forall (x : A), Pertenece x t2 -> ~ Pertenece x t1)
    /\ ~ Pertenece a t1
    /\ ~ Pertenece a t2)
    -> SinRepetidos (consAB a t1 t2).

End Ejercicio4.

Section Ejercicio5.

(* 5.1 *)
Definition Var : Set := nat.

Inductive BoolExpr : Set :=
  BoolVar : Var -> BoolExpr
  | Bool : bool -> BoolExpr
  | Or : BoolExpr -> BoolExpr -> BoolExpr
  | Not : BoolExpr -> BoolExpr.

(* 5.2 *)
Definition Valor : Set := bool.

Definition Memoria : Set := Var -> Valor.

Definition lookup : Memoria -> Var -> Valor :=
  fun f v => f v.

Inductive BEval : BoolExpr -> Memoria -> bool -> Prop :=
  | evar : forall (v : Var) (m : Memoria),
      BEval (BoolVar v) m (lookup m v)
  | eboolt : forall (m : Memoria),
      BEval (Bool true) m true
  | eboolf : forall (m : Memoria),
      BEval (Bool false) m false
  | eorl : forall (e1 e2 : BoolExpr) (m : Memoria),
      BEval e1 m true -> BEval (Or e1 e2) m true
  | eorr : forall (e1 e2 : BoolExpr) (m : Memoria),
      BEval e2 m true -> BEval (Or e1 e2) m true
  | eorrl : forall (e1 e2 : BoolExpr) (m : Memoria),
      BEval e1 m false -> BEval e2 m false
      -> BEval (Or e1 e2) m false
  | enott : forall (e : BoolExpr) (m : Memoria),
      BEval e m true -> BEval (Not e) m false
  | enotf : forall (e : BoolExpr) (m : Memoria),
      BEval e m false -> BEval (Not e) m true
  .

(* 5.4 *)
Fixpoint beval (m : Memoria) (b : BoolExpr) : Valor :=
  match b with
    | BoolVar v => lookup m v
    | Bool b => b
    | Or e1 e2 => orb (beval m e1) (beval m e2)
    | Not e => negb (beval m e)
  end.

(* 5.5 *)
Lemma e55 : forall (m : Memoria) (e : BoolExpr),
  BEval e m (beval m e).
Proof.
  intros.
  induction e;
  simpl.
    apply evar.

    destruct b; [ apply eboolt | apply eboolf ].

    destruct (beval m e1);
    simpl;
    [ apply (eorl e1 e2 m) in IHe1;
      trivial
    | destruct (beval m e2);
      [ apply (eorr e1 e2 m) in IHe2
      | apply (eorrl e1 e2 m) ]; trivial
    ].

    destruct (beval m e);
    simpl; [ apply enott | apply enotf ]; trivial.
Qed.

(* 5.3 *)
Lemma e53a : forall (m : Memoria),
  ~ (BEval (Bool true) m false).
Proof.
  unfold not.
  intros.
  inversion H.
Qed.

Lemma e53b :
  forall (m : Memoria) (e1 e2 : BoolExpr) (w : bool),
    BEval e1 m false
    -> BEval e2 m w
    -> BEval (Or e1 e2) m w.
Proof.
  intros.
  destruct w; [ apply eorr | apply eorrl]; trivial.
Qed.

Lemma e53c :
  forall (m : Memoria) (e : BoolExpr) (w1 w2 : bool),
    BEval e m w1 -> BEval e m w2 -> w1 = w2.
Proof.
  intros.
   induction e.
     inversion H ; inversion H0.
     reflexivity.
     induction b.
     inversion H ; inversion H0.
     reflexivity.
     inversion H ; inversion H0.
     reflexivity.
     inversion H; inversion H0.
       trivial.

       trivial.

       destruct H10.
       rewrite H4.
       rewrite H4 in H5.
       exact (IHe1 H5 H8).

       trivial.

       trivial.

       destruct H10.
       rewrite H4.
       rewrite H4 in H5.
       exact (IHe2 H5 H11).

       destruct H5.
       rewrite H10.
       rewrite H10 in H11.
       exact (IHe1 H3 H11).

       destruct H5.
       rewrite H10.
       rewrite H10 in H11.
       exact (IHe2 H6 H11).

       trivial.

    inversion H; inversion H0; try trivial;
      rewrite H4 in H6;
      rewrite H8 in H2;
      rewrite H4;
      rewrite H8;
      exact (IHe H6 H2).
Qed.

Lemma e53d :
  forall (m : Memoria) (e1 e2 : BoolExpr),
    BEval e1 m true -> ~ BEval (Not (Or e1 e2)) m true.
Proof.
  unfold not.
  intros.
  apply (eorl e1 e2) in H.
  apply enott in H.
  assert (false = true).
  elim (e53c m (Not (Or e1 e2)) false true); trivial.
  discriminate H1.
Qed.

End Ejercicio5.

(**
If you haveIf you have the hypothesis [H : a = b],
then you can do [apply (f_equal f) in H]
it will replace it with [H : f a = f b] 
**)

Section Ejercicio6.

(* 6.1 *)

Inductive Instr : Set :=
  | Skip : Instr
  | Assign : Var -> BoolExpr -> Instr
  | IfThenElse : BoolExpr -> Instr -> Instr -> Instr
  | While : BoolExpr -> Instr -> Instr
  | Begin : LInstr -> Instr
  with
  LInstr : Set :=
  | Fin : LInstr
  | Seq : Instr -> LInstr -> LInstr
  .

(* 6.2 *)
Infix ";" := Seq (at level 60, right associativity).

Variable v1 v2 : Var.

Definition PP : Instr :=
  Begin (
    Assign v1 (Bool true);
    Assign v2 (Not (BoolVar v1));
    Fin
  ).

Variable aux : Var.

Definition swap : Instr :=
  Begin (
    Assign aux (BoolVar v1);
    Assign v1 (BoolVar v2);
    Assign v2 (BoolVar aux);
    Fin
  ).

(* 6.3 *)
Fixpoint eqnat (n1 n2 : nat) : bool :=
  match n1, n2 with
    | 0, 0 => true
    | (S n), (S m) => eqnat n m
    | _, _ => false
  end.

Definition update : Memoria -> Var -> Valor -> Memoria :=
  fun m v w =>
    fun (var : Var) =>
      if eqnat v var then w else lookup m var
  .

End Ejercicio6.

Section Ejercicio7.

(* 6.2 *)
Infix ";" := Seq (at level 60, right associativity).

(* 7.1 *)
Inductive Execute : Instr -> Memoria -> Memoria -> Prop :=
  | xAss : forall (m : Memoria) (e : BoolExpr)
    (w : Valor) (v : Var),
    BEval e m w -> Execute (Assign v e) m (update m v w)
  | xSkip : forall (m : Memoria),
    Execute Skip m m
  | xIfThen : forall (m m1 : Memoria) (c : BoolExpr)
    (p1 p2 : Instr),
    BEval c m true -> Execute p1 m m1
    -> Execute (IfThenElse c p1 p2) m m1
  | xIfElse : forall (m m2 : Memoria) (c : BoolExpr)
    (p1 p2 : Instr),
    BEval c m false -> Execute p2 m m2
    -> Execute (IfThenElse c p1 p2) m m2
  | xWhileTrue : forall (m m1 m2 : Memoria) (c : BoolExpr)
    (p : Instr),
    BEval c m true
    -> Execute p m m1
    -> Execute (While c p) m1 m2
    -> Execute (While c p) m m2
  | xWhileFalse : forall (m : Memoria) (c : BoolExpr)
    (p : Instr),
    BEval c m false
    -> Execute (While c p) m m
  | xBeginEnd : forall (p : LInstr) (m m1 : Memoria),
    ExecuteLInstr p m m1 -> Execute (Begin p) m m1
    with
    ExecuteLInstr : LInstr -> Memoria -> Memoria -> Prop :=
      | xEmptyBlock : forall (m : Memoria), ExecuteLInstr Fin m m
      | xNext : forall (i : Instr) (li : LInstr) (m m1 m2 : Memoria),
        Execute i m m1 -> ExecuteLInstr li m1 m2
        -> ExecuteLInstr (i; li) m m2
  .

(* 7.2 *)
Lemma e72 : forall (e1 e2 : Instr) (m m1 : Memoria),
  Execute (IfThenElse (Not (Bool true)) e1 e2) m m1
  -> Execute (IfThenElse (Bool true) e2 e1) m m1.
Proof.
   intros.
   inversion_clear H;
   inversion_clear H0;
   inversion_clear H.
   apply xIfThen; trivial.
   apply eboolt.
Qed.

(* 7.3 *)
Lemma e73 : forall (e1 e2 : Instr) (m m1 : Memoria) (c : BoolExpr),
  Execute (IfThenElse (Not c) e1 e2) m m1
  -> Execute (IfThenElse c e2 e1) m m1.
Proof.
  intros.
  inversion_clear H;
  inversion_clear H0;
  [ apply xIfElse | apply xIfThen ]; trivial.
Qed.

(* 7.4 *)
Lemma e74 : forall (p : Instr) (m m1 : Memoria),
  Execute (While (Bool false) p) m m1 -> m = m1.
Proof.
  intros.
  inversion_clear H;
  inversion_clear H0.
  reflexivity.
Qed.

(**
Lemma e76_aux : forall (m m1 : Memoria) (v : Var) (val : Valor),
  update m v val = m1 -> lookup m1 v = val.
Proof.
  intros.
  assert (BEval (BoolVar v) m1 (beval m1 (BoolVar v))).
  apply (e55 m1 (BoolVar v)).
  rewrite <- H in H0.
  simpl in H0.
    Check e53c.
    apply (e53c m1 (BoolVar v)).
      apply (evar v m1).

      rewrite <- H.
      simpl in H0.
      inversion H0.
      

      
Qed.
**)

(* 7.5 *)
Lemma e75 : forall (c : BoolExpr) (p : Instr) (m m1 : Memoria),
  Execute (Begin (IfThenElse c p Skip; While c p; Fin)) m m1
  -> Execute (While c p) m m1.
Proof.
  intros.
  inversion H.
  clear m0 m2 H2 H3 H0 p0.
  inversion H1.
  clear m0 m3 i H0 li H2 H4 H5.
  inversion H6.
  clear i li m0 m4 H0 H2 H5 H7.
  inversion H8.
  rewrite H5 in H4.
  clear m0 H2 H8 H5 m3.
  inversion H3.
    clear m0 c0 p1 p2 m3 H5 H8 H0 H2 H7.
    apply (xWhileTrue m m2 m1 c); trivial.

    clear m0 m3 c0 p1 p2 H0 H2 H7 H5 H8.
    inversion H10.
    rewrite <- H5.
    rewrite <- H5 in H4.
    trivial.
Qed.

(* Lemita *)
(**
Lemma e76_aux : forall (m m1 : Memoria) (v : Var),
  Execute (Begin (Assign v (Bool true); Fin)) m m1
  -> lookup m1 v = true.
Proof.
  intros.
  inversion_clear H.
  inversion_clear H0.
  inversion H1.
  rewrite H3 in H.
  rewrite H3 in H1.
  clear m0 m2 H2 H3.
  inversion H.
  inversion H5.
  clear H0 H2 H3 m2 H7 v0 e m0 m2.

  destruct w.
  Check e53c.
  apply (e53c m (Bool true)); try trivial.
    case (lookup (update m v true) v); trivial.
Qed.
**)

Axiom lookup1 : forall (m : Memoria) (v : Var) (val : Valor),
  lookup (update m v val) v = val.
Axiom lookup2 : forall (m : Memoria) (v1 v2 : Var) (val : Valor),
  v1 <> v2 -> lookup (update m v1 val) v2 = lookup m v2.

(* 7.6 *)
Lemma e76 : forall (m m1 : Memoria) (v1 v2 : Var),
  v1 <> v2 -> Execute (PP v1 v2) m m1
  -> lookup m1 v1 = true /\ lookup m1 v2 = false.
Proof.
  (**unfold not.
  intros.
  split.
    inversion_clear H0.
    inversion_clear H1.
    inversion_clear H0.
    inversion H1.
    clear m0 H3.
    inversion_clear H2.
    inversion H3.
    rewrite H6 in H0.
    clear H3 m0 H5 H6 m3.
    inversion H0.
    clear H5 H2 H3 v e m0.
    inversion H7.
    clear H2 H5 m0 e.
    rewrite (lookup2 m2 v2 v1 false).
 **)

  unfold not.
  intros.
    inversion_clear H0.
    inversion_clear H1.
    inversion_clear H2.
    inversion H3.
    rewrite H5 in H1.
    clear m0 H3 H4 H5 m3.
    inversion H0.
    clear H2 H4 H3 m0 e.
    rewrite <- H5 in H0.
    rewrite <- H5 in H1.
    (*clear H5. *)
    inversion H6.
    clear m0 H3.
    rewrite <- H4 in H6.
    rewrite <- H4 in H1.
    rewrite <- H4 in H0.
    rewrite <- H4 in H5.
    clear H4 w.
    inversion_clear H1.
(*    inversion_clear H2. *)

    split.
      rewrite lookup2.
      rewrite lookup1.
      reflexivity.
      intuition.

      rewrite lookup1.
      destruct w; try trivial.
      inversion H2.
      assert (BEval (BoolVar v1) (update m v1 true)
      (beval (update m v1 true) (BoolVar v1))).
    apply e55.
      simpl in H7.
      rewrite lookup1 in H7.
      Check e53c.
      apply (e53c (update m v1 true) (BoolVar v1)); trivial.
Qed.
(**

INTENTOS FALLIDOS :P
:
        reflexivity.

        inversion H2.
          rewrite H7.
          rewrite H11.
          trivial.
        

    split.
      rewrite lookup2.
      rewrite lookup1.
      reflexivity.
      intuition.

      rewrite lookup1.
    Check e55.
    assert (BEval (BoolVar v1) (update m2 v2 false)
      (beval (update m2 v2 false) (BoolVar v1))).
    apply e55.
    simpl in H2.
    apply (e53c (update m2 v2 false) (BoolVar v1)).
      rewrite H5.
      trivial.

      apply (lookup2) .
      


  unfold not.
  intros.
  split.
    inversion_clear H0.
    Check xNext.
    inversion_clear H1.
    inversion_clear H2.
    inversion H3.
    rewrite H5 in H1.
    clear m0 m3 H4 H5 H3.
    inversion_clear H1.
      inversion_clear H2.
      inversion_clear H0.
      inversion H2.
      rewrite <- H4 in H2.
      clear H3 m0 w0 H4 w.
      Check e53c.
      apply (e53c m2 (BoolVar v1)); try apply evar; try trivial.
      Check xAss.
 

    inversion_clear H0.
    inversion_clear H1.
    inversion_clear H2.
    inversion H3.
    rewrite H5 in H1.
    clear m0 H4 H5 H3 m3.
    inversion_clear H1.
    inversion_clear H2.
    Check xAss.
    apply (xAss m2 (BoolVar v1) true v2) in H1.
    inversion H1.
    inversion H5.
    rewrite <- H9 in H5.
    inversion H5.    
    Check e53c.

    inversion_clear H0.
    inversion_clear H1.
    inversion_clear H0.
    inversion H1.
    clear H3 m0.
    (* trabajando con H2 *)
    inversion H2.
    clear m0 m4 H3 H6 H7 i li H0.
    inversion H8.
    rewrite H6 in H5.
    rewrite H6 in H8.
    clear m0 H3 H6.
    inversion H5.
    clear H0 v e H6 H3.
      inversion H9.
      clear e m4 H0 H6.
      inversion H3.
      clear v m4 H6 H0.
      Check e53c.
      apply (e53c m1 (BoolVar v1)).
        rewrite <- H10 in H7.
        rewrite H7.
        apply evar.

        rewrite <- H7.
        rewrite H12.
        apply evar.

    inversion_clear H0.
    inversion_clear H1.
    inversion_clear H2.
    inversion H3.
    rewrite H5 in H1.
    clear H4 m0 m3 H3 H5.
    inversion_clear H0.
    inversion_clear H1.
    inversion H2.
    clear H3 m0.
    inversion H0.
    clear H1 H5.

    inversion H3.
    rewrite H5 in H0.
    clear H4 H3 m0 m3 H5.
    inversion H1.
    clear m0 H3.
    inversion H0.
    rewrite H6.
    clear H2 H5 H3 H6.
    inversion_clear H7.
    inversion_clear H2.
    inversion_clear H0.
    
    apply (e53c m2 (BoolVar v1)).



    inversion_clear H0.
    inversion_clear H1.
    inversion H0.
    rewrite <- H5 in H0.
    rewrite <- H5 in H2.
    clear H3 H4 m0 m2 H5.
    inversion_clear H0.
    clear w0 H3.
    inversion H6.
    clear m0 H3.
    inversion H2.
    clear i li m0 m3 H0 H3 H7 H8.
    inversion H9.
    clear H3 m0.
    rewrite H7 in H9.
    rewrite H7 in H5.
    clear m2 H7.
    inversion H5.
    clear H0 H7 H3 e0 m0 v0.
    inversion H10.
    clear e0 H0 H7 m0.
    inversion H3.
    clear v0 H7 H0 H8.
    rewrite <- H4.
    clear H11 m0.
    
    apply (e53c m (BoolVar v1)).
      apply (evar).

    injection.
    clear m0 H3.
    inversion_clear H2.
    inversion H3.
    rewrite H6 in H0.
    rewrite H6 in H3.
    clear H5 H6 m3 m0.
    inversion H0.
    rewrite <- H7 in H0.
    rewrite <- H7 in H3.
    inversion_clear H0.
    inversion_clear H9.
    clear m0 w1 H5.
    apply (e53c (update m2 v2 false) (BoolVar v1)).


    inversion H9.
    inversion H8.
    

    inversion_clear H0.
    inversion_clear H1.
    inversion H0.
    rewrite <- H5 in H0.
    apply (e53c m1 (BoolVar v1)).
      apply evar.

      Check e53c.
      inversion H6.
      inversion H0.
      inversion H2.
      inversion H16.`
      apply (e53c m1 (BoolVar v1)) in H1.

  intros.
  split.
  inversion_clear H0.
  inversion_clear H1.
  inversion_clear H0.
  assert (BEval (BoolVar v1) m1 (lookup m1 v1)).
  apply (evar v1 m1).
  inversion_clear H2. (* evar : forall (v : Var) (m : Memoria) *)
  inversion H0.
  destruct w.


  (*
   forall (m : Memoria) (e : BoolExpr) (w1 w2 : bool),
    BEval e m w1 /\ BEval e m w2 -> w1 = w2.
   *)
  
Qed.
**)
End Ejercicio7.