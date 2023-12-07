(*****************************************************************************)
(*                            *                    Trocq                     *)
(*  _______                   *           Copyright (C) 2023 MERCE           *)
(* |__   __|                  *    (Mitsubishi Electric R&D Centre Europe)   *)
(*    | |_ __ ___   ___ __ _  *       Cyril Cohen <cyril.cohen@inria.fr>     *)
(*    | | '__/ _ \ / __/ _` | *       Enzo Crance <enzo.crance@inria.fr>     *)
(*    | | | | (_) | (_| (_| | *   Assia Mahboubi <assia.mahboubi@inria.fr>   *)
(*    |_|_|  \___/ \___\__, | ************************************************)
(*                        | | * This file is distributed under the terms of  *)
(*                        |_| * GNU Lesser General Public License Version 3  *)
(*                            * see LICENSE file for the text of the license *)
(*****************************************************************************)

From Coq Require Import ssreflect.
From Coq Require Import Vectors.VectorDef.
From Trocq Require Import Trocq.
From Trocq Require Import Param_nat Param_trans.

Set Universe Polymorphism.

Module Vector.

Inductive t (A : Type) : nat -> Type :=
  | nil : t A 0
  | cons : forall (n : nat), A -> t A n -> t A (S n).
Arguments nil {_}.
Arguments cons {_ _}.

Definition hd : forall {A : Type} {n : nat}, t A (S n) -> A :=
  fun A n v =>
    match v in t _ m
    return match m with O => Unit | S _ => A end
    with
    | nil => tt
    | cons _ a _ => a
    end.

Definition tail : forall {A : Type} {n : nat}, t A (S n) -> t A n :=
  fun A n v =>
    match v in t _ m
    return match m with O => Unit | S k => t A k end
    with
    | nil => tt
    | cons _ _ v' => v'
    end.

Definition const : forall {A : Type} (a : A) (n : nat), t A n :=
  fun A a =>
    fix F n :=
      match n with
      | O => nil
      | S n' => cons a (F n')
      end.

Definition append :
  forall {A : Type} {n1 n2 : nat} (v1 : t A n1) (v2 : t A n2),
    t A (n1 + n2) :=
  fun A n1 n2 v1 v2 =>
    (fix F n (v : t A n) {struct v} : t A (n + n2) :=
      match v with
      | nil => v2
      | @cons _ n a v => cons a (F n v)
      end) n1 v1.

Lemma append_const {A : Type} (a : A) (n1 n2 : nat) :
  append (const a n1) (const a n2) = const a (n1 + n2).
Proof.
  induction n1.
  - reflexivity.
  - simpl. apply ap. assumption.
Qed.

Lemma append_comm_cons {A : Type} {n1 n2 : nat} (v1 : t A n1) (v2 : t A n2) (a : A) :
  cons a (append v1 v2) = append (cons a v1) v2.
Proof.
  simpl. reflexivity.
Defined.

Inductive tR (A A' : Type) (AR : A -> A' -> Type) :
  forall (n n' : nat) (nR : natR n n'), t A n -> t A' n' -> Type :=
  | nilR : tR A A' AR O O OR nil nil
  | consR :
    forall
      (n n' : nat) (nR : natR n n') (a : A) (a' : A') (aR : AR a a')
      (v : t A n) (v' : t A' n') (vR : tR A A' AR n n' nR v v'),
        tR A A' AR (S n) (S n') (SR n n' nR) (cons a v) (cons a' v').

Definition map :
  forall (A A' : Type) (AR : Param10.Rel A A') (n n' : nat) (nR : natR n n'),
    t A n -> t A' n' :=
  fun A A' AR =>
    fix F n n' nR :=
      match nR with
      | OR => fun _ => nil
      | SR m m' mR => fun v => cons (map AR (hd v)) (F m m' mR (tail v))
      end.

Definition t0 {A} (v : t A O) : v = nil := match v in t _ m return
     (match m return t A m -> Type with
       O => fun v => v = nil | S k => fun _ => Unit end) v
   with nil => 1%path | cons _ _ _ => tt end.

Definition tE {A n} (v : t A (S n)) : v = cons (hd v) (tail v) :=
 (match v in t _ m return
     (match m return t A m -> Type with
       O => fun _ => Unit | S k => fun v => v = (cons (hd v) (tail v))
     end) v
   with nil => tt | cons _ a w => 1%path end).

Lemma path_prodE  {A B : Type} {x x' : A} {y y' : B} :
  (x, y) = (x', y') -> x = x' /\ y = y'.
Proof.
move=> e; split; move: e.
- by move=> /(ap fst).
- by move=> /(ap snd).
Defined.

Definition t0P A P (v : t A O) : P nil -> P v := match v in t _ m return
     (match m return t A m -> Type with
       O => fun v => P nil -> P v | S k => fun _ => Unit end) v
   with nil => id | cons _ _ _ => tt end.

Definition tSP A n P : (forall a (v : t A n), P (cons a v)) -> forall v, P v.
Proof. by move=> Pn v; apply (transport P (tE _)^); apply Pn. Defined.

Definition map_in_R :
  forall
    (A A' : Type) (AR : Param2a0.Rel A A') (n n' : nat) (nR : natR n n')
    (v : t A n) (v' : t A' n'),
      map A A' AR n n' nR v = v' -> tR A A' AR n n' nR v v'.
Proof.
intros A A' AR n n'.
elim=> [{n n'}|{n'}n n' nR IHn]/=.
  - by elim/t0P; elim/t0P; constructor.
  - elim/tSP => a v; elim/tSP => a' v' e.
    constructor.
    + by have /(ap hd)/(map_in_R AR) := e.
    + by have /(ap tail)/IHn := e.
Defined.

Definition R_in_map :
  forall
    (A A' : Type) (AR : Param2b0.Rel A A') (n n' : nat) (nR : natR n n')
    (v : t A n) (v' : t A' n'),
      tR A A' AR n n' nR v v' -> map A A' AR n n' nR v = v'.
Proof.
  intros A A' AR n n' nR v v' vR.
  elim: vR => [|{}n {}n' {}nR a a' aR {}v {}v' _ []].
  - reflexivity.
  - by elim (R_in_map AR a a' aR).
Defined.

Definition R_in_mapK :
  forall
    (A A' : Type) (AR : Param44.Rel A A') (n n' : nat) (nR : natR n n')
    (v : t A n) (v' : t A' n') (vR : tR A A' AR n n' nR v v'),
      map_in_R A A' AR n n' nR v v' (R_in_map A A' AR n n' nR v v' vR) = vR.
Proof.
  intros A A' AR n n' nR v v' vR.
  elim: vR => {n n' nR v v'}[|n n' nR a a' aR v v' IHv r]//=.
  elim: {2}aR / (R_in_mapK AR).
  elim: (Hierarchy.R_in_map AR a a' aR)=> //=.
  elim: {2}_ / r.
  by elim: R_in_map.
Defined.

Definition Param_nat_symK m n (nR : natR m n) : nR = Param_nat_sym (Param_nat_sym nR).
Proof. by elim: nR => //= {}m {}n mn emn; apply: ap. Defined.

Definition tR_sym_f {A A' : Type} (AR : A -> A' -> Type) {n n' : nat} (nR : natR n n')
  {v : t A n} {v' : t A' n'} :
      sym_rel (tR A A' AR n n' nR) v' v -> tR A' A (sym_rel AR) n' n (Param_nat_sym nR) v' v.
Proof. by elim=> //=; constructor. Defined.

Definition tR_sym_t {A A' : Type} (AR : A -> A' -> Type) {n n' : nat} (nR : natR n n')
   {v' : t A' n'} {v : t A n} :
    tR A A' AR n n' (Param_nat_sym (Param_nat_sym nR)) v v' <~> tR A A' AR n n' nR v v'.
Proof.
unshelve eapply equiv_adjointify.
- apply: (transport (fun nR => tR _ _ _ _ _ nR _ _)).
  symmetry; exact: Param_nat_symK.
- apply: (transport (fun nR => tR _ _ _ _ _ nR _ _)).
  exact: Param_nat_symK.
- by move=> vR; rewrite -transport_pp concat_pV.
- by move=> vR; rewrite -transport_pp concat_Vp.
Defined.

Local Notation f := (tR_sym_f _ _).
Local Notation g := (tR_sym_t _ _).

Definition tR_sym_fK {A A' : Type} (AR : A -> A' -> Type) {n n' : nat} (nR : natR n n')
  (v : t A n) (v' : t A' n') (vR : tR A A' AR n n' nR v v') :
     g (f (f vR)) = vR.
Proof.
elim: vR => // {}n {}n' {}nR a a' aR {}v {}v' vR {2}<-/=.
by elim: _ / Param_nat_symK (tR_sym_f _ _ _).
Defined.

Definition tR_sym_fE {A A' : Type} (AR : A -> A' -> Type) {n n' : nat} (nR : natR n n')
  (v : t A n) (v' : t A' n') (vR : tR A A' AR n n' nR v v') :
     f vR = g (f (g^-1 vR)).
Proof. by rewrite -{2}[vR]tR_sym_fK eissect tR_sym_fK. Qed.

Definition tR_sym  (A A' : Type) (AR : A -> A' -> Type) (n n' : nat) (nR : natR n n')
   (v' : t A' n') (v : t A n) :
      sym_rel (tR A A' AR n n' nR) v' v <~> tR A' A (sym_rel AR) n' n (Param_nat_sym nR) v' v.
Proof.
  unshelve eapply equiv_adjointify.
  - exact: tR_sym_f.
  - move/tR_sym_f/tR_sym_t; exact.
  - by move=> vR; rewrite [f (g _)]tR_sym_fE eissect tR_sym_fK.
  - exact: tR_sym_fK.
Defined.

Definition Map4 (A A' : Type) (AR : Param44.Rel A A') (n n' : nat) (nR : natR n n') :
  Map4.Has (tR A A' AR n n' nR).
Proof.
  unshelve econstructor.
  - exact (map A A' AR n n' nR).
  - exact (map_in_R A A' AR n n' nR).
  - exact (R_in_map A A' AR n n' nR).
  - exact (R_in_mapK A A' AR n n' nR).
Defined.

Definition Param44 :
  forall (A A' : Type) (AR : Param44.Rel A A') (n n' : nat) (nR : natR n n'),
    Param44.Rel (t A n) (t A' n').
Proof.
  intros A A' AR n n' nR.
  unshelve econstructor.
  - exact (@tR A A' AR n n' nR).
  - exact (Map4 A A' AR n n' nR).
  - unshelve eapply
      (@eq_Map4 _ _
        (sym_rel (tR A A' AR n n' nR))
        (tR A' A (sym_rel AR) n' n (Param_nat_sym nR))).
    + exact (tR_sym A A' AR n n' nR).
    + exact (Map4 A' A (Param44_sym A A' AR) n' n (Param_nat_sym nR)).
Defined.

Definition Param_append
  (A A' : Type) (AR : Param00.Rel A A')
  (n1 n1' : nat) (n1R : natR n1 n1')
  (n2 n2' : nat) (n2R : natR n2 n2')
  (v1 : t A n1) (v1' : t A' n1') (v1R : tR A A' AR n1 n1' n1R v1 v1')
  (v2 : t A n2) (v2' : t A' n2') (v2R : tR A A' AR n2 n2' n2R v2 v2') :
    tR A A' AR (n1 + n2) (n1' + n2') (Param_add n1 n1' n1R n2 n2' n2R)
      (append v1 v2) (append v1' v2').
Proof.
  induction v1R.
  - simpl. exact v2R.
  - simpl. apply consR.
    + exact aR.
    + exact IHv1R.
Defined.

Definition Param_const
  (A A' : Type) (AR : Param00.Rel A A')
  (a : A) (a' : A') (aR : AR a a')
  (n n' : nat) (nR : natR n n') :
    tR A A' AR n n' nR (const a n) (const a' n').
Proof.
  induction nR; simpl.
  - apply nilR.
  - apply consR.
    * exact aR.
    * exact IHnR.
Defined.

End Vector.

Definition tuple (A : Type) : nat -> Type :=
  fix F n :=
    match n with
    | O => Unit
    | S n' => F n' * A
    end.

Definition const : forall {A : Type} (a : A) (n : nat), tuple A n :=
  fun A a =>
    fix F n :=
      match n with
      | O => tt
      | S n' => (F n', a)
    end.

Definition append :
  forall {A : Type} {n1 n2 : nat} (t1 : tuple A n1) (t2 : tuple A n2),
    tuple A (n1 + n2) :=
  fun A =>
    fix F n1 :=
      match n1 with
      | O => fun n2 _ t2 => t2
      | S n =>
        fun n2 t1 t2 =>
          match t1 with
          | (t, a) => (F n n2 t t2, a)
          end
      end.

(* ========================================================================== *)

(* tuple ~ vector *)

Definition tuple_to_vector {A : Type} : forall {n : nat}, tuple A n -> Vector.t A n :=
  fix F n : tuple A n -> Vector.t A n :=
    match n with
    | O => fun _ => Vector.nil
    | S m => fun t =>
      match t with
      | (t', a) => Vector.cons a (F m t')
      end
    end.

Definition vector_to_tuple {A : Type} : forall {n : nat}, Vector.t A n -> tuple A n :=
  fix F n : Vector.t A n -> tuple A n :=
    match n with
    | O => fun _ => tt
    | S m => fun v => (F m (Vector.tail v), Vector.hd v)
    end.

Definition vector_to_tupleK {A : Type} :
  forall {n : nat} (v : Vector.t A n), tuple_to_vector (vector_to_tuple v) = v :=
    fix F n v :=
      match v with
      | Vector.nil => idpath
      | Vector.cons m a v' => ap (Vector.cons a) (F m v')
      end.

Definition tuple_to_vectorK {A : Type} :
  forall {n : nat} (t : tuple A n), vector_to_tuple (tuple_to_vector t) = t.
Proof.
  refine (
    fix F n : forall (t : tuple A n), vector_to_tuple (tuple_to_vector t) = t :=
      match n as k
      return forall (t : tuple A k), vector_to_tuple (tuple_to_vector t) = t
      with
      | O => fun t => match t with tt => idpath end
      | S m => _
      (* fun t => match t with (t', a) => path_prod _ _ _ _ end *)
      end
  ).
  intros [t' a].
  apply path_prod; simpl.
  - exact (F m t').
  - apply idpath.
Defined.

Definition Param44_tuple_vector_d (A : Type) (n : nat) : Param44.Rel (tuple A n) (Vector.t A n).
Proof.
apply Iso.toParam; unshelve econstructor.
- exact: tuple_to_vector.
- exact: vector_to_tuple.
- exact: tuple_to_vectorK.
- exact: vector_to_tupleK.
Defined.

Definition Param44_tuple_vector
  (A A' : Type) (AR : Param44.Rel A A') (n n' : nat) (nR : natR n n') :
    Param44.Rel (tuple A n) (Vector.t A' n').
Proof.
  unshelve eapply (@Param44_trans _ (Vector.t A n)).
  - exact (Param44_tuple_vector_d A n).
  - exact (Vector.Param44 A A' AR n n' nR).
Defined.

Definition Param02b_tuple_vector :
  forall (A A' : Type) (AR : Param44.Rel A A') (n n' : nat) (nR : natR n n'),
    Param02b.Rel (tuple A n) (Vector.t A' n') :=
      Param44_tuple_vector.

Definition tuple_vectorR {A : Type} {n : nat} := rel (Param44_tuple_vector_d A n).

Definition Param_append_d
  {A : Type} {n1 n2 : nat}
  {t1 : tuple A n1} {v1 : Vector.t A n1} (tv1R : tuple_vectorR t1 v1)
  {t2 : tuple A n2} {v2 : Vector.t A n2} (tv2R : tuple_vectorR t2 v2) :
      tuple_vectorR (append t1 t2) (Vector.append v1 v2).
Proof.
  unfold tuple_vectorR in *. rewrite <- tv1R, <- tv2R.
  induction n1.
  - simpl in t1. unfold append, tuple_to_vector at 2. simpl. reflexivity.
  - destruct t1 as [t' a]. simpl in tv1R. simpl.
    rewrite /graph/=.
    apply ap.
    unshelve eapply IHn1.
    + exact (Vector.tail v1).
    + rewrite <- tv1R. simpl. reflexivity.
Defined.

Definition Param_append
  (A A' : Type) (AR : Param00.Rel A A')
  (n1 n1' : nat) (n1R : natR n1 n1')
  (n2 n2' : nat) (n2R : natR n2 n2')
  (t1 : tuple A n1) (v1' : Vector.t A' n1')
  (tv1R : R_trans (@tuple_vectorR A n1) (Vector.tR A A' AR n1 n1' n1R) t1 v1')
  (t2 : tuple A n2) (v2' : Vector.t A' n2')
  (tv2R : R_trans (@tuple_vectorR A n2) (Vector.tR A A' AR n2 n2' n2R) t2 v2') :
    R_trans
      (@tuple_vectorR A (n1 + n2))
      (Vector.tR A A' AR (n1 + n2) (n1' + n2') (Param_add n1 n1' n1R n2 n2' n2R))
        (append t1 t2) (Vector.append v1' v2').
Proof.
  unfold R_trans, tuple_vectorR in *.
  destruct tv1R as [v1 [p1v1 p2v1]].
  destruct tv2R as [v2 [p1v2 p2v2]].
  exists (Vector.append v1 v2).
  split.
  - apply (Param_append_d p1v1 p1v2).
  - apply (Vector.Param_append).
    * exact p2v1.
    * exact p2v2.
Defined.

Definition Param_const_d {A : Type} (a : A) (n : nat) :
  tuple_vectorR (const a n) (Vector.const a n).
Proof.
  unfold tuple_vectorR.
  induction n; simpl.
  - reflexivity.
  - rewrite /graph; apply ap. exact IHn.
Defined.

Definition Param_const
  (A A' : Type) (AR : Param00.Rel A A') (a : A) (a' : A') (aR : AR a a')
  (n n' : nat) (nR : natR n n') :
    R_trans (@tuple_vectorR A n) (Vector.tR A A' AR n n' nR) (const a n) (Vector.const a' n').
Proof.
  unfold R_trans, tuple_vectorR.
  exists (Vector.const a n).
  split.
  - apply Param_const_d.
  - apply Vector.Param_const. exact aR.
Defined.

Trocq Use Param00_nat.
Trocq Use Param2a0_nat.
Trocq Use Param_add.
Trocq Use Param02b_tuple_vector.
Trocq Use Param_append.
Trocq Use Param_const.
Trocq Use Param01_paths.

Lemma append_const : forall {A : Type} (a : A) (n1 n2 : nat),
  append (const a n1) (const a n2) = const a (n1 + n2).
Proof.
  trocq. exact @Vector.append_const.
Qed.

Definition cons {A : Type} {n : nat} (a : A) (t : tuple A n) : tuple A (S n) := (t, a).

Definition Param_cons
  (A A' : Type) (AR : Param00.Rel A A') (n n' : nat) (nR : natR n n')
  (a : A) (a' : A') (aR : AR a a')
  (t : tuple A n) (v' : Vector.t A' n') :
    R_trans (@tuple_vectorR A n) (Vector.tR A A' AR n n' nR) t v' ->
    R_trans
      (@tuple_vectorR A (S n)) (Vector.tR A A' AR (S n) (S n') (SR n n' nR))
      (cons a t) (Vector.cons a' v').
Proof.
  intros [v [tvR vv'R]].
  unfold R_trans, tuple_vectorR in *.
  exists (Vector.cons a v).
  split.
  - simpl in *. unfold graph in *. simpl. apply ap. exact tvR.
  - apply Vector.consR.
    + exact aR.
    + exact vv'R.
Defined.

Trocq Use Param_cons.
Trocq Use SR.
Trocq Use Param_add.

Lemma append_comm_cons : forall {A : Type} {n1 n2 : nat}
    (v1 : tuple A n1) (v2 : tuple A n2) (a : A),
  cons a (append v1 v2) = append (cons a v1) v2.
Proof.
Fail trocq.
  (* apply Vector.append_comm_cons. *)
Abort.

Axiom cheat : forall A, A.
Ltac cheat := apply cheat.

Definition bitvector (k : nat) := Vector.t Datatypes.bool k.
Definition bounded_nat (k : nat) := {n : nat & n < pow 2 k}%nat.

Definition bv_to_nat : forall {k : nat}, bitvector k -> nat :=
  fix F k bv :=
    match bv with
    | Vector.nil => O
    | Vector.cons k' b bv' => (if b then S else id) (2 * F k' bv')%nat
    end.

Lemma S_add1 : forall (n : nat), S n = (n + 1)%nat.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl add. apply ap. exact IHn.
Defined.

Lemma one_lt_pow2 (k : nat) : (1 <= pow 2 k)%nat.
Proof.
  induction k.
  - simpl. apply leq_n.
  - apply (leq_trans IHk).
    simpl.
    apply n_leq_add_n_k.
Defined.

Lemma const1_pow2 : forall {k : nat},
  (bv_to_nat (Vector.const Datatypes.true k) = pow 2 k - 1)%nat.
Proof.
  induction k.
  - reflexivity.
  - simpl. rewrite IHk.
    rewrite nat_add_n_Sm.
    rewrite <- nataddsub_comm.
    2: { apply one_lt_pow2. }
    apply ap.
    do 2 rewrite <- add_n_O.
    rewrite S_add1.
    unshelve erewrite (nataddsub_comm _ 1 1 _).
    1: { apply one_lt_pow2. }
    rewrite <- nataddsub_assoc.
    2: { apply leq_n. }
    simpl. rewrite <- add_n_O.
    reflexivity.
Defined.

Lemma bv_bound_ones {k : nat} (bv : bitvector k) :
  (bv_to_nat bv <= bv_to_nat (Vector.const Datatypes.true k))%nat.
Proof.
  induction bv as [|k' b' bv IH].
  - apply leq_0_n.
  - simpl. destruct b'.
    + simpl.
      do 2 rewrite <- add_n_O.
      apply leq_S_n'.
      apply nat_add_bifunctor.
      all: apply IH.
    + simpl. unfold id.
      apply leq_S.
      do 2 rewrite <- add_n_O.
      apply nat_add_bifunctor.
      all: apply IH.
Defined.

Theorem bv_bound {k : nat} (bv : bitvector k) : (bv_to_nat bv <= pow 2 k - 1)%nat.
Proof.
  rewrite <- const1_pow2. apply bv_bound_ones.
Defined.

Definition bv_to_bnat {k : nat} (bv : bitvector k) : bounded_nat k.
Proof.
  unshelve econstructor.
  - exact (bv_to_nat bv).
  - apply (mixed_trans1 _ (pow 2 k - 1) _).
    * apply bv_bound.
    * apply natpmswap1.
      1: { apply one_lt_pow2. }
      rewrite nat_add_comm.
      rewrite <- (S_add1 (pow 2 k)).
      apply n_lt_Sn.
Defined.
  
Definition R_bv_bnat {k : nat} (bv : bitvector k) (bn : bounded_nat k) :=
  bv_to_bnat bv = bn.

Definition map_in_R_bv_bnat {k : nat} {bv : bitvector k} {bn : bounded_nat k} :
  bv_to_bnat bv = bn -> R_bv_bnat bv bn.
Proof. intro e. unfold R_bv_bnat. exact e. Defined.

Definition R_in_map_bv_bnat {k : nat} {bv : bitvector k} {bn : bounded_nat k} :
  R_bv_bnat bv bn -> bv_to_bnat bv = bn.
Proof. intro e. unfold R_bv_bnat. exact e. Defined.

Definition R_in_mapK_bv_bnat
  {k : nat} {bv : bitvector k} {bn : bounded_nat k} (r : R_bv_bnat bv bn) :
    map_in_R_bv_bnat (R_in_map_bv_bnat r) = r.
Proof. unfold map_in_R_bv_bnat, R_in_map_bv_bnat. reflexivity. Defined.
  
Definition Map4_bv_bnat {k : nat} : Map4.Has (@R_bv_bnat k).
Proof.
  unshelve econstructor.
  - exact (@bv_to_bnat k).
  - exact (@map_in_R_bv_bnat k).
  - exact (@R_in_map_bv_bnat k).
  - exact (@R_in_mapK_bv_bnat k).
Defined.

Definition bnat_to_bv {k : nat} (bn : bounded_nat k) : bitvector k.
Proof.
  destruct bn as [n p].
  cheat.
Defined.

Definition map_in_R_bnat_bv {k : nat} {bn : bounded_nat k} {bv : bitvector k} :
  bnat_to_bv bn = bv -> R_bv_bnat bv bn.
Proof.
  cheat.
Defined.

Definition R_in_map_bnat_bv {k : nat} {bn : bounded_nat k} {bv : bitvector k} :
  R_bv_bnat bv bn -> bnat_to_bv bn = bv.
Proof.
  cheat.
Defined.

Definition R_in_mapK_bnat_bv
  {k : nat} {bn : bounded_nat k} {bv : bitvector k} (r : R_bv_bnat bv bn) :
    map_in_R_bnat_bv (R_in_map_bnat_bv r) = r.
Proof.
  cheat.
Defined.

Definition Map4_bnat_bv {k : nat} : Map4.Has (sym_rel (@R_bv_bnat k)).
Proof.
  unshelve econstructor.
  - exact (@bnat_to_bv k).
  - exact (@map_in_R_bnat_bv k).
  - exact (@R_in_map_bnat_bv k).
  - exact (@R_in_mapK_bnat_bv k).
Defined.

Definition Param44_bitvector_bnat {k : nat} :
  Param44.Rel (bitvector k) (bounded_nat k).
Proof.
  unshelve econstructor.
  - exact (@R_bv_bnat k).
  - exact (@Map4_bv_bnat k).
  - exact (@Map4_bnat_bv k).
Defined.
