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
From Trocq Require Import Param_nat Param_trans Param_bool.

Set Universe Polymorphism.

Module Vector.

(* the standard vector type *)

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

(* vector ~ vector *)

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

(* append ~ append *)

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

(* const ~ const *)

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

(* iterated tuple type *)

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

Definition head {A : Type} {n : nat} (t : tuple A (S n)) : A :=
  match t with (t', a) => a end.

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

(* proof by transitivity:
   - first tuple A n ~ vector A n
     the proof is easier when the parameters/indices do not change
   - then vector A n ~ vector A' n'
     exploiting already proved parametricity on vector
*)

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
Definition Param2a0_tuple_vector :
  forall (A A' : Type) (AR : Param44.Rel A A') (n n' : nat) (nR : natR n n'),
    Param2a0.Rel (tuple A n) (Vector.t A' n') :=
      Param44_tuple_vector.
Definition Param10_tuple_vector :
  forall (A A' : Type) (AR : Param44.Rel A A') (n n' : nat) (nR : natR n n'),
    Param10.Rel (tuple A n) (Vector.t A' n') :=
      Param44_tuple_vector.

Definition tuple_vectorR {A : Type} {n : nat} := rel (Param44_tuple_vector_d A n).

(* append (tuple) ~ append (vector) *)
(* proof by transitivity as well *)

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

(* const (tuple) ~ const (vector) *)

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

(* transfer examples *)

Module AppendConst.

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

End AppendConst.

(* head (tuple) ~ hd (vector) *)

Axiom Param_head : forall
  (A A' : Type) (AR : Param00.Rel A A') (n n' : nat) (nR : natR n n')
  (t : tuple A (S n)) (v' : Vector.t A' (S n'))
  (r : R_trans
        (@tuple_vectorR A (S n)) (Vector.tR A A' AR (S n) (S n') (SR n n' nR))
        t v'),
    AR (head t) (Vector.hd v').

(* composition with arithmetic parametricity as in int_to_Zp.v *)

Module HeadConst.

Axiom (int : Type) (Zp : Type) (Rp42b : Param42b.Rel Zp int).
Definition Rp00 : Param00.Rel Zp int := Rp42b.
Definition Rp2a0 : Param2a0.Rel Zp int := Rp42b.
Definition Rp02b : Param02b.Rel Zp int := Rp42b.

Lemma head_const {n : nat} : forall (i : int), Vector.hd (Vector.const i (S n)) = i.
Proof. destruct n; simpl; reflexivity. Qed.

Trocq Use Param00_nat.
Trocq Use Param2a0_nat.
Trocq Use SR.
Trocq Use Rp00.
Trocq Use Rp2a0.
Trocq Use Rp02b.
Trocq Use Param_head.
Trocq Use Param_const.
Trocq Use Param01_paths.

Lemma head_const' : forall {n : nat} (z : Zp), head (const z (S n)) = z.
Proof. trocq. intro n. apply head_const. Qed.

End HeadConst.







(* bug *)

Module bug.

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

Trocq Use SR.
Trocq Use Param_cons.

Lemma append_comm_cons : forall {A : Type} {n1 n2 : nat}
    (v1 : tuple A n1) (v2 : tuple A n2) (a : A),
  @paths (tuple A (S (n1 + n2))) (cons a (append v1 v2)) (append (cons a v1) v2).
Proof.
Fail Timeout 1 trocq.
  (* apply Vector.append_comm_cons. *)
Abort.

End bug.










(* bounded nat and bitvector *)
(* NB: we can use transitivity to make the proofs here too *)

Module BV.

Definition bounded_nat (k : nat) := {n : nat & n < pow 2 k}%nat.
Definition bitvector (k : nat) := Vector.t bool k.

(* bounded_nat k ~ bitvector k' *)

Axiom bnat_to_bv : forall {k : nat}, bounded_nat k -> bitvector k.
Definition R_bnat_bv {k : nat} (bn : bounded_nat k) (bv : bitvector k) :=
  bnat_to_bv bn = bv.
Definition map_in_R_bnat_bv {k : nat} {bn : bounded_nat k} {bv : bitvector k} :
  bnat_to_bv bn = bv -> R_bnat_bv bn bv.
Proof. exact id. Defined.
Definition R_in_map_bnat_bv {k : nat} {bn : bounded_nat k} {bv : bitvector k} :
  R_bnat_bv bn bv -> bnat_to_bv bn = bv.
Proof. exact id. Defined.
Definition R_in_mapK_bnat_bv
  {k : nat} {bn : bounded_nat k} {bv : bitvector k} (r : R_bnat_bv bn bv) :
    map_in_R_bnat_bv (R_in_map_bnat_bv r) = r.
Proof. reflexivity. Defined.

(* proofs can be done but they include quite painful arithmetic proof steps,
   for which there is no automation in HoTT, hence the axiomatisation *)
Definition bv_to_nat : forall {k : nat}, bitvector k -> nat :=
  fix F k bv :=
    match bv with
    | Vector.nil => O
    | Vector.cons k' b bv' =>
      (match b with true => S | false => id end) (2 * F k' bv')%nat
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

Axiom bv_bound :
  forall {k : nat} (bv : bitvector k), (bv_to_nat bv <= pow 2 k - 1)%nat.

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

Axiom map_in_R_bv_bnat :
  forall {k : nat} {bv : bitvector k} {bn : bounded_nat k},
    bv_to_bnat bv = bn -> R_bnat_bv bn bv.

Axiom R_in_map_bv_bnat :
  forall {k : nat} {bv : bitvector k} {bn : bounded_nat k},
    R_bnat_bv bn bv -> bv_to_bnat bv = bn.

Axiom R_in_mapK_bv_bnat :
  forall
    {k : nat} {bv : bitvector k} {bn : bounded_nat k} (r : R_bnat_bv bn bv),
      map_in_R_bv_bnat (R_in_map_bv_bnat r) = r.

Definition Map4_bnat_bv {k : nat} : Map4.Has (@R_bnat_bv k).
Proof.
  unshelve econstructor.
  - exact (@bnat_to_bv k).
  - exact (@map_in_R_bnat_bv k).
  - exact (@R_in_map_bnat_bv k).
  - exact (@R_in_mapK_bnat_bv k).
Defined.

Definition Map4_bv_bnat {k : nat} : Map4.Has (sym_rel (@R_bnat_bv k)).
Proof.
  unshelve econstructor.
  - exact (@bv_to_bnat k).
  - exact (@map_in_R_bv_bnat k).
  - exact (@R_in_map_bv_bnat k).
  - exact (@R_in_mapK_bv_bnat k).
Defined.

Definition Param44_bnat_bv_d {k : nat} :
  Param44.Rel (bounded_nat k) (bitvector k).
Proof.
  unshelve econstructor.
  - exact (@R_bnat_bv k).
  - exact (@Map4_bnat_bv k).
  - exact (@Map4_bv_bnat k).
Defined.

Definition Param44_bnat_bv (k k' : nat) (kR : natR k k') :
  Param44.Rel (bounded_nat k) (bitvector k').
Proof.
  unshelve eapply (@Param44_trans _ (bitvector k) _).
  - exact Param44_bnat_bv_d.
  - exact (Vector.Param44 bool bool Param44_bool k k' kR).
Defined.

Definition Param2a0_bnat_bv (k k' : nat) (kR : natR k k') :
  Param2a0.Rel (bounded_nat k) (bitvector k') :=
    Param44_bnat_bv k k' kR.

(* operations to get and set bits *)

Axiom setBit_bv : forall {k : nat}, bitvector k -> nat -> bool -> bitvector k.
Axiom setBit_bnat : forall {k : nat}, bounded_nat k -> nat -> bool -> bounded_nat k.
Axiom getBit_bv : forall {k : nat}, bitvector k -> nat -> bool.
Axiom getBit_bnat : forall {k : nat}, bounded_nat k -> nat -> bool.

(* setBit_bnat ~ setBit_bv *)

Axiom setBitR :
  forall
    (k k' : nat) (kR : natR k k')
    (bn : bounded_nat k) (bv' : bitvector k') 
    (r : R_trans
          (@R_bnat_bv k) (Vector.Param44 bool bool Param44_bool k k' kR) bn bv')
    (n n' : nat) (nR : natR n n')
    (b b' : bool) (bR : boolR b b'),
      R_trans (@R_bnat_bv k) (Vector.Param44 bool bool Param44_bool k k' kR)
        (setBit_bnat bn n b) (setBit_bv bv' n' b').

(* getBit_bnat ~ getBit_bv *)

Axiom getBitR :
  forall
    (k k' : nat) (kR : natR k k')
    (bn : bounded_nat k) (bv' : bitvector k') 
    (r : R_trans
          (@R_bnat_bv k) (Vector.Param44 bool bool Param44_bool k k' kR) bn bv')
    (n n' : nat) (nR : natR n n'),
      boolR (getBit_bnat bn n) (getBit_bv bv' n').

(* lt ~ lt *)
Axiom Param10_lt :
  forall (n1 n1' : nat) (n1R : natR n1 n1') (n2 n2' : nat) (n2R : natR n2 n2'),
    Param10.Rel (n1 < n2)%nat (n1' < n2')%nat.

(* Trocq Use Param00_nat.
Trocq Use Param2a0_nat.
Trocq Use SR.
Trocq Use Rp00.
Trocq Use Rp2a0.
Trocq Use Rp02b.
Trocq Use Param_head.
Trocq Use Param_const.
Trocq Use Param01_paths. *)

Axiom setBitThenGetSame :
  forall {k : nat} (bv : bitvector k) (i : nat) (b : bool),
    (i < k)%nat -> getBit_bv (setBit_bv bv i b) i = b.

Definition Param2a0_bool : Param2a0.Rel bool bool := Param44_bool.
Definition Param02b_bool : Param02b.Rel bool bool := Param44_bool.

Trocq Use Param00_nat.
Trocq Use Param2a0_nat.
Trocq Use Param2a0_bool.
Trocq Use Param02b_bool.
Trocq Use Param2a0_bnat_bv.
Trocq Use getBitR.
Trocq Use setBitR.
Trocq Use Param01_paths.
Trocq Use Param10_lt.

Lemma setBitThenGetSame' :
  forall {k : nat} (bn : bounded_nat k) (i : nat) (b : bool),
    (i < k)%nat -> getBit_bnat (setBit_bnat bn i b) i = b.
Proof.
  trocq. intros k bv i b H. apply setBitThenGetSame. exact H.
Qed.
