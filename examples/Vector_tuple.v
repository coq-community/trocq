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

Axiom cheat : forall A, A.
Ltac cheat := apply cheat.

Module Vector.

Inductive t (A : Type) : nat -> Type :=
  | nil : t A 0
  | cons : forall (n : nat), A -> t A n -> t A (S n).
Arguments nil {_}.
Arguments cons {_ _}.

Definition t_nat_param_rect {A : Type} (P : forall (n n' : nat), natR n n' -> t A n -> Type) :
  P O O OR nil ->
  (forall (n n' : nat) (nR : natR n n') (a : A) (v : t A n), P n n' nR v -> P (S n) (S n') (SR n n' nR) (cons a v)) ->
  forall (n n' : nat) (nR : natR n n') (v : t A n), P n n' nR v.
Proof.
  intros P0 PS n n' nR v.
  cheat.
Defined.

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

Definition map_in_R :
  forall
    (A A' : Type) (AR : Param2a0.Rel A A') (n n' : nat) (nR : natR n n')
    (v : t A n) (v' : t A' n'),
      map A A' AR n n' nR v = v' -> tR A A' AR n n' nR v v'.
Proof.
  intros A A' AR n n' nR v v' e.
  induction e.
  apply (t_nat_param_rect (fun n n' nR v => tR A A' AR n n' nR v (map A A' AR n n' nR v))).
  - apply nilR.
  - intros m m' mR a v' r.
    apply consR.
    + exact (map_in_R AR a (Hierarchy.map AR a) idpath).
    + exact r.
Defined. 
  
Definition R_in_map :
  forall
    (A A' : Type) (AR : Param2b0.Rel A A') (n n' : nat) (nR : natR n n')
    (v : t A n) (v' : t A' n'),
      tR A A' AR n n' nR v v' -> map A A' AR n n' nR v = v'.
Proof.
  intros A A' AR n n' nR v v' vR.
  induction vR.
  - simpl. reflexivity.
  - simpl.
    elim (R_in_map AR a a' aR).
    elim IHvR.
    reflexivity.
Defined.

Definition R_in_mapK :
  forall
    (A A' : Type) (AR : Param44.Rel A A') (n n' : nat) (nR : natR n n')
    (v : t A n) (v' : t A' n') (vR : tR A A' AR n n' nR v v'),
      map_in_R A A' AR n n' nR v v' (R_in_map A A' AR n n' nR v v' vR) = vR.
Proof.
  intros A A' AR n n' nR v v' vR.
  cheat.
Defined.

Definition tR_sym
  (A A' : Type) (AR : A -> A' -> Type) (n n' : nat) (nR : natR n n')
  (v' : t A' n') (v : t A n) :
      sym_rel (tR A A' AR n n' nR) v' v <~> tR A' A (sym_rel AR) n' n (Param_nat_sym nR) v' v.
Proof.
  unfold sym_rel.
  unshelve eapply equiv_adjointify.
  - intro vR. induction vR.
    + simpl. apply Vector.nilR.
    + simpl. apply Vector.consR.
      * exact aR.
      * exact IHvR.
  - intro vR.
    (* induction nR/vR *)
    cheat.
  - cheat.
  - cheat.
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

Definition tuple_vectorR {A : Type} {n : nat} : tuple A n -> Vector.t A n -> Type :=
  fun t v => tuple_to_vector t = v.

Definition map_in_R_tv {A : Type} {n : nat} (t : tuple A n) (v : Vector.t A n) :
  tuple_to_vector t = v -> tuple_vectorR t v := id.

Definition R_in_map_tv {A : Type} {n : nat} (t : tuple A n) (v : Vector.t A n) :
  tuple_vectorR t v -> tuple_to_vector t = v := id.

Definition R_in_mapK_tv
  {A : Type} {n : nat} (t : tuple A n) (v : Vector.t A n) (r : tuple_vectorR t v) :
    map_in_R_tv t v (R_in_map_tv t v r) = r := idpath.

Definition Map4_tuple_vector_d (A : Type) (n : nat) : Map4.Has (@tuple_vectorR A n).
Proof.
  unshelve econstructor.
  - exact (@tuple_to_vector A n).
  - exact (@map_in_R_tv A n).
  - exact (@R_in_map_tv A n).
  - exact (@R_in_mapK_tv A n).
Defined.

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
    
Definition map_in_R_vt {A : Type} {n : nat} (v : Vector.t A n) (t : tuple A n) :
  vector_to_tuple v = t -> tuple_vectorR t v.
Proof.
  unfold tuple_vectorR.
  intro e.
  apply (transport (fun x => tuple_to_vector x = v) e).
  apply vector_to_tupleK.
Defined.

Definition R_in_map_vt {A : Type} {n : nat} (v : Vector.t A n) (t : tuple A n) :
  tuple_vectorR t v -> vector_to_tuple v = t.
Proof.
  unfold tuple_vectorR.
  intro e.
  apply (transport (fun x => vector_to_tuple x = t) e).
  apply tuple_to_vectorK.
Defined.

Definition R_in_mapK_vt {A : Type} :
  forall {n : nat} (v : Vector.t A n) (t : tuple A n) (r : tuple_vectorR t v),
    map_in_R_vt v t (R_in_map_vt v t r) = r.
Proof.
  induction n.
  - simpl. intros v t r. destruct r. simpl. cheat.
  - simpl. intros v [t' a] []. simpl. cheat.
Defined.

Definition Map4_vector_tuple_d (A : Type) (n : nat) : Map4.Has (sym_rel (@tuple_vectorR A n)).
Proof.
  unshelve econstructor.
  - exact (@vector_to_tuple A n).
  - exact (@map_in_R_vt A n).
  - exact (@R_in_map_vt A n).
  - exact (@R_in_mapK_vt A n).
Defined.

Definition Param44_tuple_vector_d (A : Type) (n : nat) : Param44.Rel (tuple A n) (Vector.t A n).
Proof.
  unshelve econstructor.
  - exact (@tuple_vectorR A n).
  - exact (Map4_tuple_vector_d A n).
  - exact (Map4_vector_tuple_d A n).
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

Definition Param_append :
  forall
    (A A' : Type) (AR : Param00.Rel A A')
    (n1 n1' : nat) (n1R : natR n1 n1') (n2 n2' : nat) (n2R : natR n2 n2')
    (t1 : tuple A n1) (v1 : Vector.t A' n1')
    (tv1R : tuple_vectorR A A' AR n1 n1' n1R t1 v1)
    (t2 : tuple A n2) (v2 : Vector.t A' n2')
    (tv2R : tuple_vectorR A A' AR n2 n2' n2R t2 v2),
    tuple_vectorR
      A A' AR (n1 + n2) (n1' + n2') (Param_add n1 n1' n1R n2 n2' n2R)
        (append t1 t2) (Vector.append v1 v2).
Proof.
  intros A A' AR n1 n1' n1R n2 n2' n2R t1 v1 tv1R.
  induction tv1R.
  - simpl. exact (fun t2 v2 tv2R => tv2R).
  - simpl.
    intros t2 v2 tv2R.
    unfold tuple_vectorR in *.
    Check Vector.consR A A' AR
      (n + n2).+1 (n' + n2').+1 (SR (n + n2) (n' + n2') (Param_add n n' nR n2 n2' n2R))
    .
    cheat.
Defined.

Definition Param_const
  (A A' : Type) (AR : Param00.Rel A A') (a : A) (a' : A') (aR : AR a a')
  (n n' : nat) (nR : natR n n') :
    tuple_vectorR A A' AR n n' nR (const a n) (Vector.const a' n').
Proof.
  cheat.
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
