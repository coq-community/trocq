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
Require Import HoTT_additions Hierarchy Param_nat.
Set Asymmetric Patterns.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Notation Unit := unit.

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
  - by case: _ / (R_in_map AR a a' aR) => <-.
Defined.

Definition R_in_mapK :
  forall
    (A A' : Type) (AR : Param44.Rel A A') (n n' : nat) (nR : natR n n')
    (v : t A n) (v' : t A' n') (vR : tR A A' AR n n' nR v v'),
      map_in_R A A' AR n n' nR v v' (R_in_map A A' AR n n' nR v v' vR) = vR.
Proof. Admitted.

Definition Param_nat_symK m n (nR : natR m n) : nR = Param_nat_sym (Param_nat_sym nR).
Proof. by elim: nR => //= {}m {}n mn emn; apply: ap. Defined.

Definition tR_sym_f {A A' : Type} (AR : A -> A' -> Type) {n n' : nat} (nR : natR n n')
  {v : t A n} {v' : t A' n'} :
      sym_rel (tR A A' AR n n' nR) v' v -> tR A' A (sym_rel AR) n' n (Param_nat_sym nR) v' v.
Proof. by elim=> //=; constructor. Defined.

Definition tR_sym_t {A A' : Type} (AR : A -> A' -> Type) {n n' : nat} (nR : natR n n')
   {v' : t A' n'} {v : t A n} :
    tR A A' AR n n' (Param_nat_sym (Param_nat_sym nR)) v v' -> tR A A' AR n n' nR v v'.
Proof.
apply: (transport (fun nR => tR _ _ _ _ _ nR _ _)).
  symmetry; exact: Param_nat_symK.
Defined.

Definition tR_sym_tV {A A' : Type} (AR : A -> A' -> Type) {n n' : nat} (nR : natR n n')
   {v' : t A' n'} {v : t A n} :
    tR A A' AR n n' nR v v' -> tR A A' AR n n' (Param_nat_sym (Param_nat_sym nR)) v v'.
Proof.
apply: (transport (fun nR => tR _ _ _ _ _ nR _ _)).
exact: Param_nat_symK.
Defined.

(* Definition tR_symK  *)
Lemma tR_sym_tK A A' AR n n' nR v v' (vR : tR A A' AR n n'
   (Param_nat_sym (Param_nat_sym nR)) v v') :
      tR_sym_tV AR nR (tR_sym_t AR nR vR) = vR.
Proof.
by rewrite /tR_sym_t /tR_sym_tV -transport_pp concat_Vp.
Defined.

Local Notation f := (tR_sym_f _ _).
Local Notation g := (tR_sym_t _ _).
Local Notation h := (tR_sym_tV _ _).

Definition tR_sym_fK {A A' : Type} (AR : A -> A' -> Type) {n n' : nat} (nR : natR n n')
  (v : t A n) (v' : t A' n') (vR : tR A A' AR n n' nR v v') :
     g (f (f vR)) = vR.
Proof.
elim: vR => // {}n {}n' {}nR a a' aR {}v {}v' vR {2}<-/=.
Fail by case: _ / Param_nat_symK (f _).
admit.
Admitted.

Definition tR_sym_fE {A A' : Type} (AR : A -> A' -> Type) {n n' : nat} (nR : natR n n')
  (v : t A n) (v' : t A' n') (vR : tR A A' AR n n' nR v v') :
     f vR = g (f (h vR)).
Proof. by rewrite -{2}[vR]tR_sym_fK tR_sym_tK tR_sym_fK. Qed.

Definition tR_sym  (A A' : Type) (AR : A -> A' -> Type) (n n' : nat) (nR : natR n n')
   (v' : t A' n') (v : t A n) :
      sym_rel (tR A A' AR n n' nR) v' v <->> tR A' A (sym_rel AR) n' n (Param_nat_sym nR) v' v.
Proof.
  unshelve eexists _, _.
  - exact: tR_sym_f.
  - move/tR_sym_f/tR_sym_t; exact.
  - by move=> vR /=; rewrite tR_sym_fK.
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
