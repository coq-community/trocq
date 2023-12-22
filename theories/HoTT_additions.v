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

From Coq Require Import ssreflect ssrfun ssrbool.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.


(* Definition equiv_forall_sigma {A : Type} {P : A -> Type} {Q : forall a, P a -> Type} : *)
(*   (forall a (b : P a), Q a b) <~> forall x : { a : A | P a }, Q x.1 x.2. *)
(* Proof. *)
(* unshelve econstructor. { move=> f [a b]; exact (f a b). } *)
(* unshelve econstructor. { move=> g a b; exact (g (a; b)). } *)
(* all: constructor. *)
(* Defined. *)

(* Lemma equiv_invK {A B} (e : A <~> B) x : e (e^-1%equiv x) = x. *)
(* Proof. by case: e => [f []]. Defined. *)

(* Lemma equiv_funK {A B} (e : A <~> B) x : e^-1%equiv (e x) = x. *)
(* Proof. by case: e => [f []]. Defined. *)

(* Definition IsFun {A B : Type@{i}} (R : A -> B -> Type@{i}) := *)
(*   (forall x, Contr {y | R x y}). *)

(* Fact isfun_isprop `{Funext} {A B : Type@{i}} (R : A -> B -> Type@{i}) : *)
(*   IsHProp (IsFun R). *)
(* Proof. typeclasses eauto. Defined. *)

(* Lemma fun_isfun {A B : Type@{i}} (f : A -> B) : IsFun (fun x y => f x = y). *)
(* Proof. by move=> x; eexists (f x; 1%path) => -[y]; elim. Defined. *)

Definition sym_rel@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := fun b a => R a b.

(* Lemma isequiv_isfun `{Univalence} {A B : Type@{i}} (f : A -> B) : *)
(*   IsEquiv f <~> IsFun (fun x y => f y = x). *)
(* Proof. by symmetry; apply equiv_contr_map_isequiv. Defined. *)

(* Lemma type_equiv_contr `{Univalence} {A : Type@{i}} : *)
(*   A <~> {P : A -> Type | Contr {x : A & P x}}. *)
(* Proof. *)
(* apply equiv_inverse; unshelve eapply equiv_adjointify. *)
(* - move=> [F [[a ?] ?]]; exact a. *)
(* - by move=> a; exists (paths a); apply contr_basedpaths. *)
(* - done. *)
(* - move=> [P Pc]; unshelve eapply path_sigma. { *)
(*     apply: path_arrow => a; apply: equiv_path_universe. *)
(*     apply: equiv_inverse; apply: equiv_path_from_contr. *)
(*     by case: Pc => -[]. } *)
(*   by apply: path_contr. *)
(* Defined. *)

(* Lemma fun_equiv_isfun `{Univalence} {A B : Type} : *)
(*   (A -> B) <~> {R : A -> B -> Type | IsFun R}. *)
(* Proof. *)
(* have fe : Funext by apply: Univalence_implies_Funext. *)
(* transitivity (A -> {P : B -> Type | Contr {y : B & P y}}). *)
(*   { apply: equiv_postcompose'; exact type_equiv_contr. } *)
(* by apply (equiv_composeR' (equiv_sig_coind _ _)^-1). *)
(* Defined. *)

(* Lemma equiv_sig_relequiv `{Univalence} {A B : Type@{i}} : *)
(*   (A <~> B) <~> RelEquiv A B. *)
(* Proof. *)
(* apply (equiv_composeR' (issig_equiv _ _)^-1). *)
(* apply (equiv_compose' issig_relequiv). *)
(* apply (equiv_compose' (equiv_sigma_assoc' _ _)^-1). *)
(* unshelve eapply equiv_functor_sigma. *)
(* - exact: fun_equiv_isfun. *)
(* - by move=> f; apply: isequiv_isfun. *)
(* - exact: equiv_isequiv. *)
(* - by move=> f; apply: equiv_isequiv. *)
(* Defined. *)

(* Definition apD10_path_forall_cancel `{Funext} : *)
(*   forall {A : Type} {B : A -> Type} {f g : forall x : A, B x} (p : forall x, f x = g x), *)
(*     apD10 (path_forall f g p) = p. *)
(* Proof. *)
(*   intros. unfold path_forall. *)
(*   apply moveR_equiv_M. *)
(*   reflexivity. *)
(* Defined. *)

(* Definition transport_apD10 : *)
(*   forall {A : Type} {B : A -> Type} {a : A} (P : B a -> Type) *)
(*          {t1 t2 : forall x : A, B x} {e : t1 = t2} {p : P (t1 a)}, *)
(*     transport (fun (t : forall x : A, B x) => P (t a)) e p = *)
(*     transport (fun (t : B a) => P t) (apD10 e a) p. *)
(* Proof. *)
(*   intros A B a P t1 t2 [] p; reflexivity. *)
(* Defined. *)

(* Definition coe_inverse_cancel {A B} (e : A = B) p: coe e (coe e^ p) = p. *)
(* Proof. elim: e p; reflexivity. Defined. *)

(* Definition coe_inverse_cancel' {A B} (e : A = B) p :  coe e^ (coe e p) = p. *)
(* Proof. elim: e p; reflexivity. Defined. *)

(* Definition path_forall_types `{Funext} A F G : *)
(*   (forall (a : A), F a = G a) -> (forall a, F a) = (forall a, G a). *)
(* Proof. by move=> /(path_forall _ _)->. Defined. *)

(* Definition equiv_flip@{i k | i <= k} : *)
(* 	forall (A B : Type@{i}) (P : A -> B -> Type@{k}), *)
(*     Equiv@{k k} (forall (a : A) (b : B), P a b) (forall (b : B) (a : A), P a b). *)
(* Proof. *)
(*   intros A B P. *)
(*   unshelve eapply Build_Equiv@{k k}. *)
(*   - exact (@flip@{i i k} A B P). *)
(*   - by unshelve eapply *)
(*       (@Build_IsEquiv@{k k} *)
(*         (forall (a : A) (b : B), P a b) (forall (b : B) (a : A), P a b) *)
(*         (@flip@{i i k} A B P) *)
(*         (@flip@{i i k} B A (fun (b : B) (a : A) => P a b))). *)
(* Defined. *)


Reserved Notation "p ^" (at level 3, format "p '^'").
Reserved Notation "p @ q" (at level 20).
Reserved Notation "p # x" (right associativity, at level 65).
Reserved Notation "p # x" (right associativity, at level 65).
Reserved Notation "p @@ q" (at level 20).
Reserved Notation "p @' q" (at level 21, left associativity,
  format "'[v' p '/' '@''  q ']'").
Reserved Notation "f == g" (at level 70, no associativity).
Reserved Notation "g 'o' f" (at level 40, left associativity).


Notation "f == g" := (forall x, f x = g x).
Notation "g 'o' f" := ((fun g0 f0 x => g0 (f0 x)) g f).

Declare Scope fibration_scope.
Open Scope fibration_scope.

Notation "( x ; y )" := (existT _ x y) : fibration_scope.

Reserved Notation "x .1" (at level 2, left associativity, format "x '.1'").
Reserved Notation "x .2" (at level 2, left associativity, format "x '.2'").

Notation pr1 := projT1.
Notation pr2 := projT2.

(** The following notation is very convenient, although it unfortunately clashes with Proof General's "electric period".  We have added [format] specifiers in Notations.v so that it will display without an extra space, as [x.1] rather than as [x .1]. *)
Notation "x .1" := (pr1 x) : fibration_scope.
Notation "x .2" := (pr2 x) : fibration_scope.

Notation paths := eq.
Notation idpath := eq_refl.

Notation eq := paths.
Notation eq_refl := idpath.
Notation inverse := eq_sym.
Notation concat := eq_trans.
Notation "x = y" := (Logic.eq x y) : type_scope.

Lemma transport {A : Type} (P : A -> Type) {x y : A} : x = y -> P x -> P y.
Proof. move->; exact. Defined.

Lemma paths_rect (A : Type) (a : A) (P : forall a0 : A, a = a0 -> Type) :
  P a idpath -> forall (a0 : A) (p : a = a0), P a0 p.
Proof. by move=> pa b; case: _ /. Defined.

Reserved Notation "A <=> B" (at level 70, no associativity). 
Notation "A <--> B" := ((A -> B) * (B -> A))%type (at level 70) : fibration_scope.
Notation "A <->> B" := {f : A -> B & { g : B -> A & forall x, g (f x) = x}} (at level 70) : fibration_scope.
Notation id := (fun x => x).
Notation idmap := (fun x => x).

Declare Scope path_scope.
Delimit Scope path_scope with path.
Bind Scope path_scope with paths.
Notation "1" := idpath : path_scope.
Notation "e ^" := (eq_sym e%path) : path_scope.
Notation "p @ q" := (eq_trans p q) : path_scope.
Open Scope path_scope.

Definition inv_V {A : Type} {x y : A} (p : x = y) : (p^)^ = p :=
  match p with idpath => 1 end.

(* relation for forall *)
Monomorphic Axiom Funext : Prop.
Existing Class Funext.
Axiom path_forall@{i j} : forall `{Funext} {A : Type@{i}} {P : A -> Type@{j}} 
  (f g : forall x : A, P x), f == g -> f = g.
Global Arguments path_forall {_ A%type_scope P} (f g)%function_scope _.

Lemma path_arrow `{Funext} {A B : Type} (f g : A -> B) :
  f == g -> f = g.
Proof. apply path_forall. Defined.

Definition equiv_flip@{i k} (A B : Type@{i}) (P : A -> B -> Type@{k}) :
(forall (a : A) (b : B), P a b) <->> (forall (b : B) (a : A), P a b).
Proof. by do 2!exists (fun PAB b a => PAB a b). Defined.

Definition ap := f_equal.
Arguments ap {A B} f {x y}.

Definition inverse2 {A : Type} {x y : A} {p q : x = y} : p = q -> p^ = q^.
Proof. exact: ap. Defined.

Lemma concat_p1 {A : Type} {x y : A} (p : x = y) : p @ 1 = p.
Proof. reflexivity. Defined.

Lemma concat_1p {A : Type} {x y : A} (p : x = y) : 1 @ p = p.
Proof. by case: _ / p. Defined.

Lemma moveL_1V {A : Type} {x y : A} (p : x = y) (q : y = x) :
  p @ q = 1%path -> p = q^.
Proof. by case: _ / q p. Defined.

Lemma moveR_pM {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  r = q @ p^ -> r @ p = q.
Proof. by case: _ / p q r. Defined.

Lemma transport_pp@{i j} {A : Type@{i}} (P : A -> Type@{j})
    {x y z : A} (p : x = y) (q : y = z) (u : P x) :
  transport P (p @ q) u = transport P q (transport P p u).
Proof.
case: _ / q.
done.
Defined.

Lemma concat_pV@{i} {A : Type@{i}} {x y : A} (p : x = y) : p @ p^ = 1%path.
Proof. by case: _ / p. Defined.

Lemma concat_Vp@{i} {A : Type@{i}} {x y : A} (p : x = y) : p^ @ p = 1%path.
Proof. by case: _ / p. Defined.

Reserved Notation "n .+1" (at level 2, left associativity, format "n .+1").
Reserved Notation "n .+2" (at level 2, left associativity, format "n .+2").
Reserved Notation "n .+3" (at level 2, left associativity, format "n .+3").
Reserved Notation "n .+4" (at level 2, left associativity, format "n .+4").
Reserved Notation "n .+5" (at level 2, left associativity, format "n .+5").
Reserved Notation "n '.-1'" (at level 2, left associativity, format "n .-1").
Reserved Notation "n '.-2'" (at level 2, left associativity, format "n .-2").
Reserved Notation "m +2+ n" (at level 50, left associativity).
Reserved Infix "mod" (at level 40, no associativity).
Reserved Notation "p ~ 1" (at level 7, left associativity, format "p '~' '1'").
Reserved Notation "p ~ 0" (at level 7, left associativity, format "p '~' '0'").
