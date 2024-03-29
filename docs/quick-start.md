# Trocq tutorial

This tutorial is an introduction to Trocq, covering several examples from the repository from the user's point of view.
First, we present the use of Trocq to perform proof transfer along type equivalence relations.
Then, we handle the case of weaker, directed relations.
Finally, we give several examples of multiple transfer featuring polymorphic and dependent containers.

## Proof transfer with type isomorphisms

In this first section, we show two examples of isomorphisms: natural numbers with unary and binary representations, and bitvectors.

?> Here, we also introduce details about the internals of Trocq relations, so that users understand better what they contain and how they are built and declared in the plugin.

### Unary and binary natural numbers

Natural numbers are often manipulated in Coq using the standard `nat` type encoding them in the Peano style, *i.e.* a unary representation with a zero (`O`) and a successor (`S`):

```coq
Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.
```

However, this mathematical concept can also be encoded in a binary fashion, which can be interesting for some proofs:

```coq
Inductive positive : Set :=
  | xI : positive -> positive
  | xO : positive -> positive
  | xH : positive.

Inductive N : Set :=
  | N0 : N
  | Npos : positive -> N.
```

A binary natural number of type `N` is either zero (`N0`) or a `positive` binary number (`Npos`) composed of a sequence of digits (`xI` and `xO`), starting from the least significant byte and always ending with a one (`xH`).

Both `nat` and `N` types come with an induction principle generated by Coq.
However, as the structures of these types are very different, the induction is performed in a very different way as well:

```coq
nat_rect : forall (P : nat -> Type),
  P O -> (forall (n : nat), P n -> P (S n)) -> forall (n : nat), P n
```
```coq
N_rect : forall (P : N -> Type),
  P N0 -> (forall (p : positive), P (Npos p)) -> forall (n : N), P n

positive_rect : forall (P : positive -> Type),
  (forall (p : positive), P p -> P (xI p)) ->
  (forall (p : positive), P p -> P (xO p)) ->
  P xH ->
    forall (p : positive), P p
```

If we want to perform a proof by induction on the binary representation of natural numbers, but reasoning with a successor-based recurrence scheme, we need to prove an induction principle on `N` similar to `nat_rect`:

```coq
Lemma N_Srect : forall (P : N -> Type),
  P N0 -> (forall (n : N), P n -> P (N_succ n) -> forall (n : N), P n.
Proof. Fail apply nat_rect. Abort.
```

Unfortunately, `nat_rect` cannot be used directly to prove `N_Srect` here, since the types of the induction principles cannot be unified.
Indeed, by default, Coq does not know `N` and `nat` represent the same concept, and that the zero and successors of `N` are associated to the ones of `nat`.

Trocq can bridge this gap if we give it the required information.
First, we need to relate `N` to `nat`.

#### Type relations

Trocq can work with various structures on relations between types, ranging from raw relations (in our case, of type `N -> nat -> Type`) to full type equivalences.
They are represented as a `ParamXY.Rel` record containing a relation and two unilateral sub-records representing the structure given to this relation in both ways (here, level `X` from `A` to `B`, and level `Y` from `B` to `A`):
```coq
ParamXY.Rel A B := {
  R : A -> B -> Type;
  covariant : MapX.Has R;
  contravariant : MapY.Has R^-1;
}
```
A unilateral sub-record is given by a number of fields chosen from an inclusive hierarchy, where a level contains fields for which there exists a path to the associated node in the following graph:

<p style="text-align: center"><img src="hierarchy.jpeg" alt="Hierarchy" width="80%" /></p>

For instance, here are the declarations of levels `4`, `2a` and `0`:

```coq
Map4.Has (R : A -> B -> Type) := {
  map : A -> B;
  map_in_R : forall (a : A) (b : B), map a = b -> R a b;
  R_in_map : forall (a : A) (b : B), R a b -> map a = b;
  R_in_mapK : forall (a : A) (b : B) (r : R a b), (map_in_R a b (R_in_map a b r)) = r
}

Map2a.Has R := {
  map : A -> B;
  map_in_R : forall (a : A) (b : B), map a = b -> R a b;
}

Map0.Has R := {}
```

?> Level `(4,4)` of the hierarchy is equivalent to type equivalence in HoTT, and if this level is used everywhere, Trocq performs a [univalent parametricity](https://dl.acm.org/doi/abs/10.1145/3429979) translation. Level `(0,0)` of the hierarchy corresponds to a structure-less relation, and if this level is used everywhere, the parametricity translation is the raw parametricity translation (*e.g.*, [here](https://arxiv.org/abs/1209.6336)) that can be found in other plugins such as [derive](https://github.com/LPCIC/coq-elpi/tree/master/apps/derive) or [ParamCoq](https://github.com/coq-community/paramcoq). The remaining levels encode for finer-grained relations, including directed relations.

For the most commonly used structures (*i.e.*, isomorphisms, sections and retractions), we provide dedicated modules in `Common.v` to create `Param` records more easily.
For example, there exists an isomorphism between `N` and `nat` given by two inverse functions:
```coq
Definition N_to_nat : N -> nat.
Definition N_of_nat : nat -> N.

Theorem N_to_natK : forall (n : N), N_of_nat (N_to_nat n) = n.
Theorem N_of_natK : forall (n : nat), N_to_nat (N_of_nat n) = n.
```

Such functions and properties can be packed into an `Iso` record and given to Trocq after conversion to a `Param44.Rel` record describing a type equivalence:
```coq
Definition N_nat_iso : Iso.type N nat := Iso.Build N_to_natK N_of_natK.

Definition N_nat_R : Param44.Rel N nat := Iso.toParam N_nat_iso.
Trocq Use N_nat_R.
```

In order to perform proof transfer for `N_Srect`, we need to declare in Trocq all the remaining constants appearing in the goal, that is, `N0` and `N_succ`.

#### Operations and constants

According to the abstraction theorem of parametricity, the required type of the proofs to give to relate a constant `k : T` to a constant `k' : T'` is `TR k k'`, with `TR` being the relation existing between `T` and `T'` (*i.e.*, the `R` field inside a record, declared in Trocq, of type `ParamXY.Rel T T'`).
We can use this theorem to know what we need to prove to relate our source and target constants.

!> In the future, Trocq is expected to generate the expected goal on its own, so that the user does not need to know the abstraction theorem, but only the two terms they want to relate together, but it is currently not the case yet.

Therefore, the constant `N0 : N` must be related to a constant `?k' : nat` by a proof `?r : N_nat_R N0 ?k'`.
Here, `?k' := O` and `?r` is the following term, added to Trocq:
```coq
Definition N0_O_R : N_nat_R N0 O. (* === N_to_nat N0 = O *)
Trocq Use N0_O_R.
```

?> Here, we see that thanks to a coercion, `N_nat_R` can be used either as a record or a projection on the raw relation contained in its `R` field.

Following the same logic, the constant `N_succ : N -> N` is related to `S : nat -> nat` by the following proof:
```coq
Definition Nsucc_S_R : forall (n : N) (n' : nat) (nR : N_nat_R n n'), (* === N_to_nat n = n' *)
  N_nat_R (N_succ n) (S n'). (* === N_to_nat (N_succ n) = S n' *)
Trocq Use Nsucc_S_R.
```

Now, Trocq can be used in proof mode through the `trocq` tactic, and the `nat_rect` proof can be reused for `N_Srect`:
```coq
Lemma N_Srect : forall (P : N -> Type),
  P N0 -> (forall (n : N), P n -> P (N_succ n) -> forall (n : N), P n.
Proof.
  trocq.
(* forall (P : nat -> Type), P O -> (forall (n : nat), P n -> P (S n)) -> forall (n : nat), P n *)
  exact nat_rect.
Qed.
```

?> A careful analysis shows that in order to transfer this goal to `nat`, only information up to level `(2a,3)` in `N_nat_R` was used. It means that we could have only proved `N_to_natK` and the transfer would still have been possible. A way to declare the minimal amount of information is to run `trocq` without adding any information, and follow the error message asking for a specific level, until all the requirements are met and the tactic succeeds.

### Bounded natural numbers and bitvectors

Trocq supports the whole syntax of CCω, including dependent types.
In this second example, we relate bitvectors encoded as bounded natural numbers with bitvectors encoded as fixed-size bit sequences:
```coq
Definition bounded_nat (k : nat) := {n : nat & n < 2^k}.
Definition bitvector (k : nat) := Vector.t bool k.
```

The required type of the Trocq relation between these type formers is the following:
```coq
forall (k k' : nat) (kR : natR k k'), ParamXY.Rel (bounded_nat k) (bitvector k')
```
for a given level `(X,Y)`, with `natR : nat -> nat -> Type` a term relating `nat` to itself.
Indeed, in this example, we can see that the length of the bitvector is expressed in `nat` for both encodings, meaning this type will not change during the translation.
Moreover, we can see that one of the encodings uses the standard `Vector.t` type.
We can exploit this by using the following proofs declared in `Param_nat.v` and `Param_vector.v` in Trocq:
```coq
Param44_nat : Param44.Rel nat nat.
Vector.Param44 :
  forall (A A' : Type), Param44.Rel A A' ->
  forall (n n' : nat), natR n n' ->
    Param44.Rel (Vector.t A n) (Vector.t A' n').
```

We will relate both encodings at level `(4,4)` because there is an equivalence between them.

#### Proving equivalence of the encodings

?> Here, `natR` is the default binary inductive parametricity relation between `nat` and itself. It is used as the `R` field in `Param44_nat`, so in the type of `Vector.Param44`, we can write `Param44_nat n n'` or `natR n n'`, at the difference that `natR` applies in all contexts whereas writing `Param44_nat` is only possible when we relate `nat` to itself at level `(4,4)`.

Therefore, in order to prove that `bounded_nat k` is related to `bitvector k'`, we can use `Vector.Param44` to relate `Vector.t bool k` to `Vector.t bool k'` (note that we also use the reflexive relation `Param44_bool` from `Param_bool.v` in this case), and we only have to prove that `bounded_nat k` is related to `Vector.t bool k` for a fixed `k`, which is supposedly easier for the user.
We will then use the following transitivity lemma to combine both proofs into the expected term:
```coq
Lemma Param44_trans : forall (A B C : Type),
  Param44.Rel A B -> Param44.Rel B C -> Param44.Rel A C.
```

The user therefore has to give two functions to switch between both encodings.
One of them has to recursively divide the natural number by 2 to get the value of each bit one by one:
```coq
Definition bnat_to_bv {k : nat} : bounded_nat k -> bitvector k.
```
The other one has to traverse the bitvector bit by bit, multiplying the accumulator by 2 at every step.
As the output type is a dependent pair, we also need a proof that the result of this operation is bounded :
```coq
Definition bv_to_nat : forall {k : nat}, bitvector k -> nat.
Theorem bv_to_nat_bound {k : nat} : forall (v : bitvector k), bv_to_nat v < 2^k.
```

After proving the additional properties of the hierarchy about these conversion functions, we obtain the relation for a given `k`, which can be used to prove the more general relation right below:
```coq
Definition Param44_bnat_bv_d {k : nat} : Param44.Rel (bounded_nat k) (bitvector k).
Definition Param44_bnat_bv : forall (k k' : nat), natR k k' ->
  Param44.Rel (bounded_nat k) (bitvector k').
```
```coq
Trocq Use Param44_bool Param44_nat Param44_bnat_bv.
```

#### Proof transfer for bitvectors

Let us take an example of property we can prove about bitvectors: if we set a cell to a value, then reading this cell right after yields the same value.
```coq
Theorem set_x_get_x {k : nat} :
  forall (v : bitvector k) (i : nat) (b : bool), i < k ->
    get (set v i b) i = b.
```

This assumes the existence of two functions to manipulate bitvectors:
```coq
Definition set {k : nat} : bitvector k -> nat -> bool -> bitvector k.
Definition get {k : nat} : bitvector k -> nat -> bool.
```

We will proceed as in the previous example, *i.e.*, find all constants involved in this goal and declare them in Trocq.
In addition to finding counterparts for `set` and `get` on `bounded_nat`, we need to relate the order relation over `nat` and equality to their counterparts, that are exactly themselves, as they do not change during the translation.

According to the abstraction theorem, the type for the proof relating `get` to its counterpart we will call `getn` is the following:
```coq
Lemma getR :
  forall (k k' : nat) (kR : natR k k'),
  forall (n : bounded_nat k) (v' : bitvector k'), Param44_bnat_bv k k' kR n v' ->
  forall (i i' : nat), natR i i' ->
    boolR (getn n i) (get v' i').
Trocq Use getR setR.
```
?> Here, we relate `getn` to `get` in this way, because we want to rephrase `getn` as `get` in the goal expressed with `bounded_nat` to exploit the previous result obtained on the `bitvector` encoding.

Here is the goal we want to transfer now:
```coq
Lemma set_x_get_x_bn {k : nat} :
  forall (n : bounded_nat k) (i : nat) (b : bool), i < k ->
    getn (setn n i b) = b.
```

If we run `trocq` before adding anything about the order (`lt`) or the equality (`paths`), Trocq will complain about it and tell us the level of the relation we need to prove:
```text
cannot find const «lt» at out class pc map0 map1
cannot find const «paths» at out class pc map0 map1
```
Trocq tells us that both of them are required at level `(0,1)`.
Here is, for instance, the proof that we need to register for `lt`:
```coq
Definition Param10_lt :
  forall (n1 n1' : nat), natR n1 n1' ->
  forall (n2 n2' : nat), natR n2 n2' ->
    Param10.Rel (n1 < n2) (n1' < n2').
Trocq Use Param10_lt.
```

Once everything is added into the Trocq database, the `trocq` tactic successfully rephrases the goal as the exact type of `set_x_get_x`, that we can apply to close the proof.
```coq
Proof. trocq. exact set_x_get_x. Qed.
```

## Using Trocq with directed relations (sections and retractions)

Trocq can also be used with relations that are weaker than an equivalence, for instance only a section or a retraction.
In this section, we give three examples: the embedding from `positive` to the `N` type that extends it with a zero, an axiomatised example of modular arithmetic, and an example of result about sums of sequences of reals involving an extension of reals with infinity.

### Positive and non-negative binary integers

We recall the definition of the type `N` of binary natural numbers:
```coq
Inductive N : Set :=
  | N0 : N
  | Npos : positive -> N.
```

Here, we can see that the `Npos` constructor is a trivial embedding function from `positive` to `N`, and we can easily define a function in the opposite way:
```coq
Definition N_to_pos (n : N) : positive :=
  match n with
  | Npos p => p
  | N0 => d
  end.
```
with `d : positive` a default value.
Indeed, `N_to_pos` performs a truncation on the zero value because `positive` does not have a zero.

One of the compositions of these functions is trivially an identity, and the other cannot be in the general case because of this truncation (the theorem is only conditionally true):
```coq
Theorem NposK : forall (p : positive), N_to_pos (Npos p) = p.
Theorem N_to_pos_condK : forall (n : N), n <> N0 -> Npos (N_to_pos n) = n.
```

As we have no isomorphism, the Trocq relation will live at a lower level than `(4,4)`.
More precisely, we can declare a split injection from `positive` to `N` with `NposK`, at level `(4,2b)`:
```coq
Definition pos_N_inj : SplitInj.type positive N := SplitInj.Build NposK.
Definition pos_N_R : Param42b.Rel positive N := SplitInj.toParam pos_N_inj.
Trocq Use pos_N_R.
```

?> Because of this lower level, Trocq will not be able to transfer all goals involving `positive` to goals expressed with `N`. Some of these goals are impossible to prove from a more general result anyway. Note that conditional identities such as `N_to_pos_condK` above are not currently supported by Trocq. They would indeed require adding a level to the hierarchy between `1` and `2b` (a conditional version of field `R_in_map`).

An example of theorem that could be proved for `positive` from the more general result on `N` is the commutativity of addition:
```coq
Lemma pos_add_comm : forall (p q : positive), p + q = q + p.
```
After relating in Trocq the addition over `positive` to its counterpart over `N`, and equality to itself, the tactic is able to transfer the goal and we can close the proof with the result on `N`:
```coq
Proof. trocq. apply N_add_comm. Qed.
```

### Modular arithmetic

It is possible to mix modular arithmetic and standard arithmetic by defining a type `Zmodp` of integers modulo a value and show it can be related to a general encoding of integers such as the standard library `Z`.

!> Note that parametricity relates terms whose types have the same structure, meaning that in the case of a type `Zmod p` dependent on an integer `p`, `Zmod` is a type former, and as such, it has to be related to another type former, which `Z` is not. Here, we make the choice of fixing `p` before defining `Zmodp`.

Here, we define two functions, one computing the modulo of an integer, the other computing a canonical integer value representing an integer in the modular space.
We also show that one of their compositions is an identity and from that, we can define a split surjection in Coq and add it to Trocq through the `SplitSurj` module:
```coq
Definition modp : Z -> Zmodp.
Definition reprp : Zmodp -> Z.
Theorem reprpK : forall (z : Zmodp), modp (reprp z) = z.
Definition Z_Zmodp_surj : SplitSurj.type Z Zmodp := SplitSurj.Build reprpK.
Definition Z_Zmodp_R : Param42a.Rel Z Zmodp := SplitSurj.toParam Z_Zmodp_surj.
Trocq Use Z_Zmodp_R.
```

?> To give a slightly different example, here we relate `Z` to `Zmodp`, aiming to rephrase a goal expressed with the bigger type `Z` as a goal expressed with `Zmodp`, instead of pulling the goal in the subtype back to a more general goal, as it was done for `positive` and `N` above.

If we define an equality over `Z` checking whether both values are congruent to each other modulo `p`, and use it in a general goal expressed with `Z`, if we relate it to a classic equality over `Zmodp`, Trocq can rephrase the general goal as a goal over `Zmodp` (we omit the details about multiplication and the zero here, as they have been covered in the previous examples):
```coq
Definition eqmodp (x y : Z) := modp x = modp y.
Definition eq_Zmodp (x y : Zmodp) := (x = y).
Theorem eq_mod_R :
  forall (m : Z) (x : Zmodp), Z_Zmodp_R m x ->
  forall (n : Z) (y : Zmodp), Z_Zmodp_R n y ->
    Param01.Rel (eqmodp m n) (eq_Zmodp x y).
Trocq Use eq_mod_R.
```

```coq
Goal forall (m n : Z), m = n * p -> eqmodp m 0.
  trocq; unfold eq_Zmodp.
  (* forall (m n : Zmodp), m = n * p -> m = 0 *)
  (* [...] (then we conclude the proof with a modular arithmetic argument) *)
Qed.
```

!> For the same reason as above (parametricity), `eqmodp` cannot directly be related to equality because they have different types: `eqmodp : Z -> Z -> Type` and `(=) : forall (A : Type), A -> A -> Type`. This is the reason for the `eq_Zmodp` redefinition here.

### Summable reals

!> Coming soon...

## Polymorphic and dependent container types

As shown in the first section of this tutorial, as Trocq has support for the whole syntax of CCω, in particular, it supports dependent types.
In this section, we show that this feature can be combined with the composition of parametricity proofs to perform proof transfer between polymorphic and dependent container types, and transfer both the container type and the type of the contents of the containers.
We present an equivalence between iterated tuples and vectors from the standard library, an embedding from options to lists, an example of composition of proofs presented previously in this tutorial, as well as an example of realistic use case of Trocq for refinements.

### Iterated tuples and vectors

In this example, we show Trocq can be used to switch between two polymorphic and dependent container types.

Although the standard library vector type is a widely used example for introducing dependent types, using it in realistic formalisation projects can have several drawbacks, including having to deal with the whole complexity of dependent types even for writing functions as simple as getting the head of the vector.
For practical reasons, an alternative is the iterated tuple, *i.e.*, `tuple A n` is a tuple of size `n` containing values of type `A`.
```coq
Definition tuple (A : Type) : nat -> Type :=
  fix F n :=
    match n with
    | O => unit
    | S k => F k * A
    end.
```
One of the advantages of this representation of fixed-size container is that `tuple A (S n)` is *convertible* to `tuple A n * A`, meaning the implementation of a `peek` function reading the outermost value is trivial:
```coq
Definition peek {A : Type} {n : nat} (t : tuple A (S n)) : A :=
  match t with (t', a) => a end.
```
whereas the implementation for vectors is more cumbersome:
```coq
Definition Vector.peek {A : Type} {n : nat} (v : Vector.t A (S n)) : A :=
  match v in t _ m
    return match m with O => unit | S _ => A end
  with
  | nil => tt
  | cons a _ => a
  end.
```
Let us also assume a `const` function on both representations, encoding for a constant container containing `n` times the same value:
```coq
Definition const {A : Type} (a : A) : forall (n : nat), tuple A n :=
  fix F n :=
    match n with
    | O => tt
    | S k => (F k, a)
    end.
```
```coq
Definition Vector.const {A : Type} (a : A) : forall (n : nat), Vector.t A n :=
  fix F n :=
    match n with
    | O => nil
    | S k => cons a (F k)
    end.
```

Now, as the standard library vector is more widespread, we can assume more properties are available about it, and could be reused for proving similar properties on iterated tuples.
For instance, let us take the following theorem:
```coq
Theorem Vector.peek_const {A : Type} : forall (a : A) (n : nat),
  Vector.peek (Vector.const a n) = a.
```

#### Proving the equivalence between both encodings

As we are proving equivalences involving vectors, we can exploit the same idea as in the section above about bounded natural numbers and bitvectors: first proving the equivalence between `tuple` and `Vector.t` for fixed parameter `A` and index `n`, then reusing `Vector.Param44` to switch between `Vector.t A n` and `Vector.t A' n'` for related `A`/`A'` and `n`/`n'`.

In order to prove the relation between `tuple` and `Vector.t`, we proceed as usual and define two functions to convert a tuple to a vector and conversely, then we prove that both compositions are identities, so that we can prove an isomorphism and the following relation:
```coq
Definition Param44_tuple_vector_d (A : Type) (n : nat) :
  Param44.Rel (tuple A n) (Vector.t A n).
```
Then, by using transitivity of parametricity records and `Vector.Param44`, we can conclude the proof:
```coq
Definition tuple_vector_R :
  forall (A A' : Type) (AR : Param44.Rel A A')
         (n n' : nat) (nR : natR n n'),
    Param44.Rel (tuple A n) (Vector.t A' n').
Trocq Use tuple_vector_R.
```

#### Relating constants

We must now provide relations linking both implementations of `peek` and `const`.
Following the transitivity idea again, we can exploit proofs present on vectors:
```coq
Definition Vector.peekR
  (A A' : Type) (AR : Param00.Rel A A')
  (n n' : nat) (nR : natR n n')
  (v : Vector.t A (S n)) (v' : Vector.t A' (S n')) (vR : Vector.tR A A' AR n n' nR v v') :
    AR (Vector.peek v) (Vector.peek v').

Definition Vector.constR
  (A A' : Type) (AR : Param00.Rel A A')
  (a : A) (a' : A') (aR : AR a a')
  (n n' : nat) (nR : natR n n') :
    Vector.tR A A' AR n n' nR (Vector.const a n) (Vector.const a' n').
```

The remaining crucial properties to prove are made easier because they are constant on the parameter and index:
```coq
Definition tuple_vector_peekR (A : Type) (n : nat) :
  forall (t : tuple A (S n)) (v : Vector.t A (S n)), Param44_tuple_vector_d A n t v ->
    AR (peek t) (Vector.peek v).

Definition tuple_vector_constR (A : Type) (a : A) (n : nat) :
    Param44_tuple_vector_d A n (const a n) (Vector.const a n).
```

The final relations proved and added to Trocq are the following:
```coq
Definition peekR
  (A A' : Type) (AR : Param00.Rel A A')
  (n n' : nat) (nR : natR n n')
  (t : tuple A (S n)) (v' : Vector.t A' (S n')) (r : tuple_vector_R A A' AR n n' nR t v') :
    AR (peek t) (Vector.peek v').
Proof.
  (* [...] transitivity : tuple_vector_peekR + Vector.peekR *)
Defined.
Trocq Use peekR.

Definition constR
  (A A' : Type) (AR : Param00.Rel A A')
  (a : A) (a' : A') (aR : AR a a')
  (n n' : nat) (nR : natR n n') :
    tuple_vector_R A A' AR n n' nR (const a n) (Vector.const a' n').
Proof.
  (* [...] transitivity : tuple_vector_constR + Vector.constR *)
Defined.
Trocq Use constR.
```

#### Actual proof reuse

Modulo adding equality to Trocq, we can now prove "for free" the following theorem expressed on iterated tuples:
```coq
Theorem peek_const {A : Type} : forall (a : A) (n : nat), peek (const a n) = a.
Proof. trocq. apply Vector.peek_const. Qed.
```

### Options and lists

Support for polymorphism and dependent types does not limit to type equivalences.
It is also possible to define directed relations between container types so that a lemma about a given container can be proved by transfer to a more general data structure.
Here, we present the example of a theorem about a map operation `omap` on the option type.
We will prove it from the associated theorem proved on lists.

#### Defining the directed relation

We can register a split injection from options to lists in Trocq, by defining two conversion functions and proving that one of the compositions is an identity.

```coq
Definition option_to_list : forall {A : Type} : option A -> list A.
Definition list_to_option : forall {A : Type}, list A -> option A.
Theorem option_to_listR (A : Type) :
  forall (xo : option A), list_to_option (option_to_list xo) = xo.
```

We can then create the split injection and the associated parametricity record:
```coq
Definition option_list_inj (A : Type) : @SplitInj.type (option A) (list A) :=
  SplitInj.Build (option_to_listR A).

Definition Param_option_list_d (A : Type) : Param42b.Rel (option A) (list A) :=
  SplitInj.toParam (option_list_inj A).
```
?> Note that again, we assume we are in a setup where relations linking the target standard type were defined previously. Here, it allows relating `option A` to `list A` and leaving the step changing the parameter `A` to an `A'` to the parametricity lemma over lists.

By transitivity, we can state the full relation and add it to Trocq:
```coq
Definition Param42b_option_list (A A' : Type) (AR : Param42b.Rel A A') :
  Param42b.Rel (option A) (list A').
Proof.
  apply (@Param42b_trans _ (list A)).
  - apply Param_option_list_d.
  - apply (Param42b_list A A' AR).
Defined.
Trocq Use Param42b_option_list.
```

#### Proof transfer with non-equivalent containers

After proving that `omap` is related to `List.map`, we can transfer the following lemma and prove it:
```coq
Theorem option_map_compose (A B C : Type) (f : A -> B) (g : B -> C) :
  forall (xo : option A), omap g (omap f xo) = omap (fun x => g (f x)) xo.
Proof.
  trocq.
  (*  forall (A B C : Type) (f : A -> B) (g : B -> C),
        forall (l : list A), map g (map f xo) = map (fun x => g (f x)) l.
  *)
  apply map_compose.
Qed.
```

### Complex proof transfer by composition

As parametricity relations can be composed, it is also possible to combine together relations declared in Trocq, including the directed ones, provided that the levels match.
For instance, a relation with structure `(α,β)` linking `list` to itself always requires a relation with the same structure on the parameter:
```coq
Lemma Param31_list : forall (A A' : Type), Param31.Rel A A' -> Param31.Rel (list A) (list A').
```
It means that an occurrence of `list T` required at level `(3,1)` will require the existence of a relation from `T` to an associated `T'` at level `(3,1)` in Trocq.

Therefore, even though `list` is *equivalent* to itself, we can declare several relations for it in Trocq, so that in cases where less information is required on the list type, a weaker relation can be accepted for the parameter, and thus transfer can be done both on a container type and the type of contents, *e.g.*, transferring `Vector.t positive n` to `tuple N n` in the following goal:
```coq
Theorem product_const_1 (A : Type) :
  forall (n : nat), Vector.product (Vector.const 1%positive n) = 1%positive.
```
Such a statement can be turned into the following goal (provided there exists a `Vector.product` with a counterpart over tuples of `N` defined in Trocq):
```coq
forall (n : nat), product (const 1%N n) = 1%N
```

### Trocq for advanced refinements

Such an approach enables refinement-like transfer, by expressing the statements with proof-oriented representations of the concepts involved in the formalisation project, be it arithmetic, containers, *etc.*, while remaining able to rephrase them in more efficient encodings to carry out proofs involving heavier computations that would take too long in the higher-level type.

#### Refining a mathematical type to a lower-level representation

?> This example is inspired from a [formalisation work involving advanced refinements](https://arxiv.org/pdf/2301.04060.pdf).

Consider the encoding of matrices in the [MathComp library](https://github.com/math-comp/math-comp), where `'M[T](m,n)` denotes a matrix of size `m`X`n` with elements in `T`.

!> To be continued...