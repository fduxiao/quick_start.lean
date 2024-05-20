import QuickStart.MyTactics
import QuickStart.Basic

/-!
I won't write a long file with everything in it. Instead I split it into many different parts, and
import them if needed later.

```lean
import QuickStart.MyTactics
import QuickStart.Basic
```
-/

/-!
# Induction principles and Curry-Howard Correspondence
We have already known how to make a new type and write some simple proof.
I will explain them further in this chapter.

In type theory, a new type means
how to form the type, how to construct terms of this type, how to eliminate it
by functions into other type, how to compute when a eliminator is applied to
a constructor.

To make a function, we have to do the following.
1. Formation of type: for `A, B: Type`, we form a new type `A -> B: Type`.
2. Construction of term: for any variable `x: A` and term `M: B`, we construct `λ x => M: A -> B`.
3. Elimination of it: To make use of some `f: A -> B`, we find `x: A` and obtain `f a: B`
4. Computation (β-reduction): `(λ x => M) N` $\to_\beta$ `M[x:=N]`
5. Optional Uniquess (α-conversion and η-equality): In λ-calculus, we may require `λ x => f x := f`

## From System F to induction principles
I only showed you how to form an inductive type and introduce terms of that type. I haven't shown you
the formal definition of the eliminator of it. Actually, for each `inductive` type, an induction principle
is assigned to the type, which acts as the eliminator of that type.

Let's begin with the basic pieces: products and sums (coproducts). With the help of dependent functions (∏-types),
we are able to define products and sums purely with functions. These definitions are known as System F.

In system F, a product is defined by how to make use of it. If you have a pair of type `A×B`, then to define
a function `f: A×B->C` out of this product type, you can think of it as the `uncarried` version of `A->B->C`.
Thus as long as you have such a function, you can get a term of type `C`, i.e., we we define
`A×B := forall (C: Type), (A -> B -> C) -> C`.

An intereresting fact is that in classical logic,
(A→B→⊥)→⊥ = ¬(A→¬B) = ¬(¬A∨¬B)=(¬¬A)∧(¬¬B) = A ∧ B.
-/


def ProdF (A: Type) (B: Type) := forall {C: Type}, (A -> B -> C) -> C
def pairF (a: A) (b: B): ProdF A B := λ f => f a b
def pr1F (p: ProdF A B): A := p (λ a b => a)
def pr2F (p: ProdF A B): B := p (λ a b => b)

#eval pr1F (pairF 2 3)
#eval pr2F (pairF 2 3)

theorem pr1_pair_F: forall (a: A) (b: B), pr1F (pairF a b) = a := by
  intros a b
  unfold pr1F
  compute only [pr1F]
  unfold pairF
  compute only [pairF]
  rfl

/-!
Similary, we define the sum (coproduct) `A + B` as: if you have `f: A->C` and `g: B->C`, then you certainly have
a type `A + B -> C`, as is the universal property of coproduct, which suggests a function `A + B -> C` is equivalent
to a pair of `(A -> C) × (B -> C)`. This is how `match` looks like in type theory.

And still in classical logic, we have $(A→⊥)→(B→⊥)→⊥=¬A→(¬¬B)=¬A→B=¬¬A∨B=A∨B$.
-/

def SumF (A: Type) (B: Type) := forall {C: Type}, (A -> C) -> (B -> C) -> C
def in1F (a: A): SumF A B := λ f g => f a
def in2F (b: B): SumF A B := λ f g => g b
def matchF (s: SumF A B) (f: A -> C) (g: B -> C): C := s f g


theorem match_in1_F: forall (a: A) (f: A -> C) (g: B -> C), matchF (in1F a) f g = f a := by
  intros a f g
  unfold matchF
  compute only [matchF]
  unfold in1F
  rfl

/-!
In the above, the elimination rules are used directly as defintions. This hints us how to give
the elimination rules for them. Recall we defined `MyProd` as
```lean
inductive MyProd (A: Type) (B: Type): Type :=
  | pair: A -> B -> MyProd A B
```

We expect an eliminator of type `forall {A B C: Type}, (A -> B -> C) -> MyProd A B -> C`, which means
to define a function out of `MyProd A B` (to eliminate `MyProd A B`), it suffices to define a function
`A -> B -> C`. We usually call it the `recusor` of type `MyProd`

Furthermore, we actually stipulate a dependent version of that `A -> B -> C`. Instead of just a constant
`C`, we use a dependent function `P: MyProd A B -> Type`, i.e.
`forall {A B: Type} {P: MyProd A B -> Type}, (forall (a: A) (b: B), P (MyProd.pair a b)) -> forall p: MyProd A B, P p`.
This is usually called the `induction principle` of the type `MyProd`. And surely the recursor is a special
case of induction principle.

You can think of `P` as a predicate on `MyProd A B`, and the induction principle says that to prove something
about `MyProd A B`, it suffices to prove for each pair.

In lean, the `induction principle` is denoted by `@MyProd.rec`. **Note it is named as `recursor`**. This is
different from HoTT or Coq, and is a bit complicated becasue it is defined for any `Sort`.
```lean
#check @MyProd.rec
```
which shows
```
@MyProd.rec : {A B : Type} →
  {motive : MyProd A B → Sort u_1} → ((a : A) → (b : B) → motive (MyProd.pair a b)) → (t : MyProd A B) → motive t
```
Here `(a : A) → (b : B) → motive (MyProd.pair a b)` is yet another syntactic sugar for
`forall (a: A) (b: B), motive (MyProd.pair a b)`

We also have a computation rule
`@MyProd.rec f (pair a b) := f a b`
-/

#check @MyProd.rec

/-!
Similary, for sum type `MySum`. The recursor is of type
`forall {A B C: Type}, (A -> C) -> (B -> C) -> MySum A B -> C`, which says to define eliminate a sum,
you only have to stipulate what happens for `A` and what happens for `B`.

The induction principle is of type
```
forall {A B: Type} {P: MySum A B -> Type},
  (forall a: A, P (in1 a)) ->
  (forall b: B, p (in2 b)) ->
  forall s: MySum A B, P s
```
which says to prove something about `A+B`, it suffices to prove only for case `A` and case `B`.

```lean
#check @MySum.rec
```
which shows

```
@MySum.rec : {A B : Type} →
  {motive : MySum A B → Sort u_1} →
    ((a : A) → motive (MySum.in1 a)) → ((a : B) → motive (MySum.in2 a)) → (t : MySum A B) → motive t
```
with a computation rule `MySum.rec f g (in1 a) := f a` and `MySum.rec f g (in2 b) := g b`
-/

#check @MySum.rec

/-!
## Curry-Howard Correspondence and tactics

Now, I can explain how the tactic `cases` works. Before that, let's first explain how tactic system
makes use of Curry-Howard correspondence to help us build a proof effectively.

### Apply an implication with tactic `apply`

For example, the distributive law of implication `(A → B → C) → (A → B) → (A → C)` is proved by the λ-term
`λ (f: A -> B -> C) => λ (g: A -> B) => λ (a: A) => f a (g a)`. Though you may be extremely familiar
with type theory and can tell the meaning of the λ-term without thinking, I want to show a construction
of it step by step as in the proof tree.

1. Our target is `⊢ ?: (A → B → C) → (A → B) → (A → C)`
2. It is equivalent to prove `f: A → B → C ⊢ ?: (A → B) → (A → C)`
3. Let's bring all premises to the context `f: (A → B → C), g: A → B, a: A ⊢ ?: C`.
4. Now, to obtain the `C`, I want to `apply f`. It suffices to form `g: A → B, a: A ⊢ ?: A` and `g: A → B, a: A ⊢ ?: B`
5. The proof is split into to cases, the proof of `A` and the proof of `B`
6. For `A`, just `apply (a: A)`.
7. For `B`, we want to `apply (g: A → B)`. Again, we only have to prove some `?: A`

This process is a bit write the proof tree upside-down. It is helpful for long proof, since you may not know
what is the first step, but from the final target, it's easier to guess what is the last step.
-/


/-! the proof as λ-term -/
def imp_distrib_func: (A -> B -> C) -> (A -> B) -> (A -> C) := λ f => λ g => λ a => f a (g a)


/-!
the proof by tactics

*Tactics can only be used for propositions in lean.*
-/

theorem imp_distrib: forall {A B C: Prop}, (A -> B -> C) -> (A -> B) -> (A -> C) := by
  -- First bring the variables into premises
  intros A B C
  intros f g a
  -- Then, I want to apply `f`.
  apply f
  -- This means I have to give the proofs of `A` and `B`
  apply a -- proof of `A`
  apply (g a) -- proof of `B`

/-!
In other words, tactics are just a small part of the construction of a long λ-term. And we know that
dependent functions are just universal quantifiers. Most tactics are just application of certain
dependent functions.

We know `intros` is to bring a variable into premises. We can also revert that.
To show you the example, I temporarily enter a section with some extra variables (axioms) for convenience.
This is a bit like an anonymous namespace.
-/

section

variable (A B: Type)
variable (P: A -> B -> Prop)
axiom some_fact: forall (x: A) (y: B), P x y

-- theorem another_fact: forall (y: B) (x: A), P x y := some_fact
theorem another_fact: forall (y: B) (x: A), P x y := by
  intros y x
  revert y
  revert x
  apply some_fact

end

/-!
### Equality and rewrite.

Now, I reveal the mistery of `rfl`. For any type `A: Type` and `x, y: A`, you can always form the type
`x = y`, and the only way to construct such a type is reflexivity `refl: forall x: A, x = x`. Thus
`rfl` is just `apply refl`.
-/

inductive MyEq (A: Type): A -> A -> Type :=
  | refl: forall x: A, MyEq A x x


/-!
The type of the eliminator of equality is
```
forall (A: Type) (P: forall {x y: A}, MyEq A x y -> Type),
  (forall x: A, P x x (refl x)) ->
  forall (x y: A) (e: MyEq A x y), P e
```
It says that to prove something based on the equality `e: x y`, we only have to assume it is obtained
from reflexivity and prove your target when `y:=x`.

Lean provides a builtin equality type `Eq` with the syntactic sugar `x=y` for `Eq A x y`, and the induction
principle is a variant of the above, called the `based path induction` in HoTT. Check it by yourself
-/

#check @Eq.rec

theorem function_well_defined: forall (f: A -> B) (x y: A), x = y -> f x = f y := by
  intros f x y
  -- apply @Eq.rec -- unable to infer the type A
  apply (@Eq.rec A) -- equivalent to `rw`
  apply Eq.refl -- equivalent to `rfl`

/-！
#### Generalization with equalities
In logic, if we are able to prove a formula about a constant which does not occur in the axioms, then
we are able to *generalize* it with a universal quantifier. This is to say, if you want to prove a fact
about a constant, you can instead treat it as a variable.
-/
theorem five_plus_zero: 5 + 0 = 5 := by
  generalize 5 = x
  apply Nat.add_zero

/-!
So, what does lean do here? Suppose you have a predicate `P: A -> Prop`, and you want to prove `P c`
for some constant `c: A`. To generalize it, lean changes your goal form `P c` to `forall x, x=c -> P x`.
Then your aim is to prove the new goal.
-/
theorem five_plus_zero': 5 + 0 = 5 := by
  -- we can make some local assertions by tactic `have`
  -- and the original is equivalent to prove this assertion
  have an_assertion: forall x, x=5 -> x + 0 = x := by
    intros x E -- note that you have this bonus equality `E: x=5`
    apply Nat.add_zero
  apply an_assertion 5 (Eq.refl 5)

/-!
This behavior is useful if you want to *remember* a term as a variable for some later usage such as
prove by cases. This could also be understood as a `enhanced` version of `revert`, because you are only
allowed to `revert` an existing symbol, but `generalize` allows you to introduce new variables.
-/
theorem five_plus_zero'': 5 + 0 = 5 := by
  -- The hypothesis of equality can be introduced explicitly as follows
  generalize E: 5 = x
  apply Nat.add_zero

/-!
### Tactic `cases`

What about `cases` tactic? The induction principle (eliminator) of `Bool` is
`forall P: Bool -> Type, P true -> P false -> forall b: Bool, P b`, which says to prove a property of `Bool`, you
only have to prove it for `true` and `false`. In the example `forall b: Bool, b and true = b` is proved by first
making a predicate `P := λ b => (b and true = b)`. Then if we apply the eliminator with this `P`, we only have to
prove `true and true = true` and `false and true = false`. This shows `cases` is just the application of the
eliminator with some syntactic sugar.

Note that `=` is itself a type and `P: Bool -> Type` is made by
the λ-abstraction, not from the induction rule. The type `x=y` is constructed from the *formation rule*
of type `=`.
-/

theorem and_true': forall b: Bool, Bool.and b true = b := by
  apply @Bool.rec
  case true => rfl
  case false => rfl

/-!
#### Disjunction and tactics
Lean provides us the disjunction type `Or`. Unlike the `Sum` defined for arbitrary type, it is only
defined for propositions.
-/

inductive MyOr (A B: Prop): Prop :=
  | inl: A -> MyOr A B
  | inr: B -> MyOr A B


/-!
In intuitionistic logic, to prove a disjunction, you have to prove either the left or the right, and
to make use of it, you have to prove the result both under the left and under the right.

```lean
#check Or
#check Or.inl
-- or use this
#check Or.intro_left
#check Or.inr
-- or use this
#check Or.intro_right
#check @Or.rec
```
-/
#check Or
#check Or.inl
-- or use this
#check Or.intro_left
#check Or.inr
-- or use this
#check Or.intro_right
#check @Or.rec

theorem affirm_the_left: A -> A ∨ B := by
  intros a
  apply Or.inl
  apply a

theorem affirm_the_right: B -> A ∨ B := by
  intros b
  right -- a tactic to apply `Or.inr`
  apply b



/--
Lean provides `or_comm`
-/
theorem disj_comm: A ∨ B -> B ∨ A := by
  intros H
  cases H
  case inl a => right; apply a -- you can write multiple tactics within one line separated by `;`
  case inr b => left; apply b

/-!
### Structure for conjuctions and existential quantifiers.

We have seen how to make a `Prod` type, which is the counterpart of conjunction according to Curry-Howard
correspondence. Similarly, existential quantifiers are just those pairs where the type of the second item
depends on the first. They are often called dependent pairs (∑-type). This is a bit like the definition of
a vector bundle, whose elements are those pairs `(p, vₚ)` such that $v_p \in T_M$.
-/

inductive MyDependentPair (A: Type) (P: A -> Type): Type :=
  | pair (a: A) (p: P a): MyDependentPair A P


def MyDependentPair.pr1: MyDependentPair A P -> A
  | pair a _ => a

def MyDependentPair.pr2 (p: MyDependentPair A P): P (MyDependentPair.pr1 p) := match p with
  | pair _ p => p

/-!
For such a (dependent) pair, the most useful things are the projections to each components. In general,
you have to define them each time after define a new type. Lean provides a syntactic sugar called `structure`
for an inductive type with only one constructor, where each component is provided as the projection.
-/

structure Point (A: Type) where
  mkPoint ::  -- name of the constructor
  x: A
  y: A
  deriving Repr

/-!
In this example, a new type `Point: Type -> Type` is defined, who has only one constructor
`mkPoint: A -> A -> Point A`, with the natural projections `x: Point A -> A` and `y: Point A -> A`.

```lean
#check Point.mkPoint -- Point.mkPoint {A : Type} (x y : A) : Point A
#check Point.x -- Point.x {A : Type}, Point A -> A
#check Point.y -- Point.y {A : Type}, Point A -> A
```

You can omit the name of the constructor `mkPoint`. Then lean will use `Point.mk` as the constructor
-/

#check Point.mkPoint
#check Point.x
#check Point.y

def point34 := Point.mkPoint 3 4
#eval { point34 with x:=5 }

/-!
You can also use the syntactic sugar `⟨,⟩` for a structure
-/
def point34': Point Nat := ⟨3, 4⟩

/-!
The structure can also be dependent. For example a monoid is a dependent tuple with
1. a type `Carrier`
2. a unit of type `Carrier`
3. the binary operator `Carrier -> Carrier -> Carrier`
4. the witness of the axioms of a monoid

I first define the `data` of a monoid, and then extend it with the witness.
-/

structure MonoidData where
  Carrier : Type
  unit : Carrier
  op : Carrier -> Carrier -> Carrier

#check MonoidData.mk
#check MonoidData.op

structure Monoid extends MonoidData where
  left_unit: forall x: Carrier, op unit x = x
  right_unit: forall x: Carrier, op x unit = x
  op_assoc: forall x y z: Carrier, op x (op y z) = op (op x y) z

/-!
Lean provides type `And` for conjuction and type `Exists` for existential quantifiers. `And` is defined
as a structure but `Exists` is still defined as an inductive pair.

```lean
#check And
#check And.intro
#check @And.left
#check @And.right
#check @And.rec

#check Exists
#check Exists.intro
#check Exists.choose
#check Exists.choose_spec
#check @Exists.rec
```
-/

namespace scratch

structure And (A B: Prop): Prop where
  intro ::
  left: A
  right: B

inductive Exists (A: Type) (P: A -> Prop): Prop where
  | intro: (a: A) -> P a -> Exists A P

end scratch


#check And
#check And.intro
#check @And.left
#check @And.right
#check @And.rec

#check Exists
#check Exists.intro
#check Exists.choose
#check Exists.choose_spec
#check @Exists.rec

/-!
#### Tactics related to `And`
I show you how to prove a conjunction and how to make use of a conjunction.
-/

theorem and_intro: A -> B -> A ∧ B := by
  intros a b
  apply And.intro a b

theorem and_intro': A -> B -> A ∧ B := by
  intros a b
  -- or prove it separately
  apply And.intro
  -- for multi-targets, you can use the `bullets` for each case
  . apply a
  . apply b

/--
Lean provides `and_comm`
-/
theorem conj_comm: A ∧ B -> B ∧ A := by
  intros H
  cases H with -- destruct a conjunction
  | intro a b =>
    apply And.intro
    -- you can also use cases
    case left => apply b
    case right => apply a


/-!
Previously, the `intros` tactics was used to introduce premises. Actually, it is the plural form
of tactic `intro`. `intros` allows you to intros multiple premises, while `intro` allow you to
introduce a conjuction by its components.
-/
theorem conj_comm3: A ∧ B ∧ C -> C ∧ B ∧ A := by
  intro ⟨ a, b, c ⟩
  apply And.intro
  . apply c
  . apply And.intro
    . apply b
    . apply a

/-!
#### Tactics related to `Exists`
Still, how to conclude an existence and how to make use of such an existence.
-/
theorem four_is_double_2: exists (k: Nat), 4 = k + k := by
  apply Exists.intro 2
  rfl

/-!
you can finish the proof with a simple `exists`
-/
theorem four_is_double_2': exists (k: Nat), 4 = k + k := by
  exists 2 -- lean will try to finish the proof after you choose one construction

/-!
To make use of it, still use cases to destruct.
-/
theorem use_exists: (exists n: Nat, n + 1 = n + 2) -> exists m, m = m + 1 := by
  intros H
  cases H with
  | intro n Hn => exists n + 1

/-!
### True and False and ex falso quodlibet

The type universe itself can be thought as a category with a terminal object `True: Type` and an initial
object `False: Type`. They should be types (unlike `true: Bool` or `false: Bool`). In lean, `True` is just
a type with only one trivial constructor and `False` is an inductive without any constructor. Also `Not A`
is defined to be `A -> False`.
-/

namespace scratch

inductive True: Prop :=
  | intro: True

#check @True.rec

inductive False: Prop

#check @False.rec

def Not (A: Prop) := A -> False

end scratch

/-!
You are able to define any function out of `False`. This time, instead of `match`, we use `nomatch`
showing that it cannot be constructed. Again, this is the application of eliminator.
-/

#check @False.elim
def exfalso (t: False): A := nomatch t
def exfalso': False -> A := @False.elim A


theorem exfalso'': forall (A B: Prop), A ∧ ¬ A -> B := by
  intros A B H
  exfalso
  have Ha := H.left
  have Hna := H.right
  apply Hna
  apply Ha

/-!
Injections and discrimination

Basically, the constructors are injective and are disjoint with each other
-/

theorem succ_inj: forall n m: Nat, n.succ = m.succ -> n = m := by
  intros n m H
  have H': n = n.succ.pred := by rfl
  rw [H']
  rw [H]
  rfl

/-!
This is admitted by lean automatically.
-/
theorem succ_inj': forall n m: Nat, n.succ.succ = m.succ.succ -> n + k = m + k := by
  intros n m H
  injection H with H'
  injection H' with H''
  rw [H'']

/-!
And `zero` can never be a `succ`
-/

theorem discriminate_ex1: forall (n: Nat), 0 = n.succ -> true = false := by
  intros n contra
  -- we have the contradiction in premise contra
  contradiction

theorem discriminate_ex2: forall (m n: Nat), true = false -> m = n := by
  intros m n contra
  -- we have the contradiction in premise contra
  contradiction

/-!
## Induction Principle for natural numbers.
Finally, I can tell you how the induction principle gets its name. Let's think about the eliminator of
natural numbers:
`forall (P: Nat -> Type) -> P Nat.zero -> (forall n: Nat, P n -> P n.succ) -> forall n: Nat, P n`.
This induction principle says that to prove something about `N`, you have to first prove it for
`Z` and forall `n` such `P n`, you can prove `P n.succ`, which is exactly the usual `mathematical induction`.
The tactic `induction` is the application of this eliminator.

You can check the builtin one.
```lean
#check @Nat.rec
```
-/

#check @Nat.rec
