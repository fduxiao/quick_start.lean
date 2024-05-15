--for some technical reason, I have to write several tactics for help
import QuickStart.MyTactics

/-!
In this file, we have basically two things: formal lean codes and comments. Lean codes are just
what they are called and comments are lines of natural language encompassed in /- -/ (we may have
some variants like --, /-! -/ and /-- -/).

Though to write a lean program only requires those lean codes, sometimes it is helpful to explain
them in natural language. In fact, I write this file treating it as a book, where most lines are
comments with relatively less lean codes.

Besides, `/-! -/` is used for Markdown display, i.e., we can have headers(#), citations(>), etc.
And `/-- -/` is used for DocString (you will figure it out later by hovering the cursor on some term).

# Basic types and functional programming

## Introduction
The core of modern computer proof assistants is always λ-calculus, i.e. functional programming.
This chapter is intended to introduce some basics about functional programming in lean.
In modern (dependent) type theory, we give a lot of *rules* to define the judgement `term: type`.
Functions are just a special rule to form a certain type, and proofs are just the judgement
`proof: proposition`, as is the Curry-Howard correspondence. I am going to introduce you those
*rules* in lean.

Programming languages based on λ-calculus have only a few core features (axioms in meta language).
And all you need for logic can be built from scratch within these features.
-/


/-!

## Days of a week
Our first example is to define a `finite` type. Just like defining a finite set, you can define
a type by enumerating all possible members.

The keyword to define a type is `inductive`. (You can tell why it is called `inductive` if you have
learned some type theory; otherwise, just accept that as a name.)

The following says we are going to define a new type `Week` in the universe `Type` with judgements
`Sunday: Week`, `Monday: Week`, etc. Recall that this definition means the judgement `term: Week`
is freely generated by the *constructors* `Sunday: Week, Monday: Week, ...`.
-/

inductive Week: Type :=
  | Sunday: Week
  | Monday: Week
  | Tuesday: Week
  | Wednesday  -- the `: Week` can be omitted since it can be infered from the context
  | Thrusday
  | Friday | Saturday -- you can write these constructors in one line
  deriving Repr -- This line is only for some technical reason, indicating you can display Week by its constructors


/-!
We are then able to check the newly defined type by

```lean
#check Week.Sunday
```
-/

#check Week.Sunday -- this will not be shown in doc-gen.

/-!
## Namespaces

You may have noticed that we have actually defined `Week.Sunday: Week`. To access the term `Sunday`,
we have to write `Week.Sunday`. This `Week` acts as a `namespace` so that if we have another type
with the same constructor names, we won't fall into a name conflict.
-/
inductive Weekend: Type := | Sunday | Saturday deriving Repr

#check Week.Sunday

/-!
If you want to use those names in a namespace directly, you can `open` it

```lean
open Weekend
#check Sunday
```
-/

open Weekend
#check Sunday

/-!
Namespaces can also be defined manually. This is helpful if you want to define something with existing
names. For example, lean has provided the type `Bool` with constructors `true` and `false`. To show you
how to define it from scratch, I have to define my own `Bool` using a different name `MyBool`, or I can
use a `namespace` to avoid it.
-/

inductive MyBool := | true | false

namespace scratch

  inductive Bool := | true | false
  open Bool

end scratch


/-!
Another application is to define the classical logic. As you know, Curry-Howard correspondence
is only true for intuitionistic logic. But you may want to use *law of excluded middle* since we have
the double negation monad (Glivenko's theorem) embedding classical logic in intuitionistic logc. We can
put those classical axioms in a namespace to use them if necessary. (Lean also provides such a namespace
called `Classical`)
-/
namespace classical

axiom em: forall (p: Prop), p ∨ ¬ p

end classical

/-!
## Define functions by case analysis
Now we know how to define a type by enumerating. Then a natural way to define
a function out of those types is to define a value for each case of those types.
This is known as case analysis (proof by cases).

The funciton `next_weekday : Week -> Week` is first a λ-abstraction `λ w => some term of type week`.
Then we perform the case analysis on `w: Week`
-/

/--
The next day in a week
-/
def next_weekday: Week -> Week := λ (w: Week) =>
  match w with
  | Week.Sunday => Week.Monday
  | Week.Monday => Week.Tuesday
  | .Tuesday => .Wednesday -- we can omit Week
  | .Wednesday => .Thrusday
  | .Thrusday => .Friday
  | .Friday => .Saturday
  | .Saturday => .Sunday


/-!
In lean, a λ-abstraction is defined using `λ variable => term` unlike the unsual `λ x . M` as in
many text books. If you don't know how to type the `λ`, you can use `fun variable => term` instead.
To type it in VSCode, just type `\lambda` and your text editor should change it for `λ`.
-/

def next_weekday_using_func: Week -> Week := fun (w: Week) =>
  match w with
  | Week.Sunday => Week.Monday
  | Week.Monday => Week.Tuesday
  | .Tuesday => .Wednesday -- we can omit Week
  | .Wednesday => .Thrusday
  | .Thrusday => .Friday
  | .Friday => .Saturday
  | .Saturday => .Sunday

/-!
To test the function `next_weekday`, using `#eval`

```lean
#eval next_weekday Week.Sunday
```
-/

#eval (next_weekday Week.Sunday)


/-!
### Currying

The above function is defined only for one variable. In set theory, a function for two variables is
defined as $f: A × B → C$. This can also be interpreted by the exponential rule: for each $a∈A$,
$f(a)$ is a function $B→C$, i.e., we many instead define $f: A → (B → C)$. This behavior is called
`currying`, which is adopted by type theory as the definition of multi-variable functions.

If we make the conventions that $→$ is right associative, we then simply write it as $f: A→B→C$.
-/

def ABA: Week -> Bool -> Week := λ a => λ b => a

-- or a simplier
def ABA': Week -> Bool -> Week := λ a b => a

/-!
## Syntactic Sugar
The above might be thought as the `standard` way to define a function by λ-calculus.
However, it may not be the most convenient way to define a function. For example, the semantics
of the above `next_weekday` can be interpreted as: for every `w: Week`, we want to find
a term of type `week` for the application `next_weekday w`, i.e., the following. This *sweeter*
way to write down the same thing with a different syntax is called a **syntactic sugar**
(Note the prime `'` after the name. In lean, we are unable to change a defined name)
-/

def next_weekday' (w: Week): Week := match w with
  | Week.Sunday => Week.Monday
  | Week.Monday => Week.Tuesday
  | .Tuesday => .Wednesday -- we can omit Week
  | .Wednesday => .Thrusday
  | .Thrusday => .Friday
  | .Friday => .Saturday
  | .Saturday => .Sunday


/-!
Moreover, we have another syntax sugar for `match`.
-/
def next_weekday'': Week -> Week
  | Week.Sunday => Week.Monday
  | Week.Monday => Week.Tuesday
  | .Tuesday => .Wednesday
  | .Wednesday => .Thrusday
  | .Thrusday => .Friday
  | .Friday => .Saturday
  | .Saturday => .Sunday

/-!
This is especially useful when you are defining a curried function.
-/

namespace scratch

def and: Bool -> Bool -> Bool
  | .true, .true => .true
  | .false, _ => .false -- wildcard
  | _, _ => .false


/-! this is an exercise -/
def or: Bool -> Bool -> Bool := sorry

def not: Bool -> Bool
  | .true => .false
  | .false => .true

end scratch

/-!
For the builtin type `Bool`, you can also use an `if ... then ... else ...` notation
instead of matching a `true`/`false`
-/

def my_not (x: Bool): Bool := if x then false else true

#eval my_not false

/-!
You can also define the `next_weekday` in the namespace `Week`. This time, let's call
it `Week.next`. But to use it, you have to spell the full name: `Week.next Week.Wednesday`.
The good part of that is you can use `w.next` for some `w: Week`.
-/

def Week.next: Week -> Week := next_weekday -- certainly you can use your own definitions
#eval Week.Wednesday.next


/-!
## Simple proofs with the tactic system

Now we are able to write down some basic proofs. We should think of proofs as terms of
some types, but to construct a large proof, the `tactic` system is more helpful. The two ways
to construct proofs are equivalent. You can think of tactics as syntactic sugar. I will
explain how tactics work later.


### Equality by reflexivity

To begin with, I am going to find a proof of `not false = true`, i.e., I am going to construct
a term `not_false_is_true: not false = true`. Here `term1 = term2` is a proposition, i.e., a
type. Then Curry-Howard correspondence says that it is provable if and only if we can find a
term of that type. I haven't defined this type, so you don't know its constructor or eliminator.
You can only rely on the tactic system to prove it now.
-/


def not_false_is_true : not false = true := by -- To use tactics, we begin with keyword `by`
  compute only [not] -- This is not a standard lean tactic. I just want to show some intermediate steps
  rfl -- The only way to prove equality is reflexivity.
  -- There's no further gaols. We have proved that.

/-!
If you don't want to always come up with a name, then use the `example` keyword.
-/

example: not false = true := by
  compute only [not]
  rfl


/-!
In fact, lean provides the `simp` tactic, so you can finish this by only one line.
-/
example: not true = false := by
  simp


/-! or some more complicated -/
example: forall b: Bool, and false b = false := by
  intros b -- bring the variable `b: Bool` into premises
  compute only [and]
  rfl

/-!
### Proof by cases

However, this fails for `and b false`. In the definition of `and`, we define `and false _` to be
`false`. This means `and false: Bool -> Bool` is a function `λ _ => false`. So of course
`and false _` can be reduced to `false`. But when we apply `and` to a variable `b: Bool`. There's no
way to do the β-reduction.
-/

theorem and_false_first_try: forall b: Bool, and b false = false := by
  intros b
  compute only [and]
  sorry


/-!
To solve this, we prove the theorem when `b:=true` and `b:=false` since `Bool` is only defined
with these two values.
-/
theorem and_false': forall b: Bool, and b false = false := by
  intros b
  cases b with
  | false =>
    compute only [and]
    rfl
  | true =>
    compute only [and]
    rfl

/-!
Still the `simp` tactic is so powerful that we can solve this simply.
-/
theorem or_true': forall b: Bool, or b true = true := by
  intros b; simp -- you can write multi tactics in one line with them separated by `;`

/-!
## Type based on other types

We have known how to define an enumeration. It is defined purely from scratch without knowing
any other inductive types. In this section, I will show you how to make a new type based
on other types. In type theory, a product `A×B` is formed by two types `A: Type` and
`B: Type`. As long as you have a term `a: A` and `b: B`, you are able to form
`⟨ a , b ⟩: A×B`, i.e., the product type is freely generated by all such pairs.

The `: Type` notation often means a name is actually a type. In dependent
type theory, we build a hierarchical universe by `Type n: Type (n+1)`. Thus we are
able to treat a type as a term. In lean `Type` is the smallest one `Type 0`.

-/

inductive MyProd (A: Type) (B: Type): Type :=
  | pair: A -> B -> MyProd A B
  deriving Repr


def MyProd.pr1: MyProd A B -> A
  | .pair a _ => a

def MyProd.pr2: MyProd A B -> B
  | .pair _ b => b


#eval (MyProd.pair Weekend.Sunday Week.Sunday)
#eval (MyProd.pair Weekend.Sunday Week.Sunday).pr1

/-!
Similarly, we define a sum/coproduct type `A+B` from `A: Type` and `B: Type`, which is freely
generated by all `a: A` and `b: B`.
-/

inductive MySum (A: Type) (B: Type): Type :=
  | in1: A -> MySum A B
  | in2: B -> MySum A B


/-!
## Type universe and dependent functions

In the above examples, we have seen the type universe `Type` and the quantifier `forall`.
The `forall` is known as dependent function type, whose `codomain` relies on the `domain`.
As noted above, a type `A: Type` can also be treated as a term. Then we are able to make
a function `P: A -> Type` to describe the codomain and the dependent function type is formed
as `forall a: A, P a`, i.e., `a: A, f: forall a: A, P a ⊢ f a: P a`. This is a bit like the
vector field `X` over a manifold M. For each `p ∈ M`, `Xₚ` is a vector in the tangent
space of `p`, i.e., `Xₚ ∈ TₚM`. So `X` is a dependent function map each `p` into `TₚM`.

Lean provides the hierarchical universe `Type 0: Type 1: Type 2: ...` together with a special
universe `Prop` for some technical reason, e.g., equalities are defined in this universe: `a=b: Prop`.
We also make `Prop: Type 0`. To have a uniform representation of type universes, they are all defined
as `Sort`: `Prop := Sort 0`, `Type 0 := Sort 1`, ..., `Type n := Sort (n+1)`.

Let's look at how to make a dependent function. Our aim is to define the identity function
id_A: A -> A. For each type `A: Type`, we can compose a λ-term `λ x => x: A -> A`. Thus we first
make the codomain function `id_type := λ A => (A -> A)` and the identity function is then defined of type
`id1 (A: Type): id_type A`
-/

def id_type: Type -> Type := λ A => A -> A
def id1 (A: Type): id_type A := λ x => x

/-!
You can also define it with the `forall` keyword.
-/

def id1': forall (A: Type), id_type A := λ A => λ (x: A) => x


/-! or write the type directly -/
def id1'': forall A: Type, A -> A := λ (A: Type) => λ (x: A) => x
def id1''' (A: Type) (x: A) := x


/-!
You can check the definitions.
```lean
#check id1''
#check id1'' Week
#eval id1 Week .Friday
```
-/

#check id1''
#check id1'' Week
#eval id1 Week .Friday

/-!
### Type inference and implicit arguments

To make `id1` well-defined, we have to define it by first passing a type `A` to it. However, `id1 A: A -> A`
must be applied to a term of type `A`. This means the `A` is redundant. The information of this type can be
inferred from the term applied after it. In tradition type theory, we usually make a convention here, if `id1`
is not applied to a term instead of a type like `id1 Week.Friday`, then this should mean
`id1 (type of Week.Friday = Week) Week.Friday`.

Lean provides a syntactic sugar called `implicit arguments` for this purpose. If you think a type can be
infered from the context, enclose it with brace `{}`.

-/

def id_auto_infer: forall {A: Type}, A -> A := λ x => x


/-!
Now you can apply it directly to a term or check its type.
```lean
#eval id_auto_infer Week.Friday
#check id_auto_infer
```
-/

#eval id_auto_infer Week.Friday
#check id_auto_infer

/-!
There might still exist some cases that you want the version with explicit arguments. Type an `@` before
the term, or using `(A:=some type)` to specify it.
-/

#check @id_auto_infer
#check @id_auto_infer Weekend
#check id_auto_infer (A:=Weekend)

/-!
You can also write it as `def id_auto_infer' {A: Type} (x: A)`.
-/
def id_auto_infer' {A: Type} (x: A) := x

/-!
Or even omit the `A`. Then lean will try to figure out the most suitable type or this $A$. In this
case, `A` is recognized as a type of some `Sort u`. So the type looks like
`id_auto_infer''.{u_1} {A : Sort u_1} (x : A) : Aid_auto_infer''.{u_1} {A : Sort u_1} (x : A) : A`
-/

def id_auto_infer'' (x: A) := x
#check id_auto_infer''


/-!
## Inductively defined types

Now I am going to really introduce some inductively define type, the natural numbers. We are also
allowed to define recursive functions upon them.

In type theory, the natural numbers `N` are freely generated by the rules:
1. `Z: N` - Zero is a natural number.
2. `S: N -> N` - if we have a natural number `n: N`, then `S n: N` is also a natural number.

This is written as
-/

/--
Natural numbers are defined with `Z: N` and `S: N -> N`.
-/
inductive N :=
  | Z: N
  | S: N -> N

/-!
The matching rule is also a bit complicated as shown in the following definition of addition.
To match an element `n: N`, you also have two cases
1. When `n` is made from `Z: N`
2. When `n` is made from `S m: N` for another number `m: N`.
-/
def N.add (n1: N) (n2: N): N :=
  match n1 with
  | .Z => n2
  | .S n => .S (n.add n2) -- we do the recusion here.

/-! Apparently, we have the following theorem. -/
theorem N_left_add_Z: forall n: N, N.add N.Z n = n := by
  intros n
  compute only [N.add]
  rfl

/-!
### Prove by induction

Just as before, after we apply `N.add` to `Z`, we get a function `N.add N.Z : N -> N := λ n2 => n2`. If we
then apply it to `n`, surly we can β-reduce it to `n`. However, if we apply it to some variable `N.add n`, we are
unable to do the β-reduction, since it is already the β-normal form. The solution is still to use case analysis,
but we will then have some extra information about the predecessor, which is usually called induction.
-/

theorem N_add_Z: forall n: N, N.add n N.Z = n := by
  intros n
  induction n
  -- we have two cases
  -- The first is just `Z`, which we prove simply by reflexity
  case Z => rfl
  -- The second is `S m` and a inductive hypothesis on `m`.
  case S m IHm =>
    -- m : N, IHm : add m Z = m ⊢ add (S m) Z = S m
    -- Then we simplify it by computing `add (S n)
    compute only [N.add]
    -- Now we have an equality `IHm` in the hypothesis. To make use of it, we write it.
    rw [IHm] -- Lean do the `rfl` automatically.


/-!
Lean provides a builtin type `Nat` for natural numbers.


Here are some exercises.
-/

/-- the predecessor function -/
def N.pred: N -> N
  | .Z => .Z
  | .S m => m


theorem pred_succ_id: forall n: N, N.pred (N.S n) = n := sorry
theorem add_comm: forall m n: N, N.add m n = N.add n m := sorry



/-!
## Polymorphic type definition
In mathematics `N` is a free monoid generated by one element. If we want another monoid generated
by two elements, what should we do?
-/

inductive FreeMonoidByTwo :=
  | EmptyWord: FreeMonoidByTwo -- which is the unit of the monoid
  | WordConstruct: Bool -> FreeMonoidByTwo -> FreeMonoidByTwo -- how to make a word
  deriving Repr


/-!
Obviously, we have `true` and `false` are two elements of `FreeMonoidByTwo`, and we may have some
complicated one.
-/

open FreeMonoidByTwo -- open it for convenience

def element_true := WordConstruct true EmptyWord
def element_false := WordConstruct false EmptyWord

def element_true_true := WordConstruct true element_true
def element_false_true_true := WordConstruct false element_true_true

#eval element_false_true_true

/-!
But what is the monoid binary operation? That is the concatenation of two such words.
-/

def FreeMonoidByTwo.concat: FreeMonoidByTwo -> FreeMonoidByTwo -> FreeMonoidByTwo
  | EmptyWord, m => m
  | WordConstruct x xs, m => WordConstruct x (FreeMonoidByTwo.concat xs m)

/-!
You certainly want the following
-/

def monoid_id2: forall l: FreeMonoidByTwo, l.concat EmptyWord = l := sorry
def monoid_assoc2: forall l m n: FreeMonoidByTwo, l.concat (m.concat n) = (l.concat m).concat n := sorry


/-!
So now, what if I want a free monoid generated by three elements?
-/

inductive Three := | One | Two | Three
inductive FreeMonoidByThree :=
  | EmptyWord3: FreeMonoidByThree
  | WordConstruct3: Three -> FreeMonoidByThree -> FreeMonoidByThree


open FreeMonoidByThree

def FreeMonoidByThree.concat: FreeMonoidByThree -> FreeMonoidByThree -> FreeMonoidByThree
  | EmptyWord3, m => m
  | WordConstruct3 x xs, m => WordConstruct3 x (FreeMonoidByThree.concat xs m)

def monoid_id3: forall l: FreeMonoidByThree, l.concat EmptyWord3 = l := sorry
def monoid_assoc3: forall l m n: FreeMonoidByThree, l.concat (m.concat n) = (l.concat m).concat n := sorry

/-!
There are ceratinly some common parts in these free monoid. We can introduce a type variable in order
to save some life. You can understand the following as defining a free monoid as above for each type, and they
turn out to be a function `FreeMonoid: Type -> Type`.
-/

inductive FreeMonoid (A: Type): Type :=
  | nil: FreeMonoid A
  | cons: A -> FreeMonoid A -> FreeMonoid A

def FreeMonoid.concat: FreeMonoid A -> FreeMonoid A -> FreeMonoid A
  | .nil, m => m
  | .cons x xs, m => .cons x (xs.concat m)

def monoid_id: forall {A: Type} (l: FreeMonoid A), l.concat .nil = l := sorry
def monoid_assoc: forall {A: Type} (l m n: FreeMonoid A), l.concat (m.concat n) = (l.concat m).concat n := sorry

/-!
Lean provides a builtin free monoid type called `List`
```lean
#check List.nil
#check List.cons
```
-/

#check List.nil
#check List.cons

/-!
with some syntactic sugar for it.

```lean
#check [] -- for nil
#check (1 :: 2 :: []) -- for cons
#check ([1, 2, 3]) -- or this notation
#check ([.Friday, .Sunday] : List Week) -- or some other type
```
-/

#check [] -- for nil
#check (1 :: 2 :: []) -- for cons
#check ([1, 2, 3]) -- or this notation
#check ([.Friday, .Sunday] : List Week) -- or some other type
