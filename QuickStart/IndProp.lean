import QuickStart.MyTactics

/-!
## Predicates with `Bool`
which are actually decidable.
-/

def evenb (n: Nat): Bool := match n with
  | .zero => true
  | .succ m => not (evenb m)


#eval evenb 5
#eval evenb 20


theorem evenb_S: forall n: Nat, evenb n.succ = not (evenb n) := by
  intros n
  compute [evenb]
  rfl

/-!
## Predicate with other propositions
-/

def double (n: Nat): Nat := 2 * n
def even_double (n: Nat): Prop := exists k: Nat, n = double k

example: even_double 4 := by
  exists 2

theorem double_evenb: forall n, evenb (double n) = true := by
  intros n
  induction n
  case zero => rfl
  case succ m IHm =>
    simp [double]
    simp [evenb]
    apply IHm

theorem even_double_conv: forall n, exists k, n = if evenb n then double k else (double k).succ := by
  intros n
  induction n
  case zero =>
    simp [evenb]
    exists 0 -- lean conclude the proof automatically
  case succ m IHm =>
    simp [evenb]
    cases IHm with
    | intro k Hk =>
      -- now we have to prove by cases of `evenb m`
      generalize E: evenb m = even_m
      rw [E] at Hk
      cases even_m with
      | true =>
        simp at *
        exists k
      | false =>
        simp at *
        exists (k + 1)
        simp [double]
        rw [Hk]
        rfl

/-!
## `even_double` is decidable
-/

theorem even_double_evenb: forall n, even_double n -> evenb n = true := by
  intros n H
  unfold even_double at H
  cases H with
  | intro k Hk =>
    rw [Hk]
    apply double_evenb

theorem evenb_even_double: forall n: Nat, evenb n = true -> even_double n := by
  intros n H
  have conv_n := even_double_conv n
  cases conv_n with
  | intro k Hk =>
    rw [H] at Hk
    simp at Hk
    exists k


/-!
## Inductively defined predicates
-/

-- zero is even and if `n` is even, then so is `n + 2`
inductive even: Nat -> Prop :=
  | even_z: even 0
  | even_ss (n: Nat): even n -> even (n + 2)

open even

/-!
## the predicate `even` is decidable
-/

#check @even.rec
theorem even_evenb: forall n, even n -> evenb n = true := by
  intros n H
  induction H
  case even_z =>
    rfl
  case even_ss m e IHe =>
    rw [evenb]
    rw [evenb]
    simp
    exact IHe


theorem double_even: forall k, even (double k) := by
  intros k
  induction k
  case zero => apply even_z
  case succ l IHl =>
    have E: double (l + 1) = double l + 2 := by simp [double]; rfl
    rw [E]
    apply even_ss
    apply IHl


theorem evenb_even: forall n, evenb n = true -> even n := by
  intros n H
  have E := evenb_even_double n H
  cases E with
  | intro k Hk =>
    rw [Hk]
    apply double_even

theorem evenb_false: forall n, evenb n = false -> ¬ even n := by
  intros n HF HE
  let H := even_evenb n HE
  rw [H] at HF
  contradiction

/-!
### Another example as exercise
-/

def eqb: Nat -> Nat -> Bool
  | 0, 0 => true
  | .succ m, .succ n => eqb m n
  | _, _ => false


#eval (eqb 0 2)
#eval (eqb 2 2)


theorem eq_eqb: forall m n, m = n -> eqb m n = true := sorry
theorem eqb_eq: forall m n, eqb m n = true -> m = n := sorry

/-!
## Decidability and `if`
Now, let's think about a predicate on `Prop` itself. A proposition is decidable if it is either true
or false (probably through some algorithm). This means you can use the `ite` (if-then-else) clause
for this proposition. Apparently, lean won't allow you to do that.
```
#eval if even 3 then true else false
```

### Typeclasses
How to tell lean the thing we have just proved? Lean asks you to fulfill a `typeclass`. Let's start
from some simple examples. Previously, we have defined a lot of types, but what if we want to use
the operator `+` for them? We know `Bool` is natural a group of order 2, so it makes sense to write
`true + true = false`. Then comes the same question: how to tell lean that?.
-/

def Bool.add (b1: Bool) (b2: Bool): Bool := Bool.xor b1 b2

/-!
In general, an `additive` type is the information of `A: Type` and an `add: A -> A -> A`, i.e,
a dependent pair of the information.
-/

structure Additive' (A: Type) where
  add: A -> A -> A

/-!
If you want lean to notice the information of the additive structure, you declare it as a `class`.
-/
class Additive (A: Type) where
  add: A -> A -> A

/-!
Then, to tell lean you want to use `add` for `Bool`, declare an `instance` of that `class`.
-/

instance bool_additive: Additive Bool where
  add := Bool.add

/-!
These typeclasses and instances are just dependent pair types and terms of that types. You
can use them as usual, but with a slightly different syntax.
-/

def add3 {A: Type} [A_is_additive: Additive A] (a b c: A): A :=
  A_is_additive.add a (A_is_additive.add b c)

#eval add3 (A_is_additive := bool_additive) true false true

/-!
Or if you only have one instance for that typeclass:
-/

def add3' {A: Type} [Additive A] (a b c: A): A :=
  Additive.add a (Additive.add b c)

#eval add3' true true false

/-!
Now, you can read the type of `Additive.add`
```lean
#check Additive
#check Additive.add
```
-/
#check Additive
#check Additive.mk
#check Additive.add

/-!
Of course, for a field, we may have two monoidal operations. You can specify the one you prefer.

If you want to use the `+` operator, you have to fulfill the `Add` typeclass. This is called
operator overloading.
-/
instance : Add Bool where
  add := Bool.add

#eval true + true + true

/-!
Besides, the digitals 0,1,⋯,9 and the decimal representation are also unary operators.
This type the dependent product is more complicated.
-/

class MyOfNat (A : Type) (n : Nat) where
  ofNat : A

instance : OfNat Bool 0 where
  ofNat := false

instance : OfNat Bool 1 where
  ofNat := true

#eval (1 + 0: Bool)


/-!
You can even define that for all natural numbers, i.e., we define the instance to be a dependent
function `forall n: nat, OfNat bool n`.
-/

def nat2bool: Nat -> Bool
  | .zero => 0
  | .succ n => (nat2bool n) + 1


#check OfNat
#check OfNat.mk
#check @OfNat.mk -- @OfNat.mk : (A : Type) → (x : Nat) → A → OfNat A x
#check (@OfNat.mk Bool 0 false)

instance : forall n: Nat, OfNat Bool n := by
  intros n
  apply OfNat.mk
  apply nat2bool n

#eval (97: Bool)

instance : (n: Nat) -> OfNat Bool n := fun n => @OfNat.mk Bool n (nat2bool n)

#eval (96: Bool)

/-!
Or even simpler
-/
instance : OfNat Bool n where
  ofNat := nat2bool n

#eval (99: Bool)

/-!
### Type coercion
We can say digitals are operators, so it's natural to add `3` to `false`. What about really add a
`Nat` to `Bool`? We can choose to fulfill a type coercion: if a `Nat` is used for a `Bool`, then
it will be automatically cast to `Bool` through `nat2bool`.
-/

instance : Coe Nat Bool where
  coe := nat2bool

#eval false + Nat.succ 2


/-!
### Auto deriving

In Lean, to *display* a term of some type, you have to map it to a string (`List`) of characters. For example,
we can display a natural number as a decimal, or a binary, or even a unary.
-/

def repr_Nat_unary: Nat -> String
  | .zero => "0"
  | .succ n => repr_Nat_unary n ++ "1"

def repr_Nat_binary: Nat -> String := sorry
def repr_Nat_decimal: Nat -> String := sorry

/-!
In Lean, to display a term with `#eval`, you have to fulfill the `Repr` typeclass. Fortunately, lean can
infer most `Repr` functions. If you want lean to figure out how to display a term, just typing
`deriving Repr` when defining it.

### Abbreviation
Another technique issue with lean is that `def` always gives a new symbol. If you use it to define a new
type (a term of `Type`), then it will remove all information about the type, i.e., you are then unable
to use the instances for that type.

```lean
def NewNat := Nat
#check (1: NewNat)
```
Lean will complain that `1` is not defined for `NewNat`
```
failed to synthesize instance
  OfNat NewNat 1
```
-/

def NewNat := Nat
-- #check (1: NewNat)
#check (.zero: NewNat)

/-!
To solve the issue, define `NewNat` as an abbreviation, which will always be unfolded when applying.
-/

abbrev NewNat' := Nat
#eval (3: NewNat')

/-!
### Decidability
Now we are able to define the decidability for `even`. A proposition `P` is deciable in intuitionistic
logic iff you can prove either `P` or `¬ P`
-/

inductive MyDecidable (p: Prop) :=
  | isTrue:p -> MyDecidable p
  | isFalse: ¬p -> MyDecidable p

/-!
Certainly, we want it to be a typeclass so that lean will pay attention to the infomation about
decidability.
-/

class inductive MyDecidable' (p: Prop) :=
  | isTrue: p -> MyDecidable' p
  | isFalse: ¬p -> MyDecidable' p


theorem dn_em: forall p: Prop, ¬¬(p∨¬p) := by
  intros p H
  apply H
  right
  intros Hp
  apply H
  left; apply Hp


instance : Decidable (¬¬(p∨¬p)):= by
  apply isTrue
  apply dn_em

#check Decidable
#check even

#check if (¬¬(True ∨ ¬ True)) then true else false

instance: Decidable (even n) := by
  generalize E: evenb n = t
  cases t
  case true =>
    apply isTrue
    apply (evenb_even n E)
  case false =>
    apply isFalse
    apply (evenb_false n E)

#eval if even 4 then true else false

/-!
Lean also provides some useful abbreviations.

A decidable predicate `P: A -> Prop` is a function that for each `a: A`, `P a` is decidable.
-/

abbrev MyDecidablePred {A: Type} (P : A → Prop) := (a : A) -> Decidable (P a)
