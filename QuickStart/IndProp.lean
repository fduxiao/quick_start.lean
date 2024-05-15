import QuickStart.MyTactics

/-!
## Predicates with `Bool`
-/

def evenb (n: Nat): Bool := match n with
  | .zero => true
  | .succ m => not (evenb m)


#eval evenb 5
#eval evenb 20

theorem not_not_id: forall b: Bool, not (not b) = b := by
  intros b
  cases b
  . rfl
  . rfl

theorem evenb_add_2: forall n, evenb (n + 2) = evenb n := by
  intros n
  compute only [evenb]
  apply not_not_id


/-!
## Predicate with other propositions
-/

def double (n: Nat): Nat := 2 * n
def evenE (n: Nat): Prop := exists k: Nat, n = double k

example: evenE 4 := by
  exists 2

theorem double_evenb: forall n, evenb (double n) = true := by
  intros n
  induction n
  case zero => rfl
  case succ n IHn =>
    admit

theorem double_conv: forall n, n = if evenb n then double k else (double k).succ := sorry

/-!
## evenE is decidable
-/

theorem evenb_evenE: forall n: Nat, evenb n = true -> evenE n := sorry


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
    rw [evenb_add_2]
    exact IHe


theorem evenb_even: forall n, evenb n = true -> even n := by
  intros n
  induction n
  case zero =>
    intro H
    apply even_z
  case succ m IHm =>
    admit
