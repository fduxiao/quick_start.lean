import QuickStart.MyTactics

/-!
## Predicates with `Bool`
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

theorem double_conv: forall n, exists k, n = if evenb n then double k else (double k).succ := by
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
## evenE is decidable
-/

theorem even_double_evenb: forall n, even_double n -> evenb n = true := by
  intros n H
  unfold even_double at H
  cases H with
  | intro k Hk =>
    rw [Hk]
    apply double_evenb

theorem evenb_even_double: forall n: Nat, evenb n = true -> even_double n := sorry


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


theorem evenb_even: forall n, evenb n = true -> even n := by
  intros n
  induction n
  case zero =>
    intro H
    apply even_z
  case succ m IHm =>
    admit

/-!
### Another example as exercise
-/
