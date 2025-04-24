/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe Exercise 6: Inductive Predicates

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Even and Odd

The `Even` predicate is `True` for even numbers and `False` for odd numbers. -/

#check Even

/- We define `Odd` as the negation of `Even`: -/

def Odd (n : ℕ) : Prop :=
  ¬ Even n

/- 1.1. Prove that 1 is odd and register this fact as a simp rule.

Hint: `cases` or `induction` is useful to reason about hypotheses of the form
`Even …`. -/

@[simp] theorem Odd_1 :
  Odd 1 :=
by
  intro h
  cases h

/- 1.2. Prove that 3 and 5 are odd. -/

-- enter your answer here

/- 1.3. Complete the following proof by structural induction. -/

theorem Even_two_tactic_mode :
  ∀m : ℕ, Even (2 * m) :=
by
  intro h
  induction h with
  | zero =>
    apply Even.zero
  | succ n ih =>
    simp [Nat.mul_succ]
    apply Even.add_two
    exact ih

-- theorem Even_two :
--   ∀m : ℕ, Even (2*m)
--   | 0     => Even.zero
--   | n + 1 => by
--     induction n with
--     | zero =>
--       apply Even.add_two
--       apply Even.zero
--     | succ n ih =>
--       simp [Nat.mul_succ]
--       apply Even.add_two
--       exact ih
theorem Even_two :
  ∀ m : ℕ, Even (2 * m)
  | 0     => Even.zero
  | (c + 1) => Even.add_two (2 * c) (Even_two c)


theorem Even_two_match (m : ℕ) : Even (2 * m) :=
  match m with
  | 0     => Even.zero
  | (c + 1) => by
    apply Even.add_two (2 * c) (Even_two_match c)

theorem foo_match (n : ℕ) : n = 0 ∨ n > 0 :=
  match n with
  | 0 => Or.inl rfl
  | n + 1 => Or.inr (Nat.zero_lt_succ n)

theorem foo : (n : Nat) → (n = 0 ∨ n > 0)
| 0 => by
  -- tactic mode inside recursion
  simp
| n+1 =>
  -- term mode inside recursion
  Or.inr (Nat.zero_lt_succ n)




/- ## Question 2: Tennis Games

Recall the inductive type of tennis scores from the demo: -/

#check Score

/- 2.1. Define an inductive predicate that returns `True` if the server is
ahead of the receiver and that returns `False` otherwise. -/

inductive ServAhead : Score → Prop
  | normal    : ∀m n: Nat, m > n -> ServAhead (Score.vs m n)
  | advAhead  : ServAhead Score.advServ
  | gameAhead : ServAhead Score.gameServ
  -- enter the missing cases here

/- 2.2. Validate your predicate definition by proving the following theorems. -/

theorem ServAhead_vs {m n : ℕ} (hgt : m > n) :
  ServAhead (Score.vs m n) :=
  ServAhead.normal m n hgt


theorem ServAhead_advServ :
  ServAhead Score.advServ :=
  ServAhead.advAhead

theorem not_ServAhead_advRecv :
  ¬ ServAhead Score.advRecv :=
by
  intro h
  cases h

theorem ServAhead_gameServ :
  ServAhead Score.gameServ :=
  ServAhead.gameAhead

theorem not_ServAhead_gameRecv :
  ¬ ServAhead Score.gameRecv :=
  fun h =>
    nomatch h

/- 2.3. Compare the above theorem statements with your definition. What do you
observe? -/

-- enter your answer here


/- ## Question 3: Binary Trees

3.1. Prove the converse of `IsFull_mirror`. You may exploit already proved
theorems (e.g., `IsFull_mirror`, `mirror_mirror`). -/

#check IsFull_mirror
#check mirror_mirror

theorem mirror_IsFull {α : Type} :
  ∀t : BTree α, IsFull (mirror t) → IsFull t :=
by
  intro t h
  have h' : IsFull (mirror (mirror t)) := IsFull_mirror (mirror t) h
  rw [mirror_mirror] at h'
  exact h'

/- 3.2. Define a `map` function on binary trees, similar to `List.map`. -/

-- inductive BTree (α : Type) : Type where
--   | empty : BTree α
--   | node  : α → BTree α → BTree α → BTree α

-- def map {α : Type} {β : Type} (f : α → β) : List α → List β
--   | [] => []
--   | x :: xs => f x :: map f xs

def BTree.map {α β : Type} (f : α → β) : BTree α → BTree β
  | BTree.empty => BTree.empty
  | BTree.node x l r => BTree.node (f x) (map f l) (map f r)

/- 3.3. Prove the following theorem by case distinction. -/

-- theorem mirror_Eq_empty_Iff {α : Type} :
--   ∀t : BTree α, mirror t = BTree.empty ↔ t = BTree.empty
--   | BTree.empty      => by simp [mirror]
--   | BTree.node _ _ _ => by simp [mirror]

theorem BTree.map_eq_empty_iff {α β : Type} (f : α → β) :
  ∀t : BTree α, BTree.map f t = BTree.empty ↔ t = BTree.empty :=
by
  intro ht
  apply Iff.intro
  { intro hht
    cases ht with
    | empty => rfl
    | node x l r => contradiction}
  { intro hht
    rw [hht]
    simp [BTree.map] }

/- 3.4 (**optional**). Prove the following theorem by rule induction. -/

-- inductive IsFull {α : Type} : BTree α → Prop where
--   | empty : IsFull BTree.empty
--   | node (a : α) (l r : BTree α)
--       (hl : IsFull l) (hr : IsFull r)
--       (hiff : l = BTree.empty ↔ r = BTree.empty) :
--     IsFull (BTree.node a l r)

theorem BTree.map_mirror {α β : Type} (f : α → β) :
  ∀t : BTree α, IsFull t → IsFull (BTree.map f t) :=
by
  intro t ht
  induction ht with
  | empty =>
    simp [map]
    exact IsFull.empty
  | node a l r hiff =>
    simp [map]
    apply IsFull.node
    { exact hl_ih }
    { exact hr_ih }
    { apply Iff.intro
      { intro hs
        have ltr := Iff.mp (map_eq_empty_iff f l)
        have l_eq_empty := ltr hs
        have hiff_l := Iff.mp hiff_1
        have r_eq_empty := hiff_l l_eq_empty
        have rtl := Iff.mpr (map_eq_empty_iff f r)
        exact rtl r_eq_empty }
      { intro hs
        have ltr := Iff.mp (map_eq_empty_iff f r)
        have r_eq_empty := ltr hs
        have hiff_r := Iff.mpr hiff_1
        have l_eq_empty := hiff_r r_eq_empty
        have rtl := Iff.mpr (map_eq_empty_iff f l)
        exact rtl l_eq_empty } }

end LoVe
