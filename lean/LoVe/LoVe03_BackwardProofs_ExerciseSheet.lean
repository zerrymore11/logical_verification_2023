/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_Demo


/- # LoVe Exercise 3: Backward Proofs

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace BackwardProofs

/- ## Question 1: Connectives and Quantifiers

1.1. Carry out the following proofs using basic tactics.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 3.3 in the Hitchhiker's Guide. -/

theorem I (a : Prop) :
  a → a :=
by
  intro h
  exact h

theorem K (a b : Prop) :
  a → b → b :=
by
  intro _ hb
  exact hb

theorem C (a b c : Prop) :
  (a → b → c) → b → a → c :=
by
  intro habc hb ha
  exact habc ha hb

theorem proj_fst (a : Prop) :
  a → a → a :=
by
  intro ha _
  exact ha

/- Please give a different answer than for `proj_fst`: -/

theorem proj_snd (a : Prop) :
  a → a → a :=
by
  intro _ ha
  exact ha

theorem some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
by
  intro _ ha hac _
  apply hac ha

/- 1.2. Prove the contraposition rule using basic tactics. -/

theorem contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
by
  intro h1 h2
  intro h3
  apply h2
  exact h1 h3
  -- forward proof using contradiction is more intuitive
  -- have hb : b := hab ha
  -- contradiction

/- 1.3. Prove the distributivity of `∀` over `∧` using basic tactics.

Hint: This exercise is tricky, especially the right-to-left direction. Some
forward reasoning, like in the proof of `and_swap_braces` in the lecture, might
be necessary. -/

theorem forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
by
  apply Iff.intro
  { intro hx
    apply And.intro
    intro ha
    apply And.left
    exact hx ha
    intro ha
    apply And.right
    exact hx ha }
  { intro hc ha
    apply And.intro
    apply And.left hc ha
    apply And.right hc ha }




/- ## Question 2: Natural Numbers

2.1. Prove the following recursive equations on the first argument of the
`mul` operator defined in lecture 1. -/

#check mul


-- theorem mul_succ (a b : ℕ) :
--   mul a (Nat.succ b) = add (mul a b) a :=
-- by
--   simp [mul]
--   simp [add_comm]

theorem mul_succ (a b : ℕ) :
  mul (Nat.succ a) b = add (mul a b) b :=
by
  induction b with
  | zero => rfl
  | succ nb ih =>
    simp [add, mul]
    simp [add_succ]
    simp [ih]
    simp [add_assoc]


theorem mul_zero (n : ℕ) :
  mul 0 n = 0 :=
by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [mul]
    simp [add_zero]
    exact ih

#check add_succ

-- def mul : ℕ → ℕ → ℕ
--   | _, Nat.zero   => Nat.zero
--   | m, Nat.succ n => add m (mul m n)

/- 2.2. Prove commutativity and associativity of multiplication using the
`induction` tactic. Choose the induction variable carefully. -/

theorem mul_comm (m n : ℕ) :
  mul m n = mul n m :=
by
  induction n with
  | zero =>
    rw [mul_zero]
    rw [mul]
  | succ nx ih =>
    simp [mul]
    rw [ih]
    rw [add_comm]
    rw [mul_succ]

/-
 - Use pattern matching style
 -/
theorem mul_comm_t :
  ∀m n : ℕ, mul m n = mul n m
  | m, 0 => by
    rw [mul_zero]
    rw [mul]
  | m, n' + 1 => by
    simp [mul]
    rw [mul_comm_t m n']
    rw [add_comm]
    rw [mul_succ]


theorem mul_assoc (l m n : ℕ) :
  mul (mul l m) n = mul l (mul m n) :=
by
  induction n with
  | zero =>
    rw [mul_comm, mul_zero]
    rfl
  | succ n' ih =>
    simp [mul, add]
    rw [ih, mul_add]

/- 2.3. Prove the symmetric variant of `mul_add` using `rw`. To apply
commutativity at a specific position, instantiate the rule by passing some
arguments (e.g., `mul_comm _ l`). -/

theorem add_mul (l m n : ℕ) :
  mul (add l m) n = add (mul n l) (mul n m) :=
by
  rw [mul_comm (add l m) n]
  rw [mul_add]


/- ## Question 3 (**optional**): Intuitionistic Logic

Intuitionistic logic is extended to classical logic by assuming a classical
axiom. There are several possibilities for the choice of axiom. In this
question, we are concerned with the logical equivalence of three different
axioms: -/

def ExcludedMiddle : Prop :=
  ∀a : Prop, a ∨ ¬ a

def Peirce : Prop :=
  ∀a b : Prop, ((a → b) → a) → a

def DoubleNegation : Prop :=
  ∀a : Prop, (¬¬ a) → a

/- For the proofs below, avoid using theorems from Lean's `Classical` namespace.

3.1 (**optional**). Prove the following implication using tactics.

Hint: You will need `Or.elim` and `False.elim`. You can use
`rw [ExcludedMiddle]` to unfold the definition of `ExcludedMiddle`,
and similarly for `Peirce`. -/

theorem Peirce_of_EM :
  ExcludedMiddle → Peirce :=
by
  rw [ExcludedMiddle, Peirce]
  intro h1 h2 h3 h4
  by_contra hna  -- We suppose that: ¬a
  apply hna
  apply h4
  intro hh2
  contradiction



/- 3.2 (**optional**). Prove the following implication using tactics. -/

theorem DN_of_Peirce :
  Peirce → DoubleNegation :=
by
  rw [DoubleNegation, Peirce]
  intro h1 h2 h3
  by_contra hna
  apply hna
  contradiction

/- We leave the remaining implication for the homework: -/

namespace SorryTheorems


/--
- I failed this case...
-/
theorem EM_of_DN :
  DoubleNegation → ExcludedMiddle :=
by
  rw [DoubleNegation, ExcludedMiddle]
  intro h1 h2
  by_cases h : h2
  . left
    exact h
  . right
    exact h


end SorryTheorems

end BackwardProofs

end LoVe
