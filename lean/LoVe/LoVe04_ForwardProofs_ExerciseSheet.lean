/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Exercise 4: Forward Proofs -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Connectives and Quantifiers

1.1. Supply structured proofs of the following theorems. -/

theorem I (a : Prop) :
  a → a :=
  assume ha : a
  show a from ha

theorem K (a b : Prop) :
  a → b → b :=
  assume ha : a
  assume hb : b
  show b from hb

theorem C (a b c : Prop) :
  (a → b → c) → b → a → c :=
  assume habc : a → b → c
  assume hb : b
  assume ha : a
  show c from
    habc ha hb

theorem proj_fst (a : Prop) :
  a → a → a :=
  assume ha : a
  assume ha' : a
  show a from ha


/- Please give a different answer than for `proj_fst`. -/

theorem proj_snd (a : Prop) :
  a → a → a :=
  assume ha : a
  assume ha' : a
  show a from ha'

theorem some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
  assume habc : a → b → c
  assume ha : a
  assume hac : a → c
  assume hb : b
  show c from
    hac ha

/- 1.2. Supply a structured proof of the contraposition rule. -/

theorem contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
  assume hab : a → b
  assume hnb : ¬ b
  assume ha : a
  have hb := hab ha
  hnb hb
  -- hnb hb
  -- pure term mode
  /-
    h : ¬ P <--> h : P → False
    (a → b) → ¬ b → ¬ a <-->
    (a → b) → (b → False) → a → False
  -/
  -- fun hab hnb ha =>
  --   hnb (hab ha)



/- 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

theorem forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  Iff.intro
    ( assume ha : ∀ (x : α), p x ∧ q x
      show (∀x, p x) ∧ (∀x, q x) from
      -- by
      --   apply And.intro
      --   <;>
      --   intro hα
      --   exact And.left (ha hα)
      --   exact And.right (ha hα)
        let hpl : (∀ (x : α), p x) :=
          fix hα : α
          And.left (ha hα)
        let hpr : (∀ (x : α), q x) :=
          fix hα : α
          And.right (ha hα)
        And.intro hpl hpr
    )
    ( assume hr : (∀ (x : α), p x) ∧ ∀ (x : α), q x
      show ∀ (x : α), p x ∧ q x from
        assume hα : α
        let hpl : p hα :=
          And.left hr hα
        let hpr : q hα :=
          And.right hr hα
        And.intro hpl hpr
    )

/- 1.4 (**optional**). Supply a structured proof of the following property,
which can be used to pull a `∀` quantifier past an `∃` quantifier. -/

theorem forall_exists_of_exists_forall {α : Type} (p : α → α → Prop) :
  (∃x, ∀y, p x y) → (∀y, ∃x, p x y) :=
  assume ha : ∃x, ∀y, p x y
  fix y : α
  let ⟨xt, hxt⟩  := ha
  show ∃ x, p x y from
    Exists.intro xt (hxt y)

/- ## Question 2: Chain of Equalities

2.1. Write the following proof using `calc`.

      (a + b) * (a + b)
    = a * (a + b) + b * (a + b)
    = a * a + a * b + b * a + b * b
    = a * a + a * b + a * b + b * b
    = a * a + 2 * a * b + b * b

Hint: This is a difficult question. You might need the tactics `simp` and
`ac_rfl` and some of the theorems `mul_add`, `add_mul`, `add_comm`, `add_assoc`,
`mul_comm`, `mul_assoc`, , and `Nat.two_mul`. -/


theorem binomial_square_t (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
calc
  (a + b) * (a + b) = (a + b) * a + (a + b) * b :=
    by rw [mul_add]
  _ = a * (a + b) + b * (a + b) :=
    by
      rw [mul_comm]
      rw [mul_comm (a + b) b]
  _ = a * a + a * b + b * a + b * b :=
    by
      simp [mul_add]
      rw [<-add_assoc]
  _ = a * a + a * b + a * b + b * b :=
    by rw [mul_comm b a]
  _ = a * a + (a * b + a * b) + b * b :=
    by
      rw [add_assoc (a * a) (a * b) (a * b)]
  _ = a * a + 2 * a * b + b * b :=
    by
      rw [<-Nat.two_mul]
      rw [<-mul_assoc 2 a b]

/- 2.2 (**optional**). Prove the same argument again, this time as a structured
proof, with `have` steps corresponding to the `calc` equations. Try to reuse as
much of the above proof idea as possible, proceeding mechanically. -/

theorem binomial_square₂ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  have h1 : (a + b) * (a + b) = (a + b) * a + (a + b) * b :=
    by rw [mul_add]
  have h2 : (a + b) * a + (a + b) * b = a * (a + b) + b * (a + b) :=
    by
      rw [mul_comm]
      rw [mul_comm (a + b) b]
  have h12 : (a + b) * (a + b) = a * (a + b) + b * (a + b) :=
    by apply Eq.trans h1 h2
  have h3 : a * (a + b) + b * (a + b) = a * a + a * b + b * a + b * b :=
    by
      simp [mul_add]
      rw [<-add_assoc]
  have h13 : (a + b) * (a + b) = a * a + a * b + b * a + b * b :=
    by apply Eq.trans h12 h3
  have h4 : a * a + a * b + b * a + b * b = a * a + a * b + a * b + b * b :=
    by rw [mul_comm b a]
  have h14 : (a + b) * (a + b) = a * a + a * b + a * b + b * b :=
    by apply Eq.trans h13 h4
  have h5 : a * a + a * b + a * b + b * b = a * a + 2 * a * b + b * b :=
    by
      rw [add_assoc (a * a) (a * b) (a * b)]
      rw [<-Nat.two_mul]
      rw [<-mul_assoc 2 a b]
  show (a + b) * (a + b) = a * a + 2 * a * b + b * b from
    by apply Eq.trans h14 h5

#print bind




/- ## Question 3 (**optional**): One-Point Rules

3.1 (**optional**). Prove that the following wrong formulation of the one-point
rule for `∀` is inconsistent, using a structured proof. -/

axiom All.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
  (∀x : α, x = t ∧ P x) ↔ P t

theorem All.proof_of_False :
  False :=
  /- Instantiate axiom with concret terms -/
  have h := All.one_point_wrong true (fun _ => True)
  have h1 : ¬ (∀ x : Bool, x = true) := by
    intro h
    have ht := h false
    contradiction
  have h2 : (∀ x : Bool, x = true) ↔ True := by
    /- Any prop P can be infered from False -/
    apply Iff.intro
    <;>
    contradiction
  have h3 : ∀ x : Bool, x = true := by
    rw [h2]
    trivial
  h1 h3


/- 3.2 (**optional**). Prove that the following wrong formulation of the
one-point rule for `∃` is inconsistent, using a structured proof. -/

axiom Exists.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
  (∃x : α, x = t → P x) ↔ P t

theorem Exists.proof_of_False :
  False :=
  have h := Exists.one_point_wrong 2 (fun n => n > 3)
  have h1 : ¬ (∃ x, x = 2 → x > 3) := by
    intro hx
    have hy := Iff.mp h hx
    contradiction
  have neq : ∃ x, x = 2 → x > 3 := by
    use 0
    intro h
    contradiction
  show False from h1 neq

end LoVe
