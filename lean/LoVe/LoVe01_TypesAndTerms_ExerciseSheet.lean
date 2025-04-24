/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe01_TypesAndTerms_Demo


/- # LoVe Exercise 1: Types and Terms

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Terms

Complete the following definitions, by replacing the `sorry` markers by terms
of the expected type.

Hint: A procedure for doing so systematically is described in Section 1.4 of
the Hitchhiker's Guide. As explained there, you can use `_` as a placeholder
while constructing a term. By hovering over `_`, you will see the current
logical context. -/

def I : α → α :=
  fun a ↦ a

def K : α → β → α :=
  fun a _ ↦ a

def C : (α → β → γ) → β → α → γ :=
  fun ab b a ↦ ab a b

def projFst : α → α → α :=
  fun a _ ↦ a

/- Give a different answer than for `projFst`. -/

def projSnd : α → α → α :=
  fun _ a ↦ a

def someNonsense : (α → β → γ) → α → (α → γ) → β → γ :=
  fun aby a _ b ↦ aby a b


/- ## Question 2: Typing Derivation

Show the typing derivation for your definition of `C` above, on paper or using
ASCII or Unicode art. You might find the characters `–` (to draw horizontal
bars) and `⊢` useful. -/

-- write your solution in a comment here or on paper


/-
-- def C : (α → β → γ) → β → α → γ :=
--   fun ab b a ↦ ab a b
-- Π : context

    —————————————————— Cst   —————————— Cst
    Π ⊢ ab : α → β → γ       Π ⊢ a : α
    ———————————————————————————————————— App
                                    —————————— Cst
                Π ⊢ ab a : β → γ    Π ⊢ b : β
                ——————————————————————————————
                        Π ⊢ ab a b : γ
-/
end LoVe
