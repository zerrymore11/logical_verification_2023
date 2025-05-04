import Aesop
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.String.Basic
import Mathlib.Data.String.Lemmas

open Lean
open Lean.Parser
open Lean.Parser.Term
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax


/-
## Definitions for Rope

We define the `Rope` type and some of its basic functions
used to show its basic properties.

The functions are listed below:
* `Rope.length` : show the total string length that Rope conveys

* `Rope.toString` : present the string corresponding to Rope

* `Rope.isLegal` : judge whether a given rope is legal, i.e., the weight
  `w` equals to its length of left rope.

* `Rope.toString` : present the string corresponding to Rope

* `prettyPrintStr` : a util which can show the graph structure of a give rope

-/

inductive Rope where
  | leaf  : String → Rope
  | node  : Rope → Nat → Rope → Rope
  deriving Repr

def Rope.length : Rope → Nat
  | Rope.leaf s        => s.length
  | Rope.node _ w r    => w + Rope.length r


/-
## `Rope.isLegal`

The `Rope.isLegal` function checks whether a given Rope satisfies the
structural invariant required for correctness.

A Rope is considered **legal** if:

* A `leaf` node is always legal by definition.
* A `node l w r` is legal if:
  - `w == Rope.length l` (i.e., the stored weight matches the length of the left subtree),
  - `l` itself is legal,
  - `r` itself is legal.
-/
def Rope.isLegal : Rope → Bool
  | Rope.leaf _        => true
  | Rope.node l w r    =>
    w == (Rope.length l) && Rope.isLegal l && Rope.isLegal r


def Rope.toString : Rope → String
  | Rope.leaf s => s
  | Rope.node l _ r => Rope.toString l ++ Rope.toString r


/-
Function `Rope.prettyPrintStr` is used to produce
a structured and human-readable visual representation
of a Rope's tree structure.
--/

def indent (n : Nat) : String :=
  String.join (List.replicate n "  ")

def Rope.prettyPrint : Rope → Nat → List String
  | Rope.leaf s, depth => [indent depth ++ s]
  | Rope.node l _ r, depth =>
    let this := indent depth ++ "++"
    let leftStrs := Rope.prettyPrint l (depth + 1)
    let rightStrs := Rope.prettyPrint r (depth + 1)
    this :: (leftStrs ++ rightStrs)

def Rope.prettyPrintStr (t : Rope) : String :=
  String.intercalate "\n" (Rope.prettyPrint t 0)


theorem toString_len_eq_Rope_len:
  ∀(t : Rope),
    Rope.isLegal t → (Rope.toString t).length = Rope.length t :=
by
  intro t hleg
  unfold Rope.length
  cases t with
  | leaf n =>
    rfl
  | node l w r =>
    simp
    simp [Rope.isLegal] at hleg
    have lleg := And.right hleg.left
    have rleg := And.right hleg
    have wlen := And.left hleg.left
    simp [Rope.toString]
    have hll : l.toString.length = w := by
      simp [wlen]
      exact toString_len_eq_Rope_len l lleg
    simp [hll]
    exact toString_len_eq_Rope_len r rleg


theorem Rope_length_eq_string_length:
  ∀(r : Rope), r.isLegal → r.length = r.toString.data.length :=
by
  intro r hr
  unfold Rope.isLegal at hr
  unfold Rope.length Rope.toString
  cases r with
  | leaf n =>
    rfl
  | node l w r =>
    simp [Rope.length]
    simp at hr
    have wlength := And.left hr.left
    have lleg := And.right hr.left
    have rleg := And.right hr
    rw [wlength]
    simp [Rope_length_eq_string_length l lleg]
    simp [Rope_length_eq_string_length r rleg]

def r1 := Rope.leaf "12345"
def r2 := Rope.leaf "678910"
def r3 := Rope.leaf "123"
def r4 := Rope.leaf "12345"
def r5 := Rope.leaf "12"
def r6 := Rope.leaf "123"

def unbalancedRope :=
  Rope.node r1 5 (
    Rope.node r2 6 (
      Rope.node r3 3 (
        Rope.node r4 5 (
          Rope.node r5 2 r6
        )
      )
    )
  )

#eval IO.println (Rope.prettyPrintStr unbalancedRope)
