import LoVe.Rope.Insert
import LoVe.Rope.Rebalance
import LoVe.Rope.Concat
import LoVe.Rope.Delete

/--
## Main Theorem: `evalSeq_invariant`

This theorem asserts that `any infinite sequence of Rope operations`
defined in the context, preserves the legality of the rope.

## Statement:
Given:
1. A legal starting rope `t`
2. A list of operations `ops : List RopeOp`
3. and every `concat` operation in `ops` uses a legal rope

Then, the final Rope produced by sequentially
applying all operations in `ops` is also legal.


This theorem guarantees the global invariant of legality across
arbitrary sequencial compositions of editing operations
such as `insert`, `delete`, `concat`, and `rebalance`.
Note that one *limitation* here is we do not include `split`
operation, thought it also preserves the legality, which
have been proved before.

## Test cases
We add some test cases to show the operations for Rope.
-/

inductive RopeOp : Type
  | insert  (i : ℕ) (s : String)
  | delete  (start len : ℕ)
  | concat  (r : Rope)
  | rebalance


def evalOp : RopeOp → Rope → Rope
  | RopeOp.insert i s, t => Rope.insert t i s
  | RopeOp.delete start len, t => Rope.delete t start len
  | RopeOp.concat r, t => Rope.concat t r
  | RopeOp.rebalance, t => rebalance t


def evalSeq : List RopeOp → Rope → Rope
  | [], t => t
  | op :: ops, t => evalSeq ops (evalOp op t)


lemma evalOp_preserves_legality :
  ∀ (op : RopeOp) (t : Rope),
    Rope.isLegal t →
    (match op with
      -- concat needs r₂ to be legal
      | RopeOp.concat r₂ => Rope.isLegal r₂
      | _ => True) →
    Rope.isLegal (evalOp op t) :=
by
  intro op t hleg
  unfold evalOp
  cases op
  simp; exact Rope_insert_length_invariant _ _ _ hleg
  simp; exact Rope_delete_length_invariant _ _ _ hleg
  simp; {intro r; exact Rope_concat_length_invariant _ _ (And.intro hleg r)}
  simp; exact Rope_rebalance_length_invariant t


theorem evalSeq_invariant :
  ∀ (ops : List RopeOp) (t : Rope),
    Rope.isLegal t →
    (∀ r₂, RopeOp.concat r₂ ∈ ops → Rope.isLegal r₂) →
    Rope.isLegal (evalSeq ops t) :=
by
  intro ops t hleg
  induction ops generalizing t with
  | nil =>
    unfold evalSeq
    simp; exact hleg
  | cons x xs ih =>
    intro r
    simp [evalSeq]
    have hstart : (evalOp x t).isLegal = true := by
      apply evalOp_preserves_legality
      exact hleg
      cases x
      repeat' simp
      aesop
    apply ih
    exact hstart
    intro rx rh'
    exact r rx (List.mem_cons_of_mem x rh')




def t1 := Rope.leaf "12345"
def t2 := Rope.leaf "678910"
def t3 := Rope.leaf "123"
def t4 := Rope.leaf "12345"
def t5 := Rope.leaf "12"
def t6 := Rope.leaf "123"

def unbalanced :=
  Rope.node t1 5 (
    Rope.node t2 6 (
      Rope.node t3 3 (
        Rope.node t4 5 (
          Rope.node t5 2 t6
        )
      )
    )
  )


#eval unbalanced.isLegal

#eval unbalanced.toString

def rsplit := Rope.split unbalanced 5

#eval (Rope.delete unbalanced 3 2)

#eval unbalanced

#eval rsplit.fst

#eval rsplit.snd

#eval rsplit.fst.toString

#eval rsplit.snd.toString


def test_rope :=
  (Rope.node t1 5 t2)

def ss := "1234567"
#eval ss
#eval test_rope.toString
#eval test_rope.isLegal
#check ss.toList[123]?
