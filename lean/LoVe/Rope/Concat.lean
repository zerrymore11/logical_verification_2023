import LoVe.Rope.Defs

/-
## Defs and Theorems about `Rope.concat`

We prove several important properties about the `Rope.concat` operation,
which joins two ropes into a new one by making a `node`.

The theorems below show that `Rope.concat` behaves well with respect to
the semantics (`toString`), length (`length`), and legality (`isLegal`)
of the Rope structure.

The theorems are as follows:

* `Rope_concat_assoc` : Proves that `concat` is associative w.r.t. `toString`.
  e.g.,
    r1 : Rope = concat t1 (concat t2 t3)
    r2 : Rope = concat (concat t1 t2) t2
    then we have, t1.toString = t2.toString

* `Rope_concat_string_invariant` : Shows that the string represented by the
  concatenation is exactly the concatenation of the individual strings.
  i.e.,
    once you concat two ropes, you are concat the string they conveys.

* `Rope_concat_length_invariant` : If both ropes are legal, then their
  concatenation is also legal.

* `Rope_concat_length_comm` : Shows that the total length of the result is
  commutative, even though the actual Rope tree structure is not.

These results help ensure the correctness of rope transformations,
and will be foundational for proving the correctness of operations
like insertion, deletion, and balanced splitting.
-/


def Rope.concat (r1 r2 : Rope) : Rope :=
  Rope.node r1 (Rope.length r1) r2

theorem Rope_concat_assoc (r1 r2 r3 : Rope) :
  Rope.toString (Rope.concat (Rope.concat r1 r2) r3) =
  Rope.toString (Rope.concat r1 (Rope.concat r2 r3)) :=
by
  unfold Rope.toString Rope.concat
  simp [Rope.toString]
  apply String.append_assoc


theorem Rope_concat_string_invariant :
  ∀ (t1 t2 : Rope),
    Rope.toString (Rope.concat t1 t2) = Rope.toString t1 ++ Rope.toString t2 :=
by
  intro t1 t2
  unfold Rope.toString Rope.concat
  simp [Rope.toString]
  cases t1 with
  | leaf a =>
    cases t2
    simp [Rope.toString]
    rfl
  | node l w r =>
    simp [Rope.toString]
    cases t2 with
    | leaf a => simp [Rope.toString]
    | node l' w' r' =>  rfl


theorem Rope_concat_length_invariant :
  ∀ (t1 t2 : Rope),
  Rope.isLegal t1 ∧ Rope.isLegal t2 → Rope.isLegal (Rope.concat t1 t2) :=
by
  intro t1 t2 hleg
  unfold Rope.isLegal Rope.concat
  simp
  exact hleg



theorem Rope_concat_length_comm (r1 r2 : Rope) :
  Rope.length (Rope.concat r1 r2) = Rope.length (Rope.concat r2 r1) :=
by
  unfold Rope.concat
  simp [Rope.length]
  apply Nat.add_comm
