import LoVe.Rope.Defs

/--
## Function and Theorem for Insert Operation

* Function `Rope.index`
  retrieves the character at a given position `i` in a Rope structure.

* Theorem `Rope_index_func_correct`
  proves that `Rope.index` behaves correctly with respect to the
  flattened string representation of the rope.
--/

def Rope.index : Rope → Nat → Option Char
  | Rope.leaf s, i      => s.toList[i]?
  | Rope.node l w r, i  =>
    if i < w then
      index l i
    else
      index r (i - w)


theorem Rope_index_func_correct:
  ∀(r : Rope) (i : ℕ), Rope.isLegal r →
    Rope.index r i = (Rope.toString r).toList[i]? :=
by
  intro r i hl
  rw [Rope.isLegal.eq_def] at hl
  simp
  cases r with
  | leaf s =>
    unfold Rope.index
    simp [Rope.toString]
  | node l w r =>
    simp at hl
    have hlength := And.left hl.left
    have hlleg := And.right hl.left
    have hrleg := And.right hl
    unfold Rope.index
    by_cases h : i < w
    . simp [h]
      simp [Rope_index_func_correct l i hlleg]
      simp [Rope.toString, Rope.index]
      simp [List.getElem?_append]
      have index : w = l.toString.data.length := by
        simp [hlength]
        exact Rope_length_eq_string_length l hlleg
      rw [index] at h
      rw [String.length_data] at h
      simp [h]
    .
      simp [h]
      simp [Rope_index_func_correct r (i - w) hrleg]
      simp [Rope.toString]
      simp [List.getElem?_append]
      have index : w = l.toString.data.length := by
        simp [hlength]
        exact Rope_length_eq_string_length l hlleg
      rw [index] at h
      rw [String.length_data] at h
      simp [h]
      aesop
