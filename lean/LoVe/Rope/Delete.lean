import LoVe.Rope.Split


/--
## Function and Theorems for Delete Operation

* Function `Rope.delete`
  Deletes a substring from a Rope `r`, starting at position `start` and
  spanning `len` characters.

* Theorem `Rope_delete_string_invariant`
  A deleting a range of characters from a legal Rope has the
  same result as applying `.take` and `.drop` to the flattened string:

* Theorem `Rope_delete_length_invariant`
  If the original rope is legal, then the result of deleting some substring
  from it is also a legal rope.
--/

def Rope.delete (r : Rope) (start len : Nat) : Rope :=
  let (lhs, _) := Rope.split r start
  let (_, rhs) := Rope.split r (start + len)
  Rope.concat lhs rhs


theorem Rope_delete_string_invariant :
  ∀(t : Rope) (start len : ℕ),
    Rope.isLegal t →
      (Rope.delete t start len).toString =
      t.toString.take start ++ t.toString.drop (start+len) :=
by
  intro t start len hleg
  simp [Rope.delete, Rope.concat, Rope.toString]
  have h1 := Rope_split1_eq_take t start hleg
  have h2 := Rope_split2_eq_drop t (start+len) hleg
  simp [h1, h2]


theorem Rope_delete_length_invariant :
  ∀(t : Rope) (start len : ℕ),
    Rope.isLegal t →
      Rope.isLegal (Rope.delete t start len) :=
by
  intro t start len hleg
  simp [Rope.delete, Rope.concat, Rope.isLegal]
  have h1 := Rope_split_length_invariant t start hleg
  have h2 := Rope_split_length_invariant t (start+len) hleg
  exact And.intro (h1.left) (h2.right)
