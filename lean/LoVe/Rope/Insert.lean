import LoVe.Rope.Split

/--
## Function and Theorems for Insert Operation

* Function `Rope.insert`
  Inserts a string `s` at index `i` into a Rope `t` to form a new Rope.

* Theorem `Rope_insert_string_invariant`
  The string represented by the rope after insertion is
  exactly what you'd expect: it corresponds to taking the original
  string, inserting `s` at index `i`, and returning the result:

* Theorem `Rope_insert_length_invariant`
  A rope is preserved under insertion:
  if the original rope is legal, then the result of inserting into it
  is also a legal rope.
--/

def Rope.insert (t : Rope) (i : Nat) (s : String) : Rope :=
  let (l, r) := Rope.split t i
  Rope.concat (Rope.concat l (Rope.leaf s)) r


theorem Rope_insert_string_invariant :
  ∀ (t : Rope) (i : ℕ) (s : String),
    Rope.isLegal t → Rope.toString (Rope.insert t i s) =
    String.take (Rope.toString t) i ++ s ++ String.drop (Rope.toString t) i := by
  intro t i s hleg
  simp [Rope.insert]
  simp [Rope.concat, Rope.toString]
  simp [Rope_split1_eq_take t i hleg]
  simp [Rope_split2_eq_drop t i hleg]



theorem Rope_insert_length_invariant (t: Rope) (i : ℕ) (s : String) :
  -- ∀(t: Rope) (i : ℕ) (s : String),
  Rope.isLegal t → Rope.isLegal (Rope.insert t i s) :=
by
  -- intro t i s
  intro hleg
  unfold Rope.insert Rope.concat Rope.split
  cases t with
  | leaf a => simp [Rope.isLegal]
  | node l w r =>
    simp
    by_cases h : i < w
    .
      simp [h]
      simp [Rope.isLegal]
      simp [Rope.isLegal] at hleg
      simp [Rope.concat, Rope.isLegal]
      have h1 := Rope_split_length_invariant l i (And.right hleg.left)
      have h2 := And.intro h1 hleg.right
      simp [h2]
    .
      simp [h]
      simp [Rope.isLegal]
      simp [Rope.isLegal] at hleg
      simp [Rope.concat, Rope.isLegal]
      have h1 := Rope_split_length_invariant r (i-w) (And.right hleg)
      have h' := And.intro  (And.right hleg.left) h1
      simp [h']
