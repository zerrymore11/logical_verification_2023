import LoVe.Rope.Defs


/--
## Function and Theorem for Rebalance Operation

### Functions:

* `Rope.flatten`
  Flattens a Rope into a list of strings by doing an in-order traversal.
  Used as an intermediate step before reconstruction.

* `buildBalanced`
  Recursively builds a balanced Rope from a list of strings by splitting
  the list at its midpoint and building left/right subtrees.

* `rebalance` ≈ `flatten` + `buildBalanced`
  Rebalances a Rope by first `flattening` it into a list of strings and
  then rebuilding it with `buildBalanced`.

* Aux function: `stringJoin`
  Concatenates a list of strings into a single `String`.
  This is used to relate the behavior of `flatten` and `toString`.
  e.g., ["hello", "world", "!"].stringJoin = "hello,world!"

### Lemmas and Theorems:

* `join_tail_append` and `join_distribute`
  `stringJoin` distributes over `++`, useful in flatten proofs.

* `toString_eq_join_flatten`
  Converting a Rope to a string is equivalent to flattening it
  and joining the resulting list of strings.

* `buildBalanced_corrct`
  Building a Rope from a list of strings using `buildBalanced`
  results in a Rope whose `toString` equals the concatenation of the list.

* `buildBalance_length_invariant`
  Proves that `buildBalanced` always constructs a legal Rope
  (i.e., it satisfies `Rope.isLegal`).

* `Rope_rebalance_string_invariant`
  Rebalancing a Rope does not change the string it represents.

* `Rope_rebalance_length_invariant`
  Rebalancing a Rope always produces a legal Rope.

--/


def Rope.flatten: Rope → List String
  | Rope.leaf s => [s]
  | Rope.node l _ r => flatten l ++ flatten r


def buildBalanced : List String → Rope
  | [] => Rope.leaf ""
  | x :: xs =>
    if h : xs.isEmpty then
      Rope.leaf x
    else
      let mid       := (x :: xs).length / 2
      let left      := (x :: xs).take mid
      let right     := (x :: xs).drop mid
      let leftRope  := buildBalanced left
      let rightRope := buildBalanced right
      Rope.node leftRope (Rope.length leftRope) rightRope
termination_by ss => ss.length
decreasing_by
  simp_wf
  { apply Nat.div_lt_self
    apply Nat.zero_lt_of_ne_zero
    simp
    simp  }
  { simp
    cases xs with
    | nil =>
      simp at h
    | cons x' xs' =>
      simp [List.length] }

/--
Function `rebalance`
  transforms a Rope into a balanced Rope by first flattening it into
  a list of strings and then rebuilding it using `buildBalanced`.
-/
def rebalance (r : Rope) : Rope :=
  buildBalanced (Rope.flatten r)


def stringJoin : List String → String
  | [] => ""
  | s :: ss => s ++ (stringJoin ss)

/-
The recursion direction is inconsistent with def,
so we need another lemma.
-/
lemma join_tail_append (l : List String) (x : String) :
  stringJoin (l ++ [x]) = stringJoin l ++ x :=
by
  induction l with
  | nil =>
    simp [stringJoin]
  | cons y ys ih =>
    simp [stringJoin, ih, List.append_assoc]
    simp [String.append_assoc]


lemma join_distribute (l r : List String):
  stringJoin l ++ stringJoin r = stringJoin (l ++ r) :=
by
  induction r generalizing l with
  | nil =>
    simp [stringJoin]
  | cons x xs ih =>
    rw [<-List.singleton_append]
    rw [<-ih [x]]
    rw [<-List.append_assoc]
    rw [<-String.append_assoc (stringJoin l) (stringJoin [x]) (stringJoin xs)]
    rw [<-ih (l ++ [x])]
    simp [stringJoin]
    simp [join_tail_append]


lemma fold_empty (l : List String):
  List.foldl (fun r s => r ++ s) "" l = String.join  l :=
by
  rfl


lemma stringJoin_concat :
  ∀ (l₁ l₂ : List String),
    stringJoin (l₁ ++ l₂) = stringJoin l₁ ++ stringJoin l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; simp [stringJoin]
  | cons x xs ih =>
    intro l₂
    simp [stringJoin, List.cons_append, ih]
    rw [String.append_assoc]


lemma toString_eq_join_flatten:
  ∀(t : Rope),
    Rope.toString t = stringJoin (Rope.flatten t) := by
  intro t
  induction t with
  | leaf s =>
    simp [Rope.toString, Rope.flatten]
    simp [stringJoin]
  | node l r w ih_l ih_r =>
    simp [Rope.toString]
    simp [ih_l, ih_r]
    simp [Rope.flatten]
    simp [join_distribute]


lemma buildBalanced_corrct :
  ∀(ss : List String),
    Rope.toString (buildBalanced ss) = stringJoin ss :=
by
  intro ss
  cases ss with
  | nil =>
    unfold Rope.toString buildBalanced
    rfl
  | cons x xs =>
    unfold Rope.toString buildBalanced
    cases h : xs.isEmpty with
    | true =>
      simp[h]
      have hxs : xs = [] := by
        cases xs with
        | nil => rfl
        | cons hd tl =>
          simp at h
      rw [hxs]
      simp [stringJoin]
    | false =>
      simp
      let mid := (x :: xs).length / 2
      let left := (x :: xs).take mid
      let right := (x :: xs).drop mid
      have ih_left := by exact buildBalanced_corrct left
      have ih_right := by exact buildBalanced_corrct right
      calc
        (buildBalanced left).toString ++ (buildBalanced right).toString
          = stringJoin left ++ stringJoin right := by rw [ih_left, ih_right]
        _ = stringJoin (left ++ right) := by rw [stringJoin_concat]
        _ = stringJoin (x :: xs) := by rw [List.take_append_drop mid (x :: xs)]
termination_by ss => ss.length
decreasing_by
  simp_wf
  { have : tail.length > 0 := by
      cases tail with
      | nil =>
        simp
        contradiction
      | cons t' ts' =>
        simp
    apply Nat.div_lt_self
    simp; simp  }
  { simp
    cases tail with
    | nil =>
      simp
      contradiction
    | cons t' ts' =>
      simp  }


lemma buildBalance_length_invariant :
  ∀(t: List String), Rope.isLegal (buildBalanced t) :=
by
  intro t
  unfold buildBalanced
  simp
  cases t with
  | nil =>
    simp[Rope.isLegal]
  | cons x xs =>
    simp
    cases xs with
    | nil => simp[Rope.isLegal]
    | cons y ys =>
      simp
      simp [Rope.isLegal]
      let mid := (x :: y :: ys).length / 2
      let left := (x :: y :: ys).take mid
      let right := (x :: y :: ys).drop mid
      apply And.intro
      . apply buildBalance_length_invariant left
      . exact buildBalance_length_invariant right
termination_by t => t.length



theorem Rope_rebalance_string_invariant :
  ∀t: Rope,
    Rope.toString t = Rope.toString (rebalance t) :=
by
  intro t
  simp [rebalance, buildBalanced]
  rw [buildBalanced_corrct]
  rw [toString_eq_join_flatten]


theorem Rope_rebalance_length_invariant :
  ∀(t: Rope), Rope.isLegal (rebalance t) :=
by
  intro t
  unfold rebalance
  exact buildBalance_length_invariant (Rope.flatten t)
