import LoVe.Rope.Concat


/--
## Function and Theorems for Rope Split Operation

### Lemmas

* Aux₁: `String_take_eq_list_take` & `String_drop_eq_list_drop`
  The `take`/`drop` operations on a `String` corresponds exactly
  to the `List.take`/`List.drop` operation on its underlying
  `String.data` representation.

  These two lemmas are useful when converting between `String` operations
  and list-based reasoning in proofs about Ropes and string manipulation.

* `string_take_drop_eq_id`
  Asserts that `take i ++ drop i = original`.

* `Rope_split1_eq_take`
  The first component of the split corresponds to
  taking the prefix of the rope's string up to index `i`.

* `Rope_split2_eq_drop`
  The second component of the split corresponds to
  dropping the prefix of length `i` from the rope's string.


### Theorems

* `Rope_split_string_invariant`
  Splitting and then concatenating the parts reproduces the original string:
  Rope.toString t = Rope.toString t₁ ++ Rope.toString t₂, where
  (t₁, t₂) :=  Rope.split t

* `Rope_split_length_invariant`
  Spliting a Rope always produces two lega Ropes.
--/


def Rope.split : Rope → Nat → Rope × Rope
  | Rope.leaf s, i =>
    let leftStr := s.take i
    let rightStr := s.drop i
    (Rope.leaf leftStr, Rope.leaf rightStr)
  | Rope.node l w r, i =>
    if i < w then
      let (l1, l2) := Rope.split l i
      let newRight := Rope.concat l2 r
      (l1, newRight)
    else
      let (r1, r2) := Rope.split r (i - w)
      let newLeft := Rope.concat l r1
      (newLeft, r2)


lemma string_take_data_eq :
  ∀(s : String) (i : ℕ),
    (s.take i).data = List.take i s.data :=
by
  intro s i
  cases s with
  | mk l =>
    cases l with
    | nil => simp[String.data]
    | cons x xs => simp

lemma string_drop_data_eq :
  ∀(s : String) (i : ℕ),
    (s.drop i).data = List.drop i s.data :=
by
  intro s i
  cases s with
  | mk l =>
    cases l with
    | nil => simp[String.data]
    | cons x xs => simp


lemma String_take_eq_list_take (ss : String) (i : ℕ):
  ss.take i = String.mk ((ss.data.take i)) :=
by
  have h := string_take_data_eq (ss) i
  rw [<-h]


lemma String_drop_eq_list_drop (ss : String) (i : ℕ):
  ss.drop i = String.mk ((ss.data.drop i)) :=
by
  have h := string_drop_data_eq (ss) i
  rw [<-h]


lemma string_take_drop_eq_id:
  ∀(n : String)(i : ℕ), n.take i ++ n.drop i = n:=
by
  intro n i
  have g := String.congr_append (n.take i) (n.drop i)
  have h : n.take i ++ n.drop i = String.mk ((n.data.take i) ++ (n.data.drop i)) := by
    rw [g]
    simp [String.data_append]
  rw [h]
  rw [List.take_append_drop]


lemma Rope_split1_eq_take :
   ∀ (t : Rope) (i : ℕ),
    Rope.isLegal t →
      (Rope.toString t).take i = (t.split i).fst.toString :=
by
  intro t i ht
  unfold Rope.split
  simp
  cases t with
  | leaf s =>
    rfl
  | node l w r =>
    simp
    by_cases h : i < w
    .
      simp [h]
      simp [Rope.toString]
      simp [Rope.isLegal] at ht
      have wlen := And.left ht.left
      rw [wlen] at h
      have htem := Rope_split1_eq_take l i
      rw [<-htem]
      have ilen : i < l.toString.length := by
        have hh := toString_len_eq_Rope_len l (And.right ht.left)
        rw [<-hh] at h
        exact h
      simp [String_take_eq_list_take]
      apply Or.inr
      exact Nat.le_of_lt ilen
      exact And.right ht.left
    .
      simp [h]
      simp [Rope.toString]
      simp [Rope.isLegal] at ht
      have wlen := And.left ht.left
      have htem := Rope_split1_eq_take r (i-w)
      simp [Rope.concat, Rope.toString]
      have g:= htem (And.right ht)
      simp [String.take_eq]
      simp [List.take_append_eq_append_take]
      have wll : w = l.toString.length := by
        have : l.length = l.toString.length := Rope_length_eq_string_length l (And.right ht.left)
        simp [wlen]
        exact this
      rw [wll]
      rw [wll] at g
      rw [<-g]
      simp [String.congr_append]
      rw [<-wll]
      aesop

lemma Rope_split2_eq_drop :
  ∀ (t : Rope) (i : ℕ),
    Rope.isLegal t →
      (t.split i).2.toString = t.toString.drop i :=
by
  intro t i ht
  unfold Rope.split
  simp
  cases t with
  | leaf s =>
    rfl
  | node l w r =>
    simp
    by_cases h : i < w
    . simp [h]
      simp [Rope.concat, Rope.toString]
      simp [String.drop_eq]
      simp [Rope.isLegal] at ht
      have htem := Rope_split2_eq_drop l i (And.right ht.left)
      simp [String.congr_append]
      have wlen := And.left (ht.left)
      have g := Rope_length_eq_string_length l (And.right ht.left)
      rw [g] at wlen
      rw [wlen] at h
      have h' := Nat.le_of_lt h
      rw [List.drop_append_of_le_length h']
      rw [<-string_drop_data_eq]
      simp [htem]
    . simp [h]
      simp [Rope.concat, Rope.toString]
      simp [String.drop_eq]
      simp [Rope.isLegal] at ht
      have htem := Rope_split2_eq_drop r (i-w) (And.right ht)
      simp at h
      have wlen := And.left (ht.left)
      have g := Rope_length_eq_string_length l (And.right ht.left)
      rw [g] at wlen
      rw [wlen] at h
      simp [List.drop_append_eq_append_drop]
      simp [List.drop_eq_nil_of_le h]
      rw [wlen]
      rw [<-String_drop_eq_list_drop]
      rw [<-wlen]
      rw [<-g] at wlen
      have this := toString_len_eq_Rope_len l (And.right ht.left)
      simp [this, wlen]
      rw [<-wlen]
      exact htem


theorem Rope_split_string_invariant :
  ∀ (t : Rope) (n : ℕ),
    let (t1, t2) := Rope.split t n
    Rope.toString t = Rope.toString t1 ++ Rope.toString t2 :=
by
  intro t n
  unfold Rope.split
  simp [Rope.split]
  cases t with
  | leaf n =>
    simp [Rope.toString]
    simp [string_take_drop_eq_id n _]
  | node l w r =>
    simp
    by_cases h : n < w
    .
      simp [h]
      -- let (t1', t2') :=  (l.split n)
      have hsubl : Rope.toString l = Rope.toString (l.split n).fst ++ Rope.toString (l.split n).snd := by
        simp [Rope_split_string_invariant l n]
      rw [Rope.toString]
      simp [Rope.concat, Rope.toString]
      rw [hsubl]
      simp [String.append_assoc]
    .
      simp [h]
      have hsubr : Rope.toString r = Rope.toString (r.split (n-w)).fst ++ Rope.toString (r.split (n-w)).snd := by
        simp [Rope_split_string_invariant r (n-w)]
      rw [Rope.toString]
      simp [Rope.concat, Rope.toString]
      rw [hsubr]
      simp [String.append_assoc]



theorem Rope_split_length_invariant :
  ∀(t: Rope) (i : ℕ),
  Rope.isLegal t → Rope.isLegal ((Rope.split t i).fst) ∧ Rope.isLegal ((Rope.split t i).snd) :=
by
  intro t i hleg
  unfold Rope.isLegal at hleg
  cases t with
  | leaf a =>
    simp at hleg
    simp [Rope.split]
    simp [Rope.isLegal]
  | node l w r =>
    simp at hleg
    apply And.intro
    { have hlleg := And.right (And.left hleg)
      have hrrleg := And.right hleg
      simp [Rope.split]
      by_cases h : i < w
      . simp [h]
        exact And.left (Rope_split_length_invariant l i hlleg)
      . simp [h]
        unfold Rope.concat
        simp [Rope.isLegal]
        have htemp := by
          apply And.left (Rope_split_length_invariant r (i-w) hrrleg)
        exact And.intro hlleg htemp }
    { have hlleg := And.right (And.left hleg)
      have hrrleg := And.right hleg
      simp [Rope.split]
      by_cases h : i < w
      . simp [h]
        unfold Rope.concat
        simp [Rope.isLegal]
        have htemp := by
          apply And.right (Rope_split_length_invariant l i hlleg)
        exact And.intro htemp hrrleg
      . simp [h]
        exact And.right (Rope_split_length_invariant r (i-w) hrrleg)  }
