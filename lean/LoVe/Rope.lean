import Std.Data.List.Basic
import Std.Data.List.Init.Lemmas
import Mathlib.Tactic.Linarith

inductive Rope
  | leaf  : String → Rope
  | node  : Rope → Nat → Rope → Rope
  deriving Repr

def Rope.length : Rope → Nat
  | Rope.leaf s        => s.length
  | Rope.node _ w r    => w + Rope.length r

def Rope.isLegal : Rope → Bool
  | Rope.leaf _        => true
  | Rope.node l w r    =>
    w == (Rope.length l) && Rope.isLegal l && Rope.isLegal r

def Rope.concat (r1 r2 : Rope) : Rope :=
  Rope.node r1 (Rope.length r1) r2

def Rope.toString : Rope → String
  | Rope.leaf s => s
  | Rope.node l _ r => Rope.toString l ++ Rope.toString r

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

def Rope.flatten: Rope → List String
  | Rope.leaf s => [s]
  | Rope.node l _ r => flatten l ++ flatten r

def buildBalanced : List String → Rope
  -- match ss with
  | [] => Rope.leaf ""
  | [s] => Rope.leaf s
  | ss =>
    let mid := ss.length / 2
    let (left, right) := ss.splitAt mid
    let leftRope := buildBalanced left
    let rightRope := buildBalanced right
    Rope.node leftRope (Rope.length leftRope) rightRope
decreasing_by
    sorry


def rebalance (r : Rope) : Rope :=
  buildBalanced (Rope.flatten r)


axiom string_append_assoc (a b c : String) :
  (a ++ b) ++ c = a ++ (b ++ c)

theorem Rope_concat_assoc (r1 r2 r3 : Rope) :
  Rope.toString (Rope.concat (Rope.concat r1 r2) r3) =
  Rope.toString (Rope.concat r1 (Rope.concat r2 r3)) :=
by
  simp [Rope.toString]
  apply string_append_assoc

theorem Rope_concat_length_comm (r1 r2 : Rope) :
  Rope.length (Rope.concat r1 r2) = Rope.length (Rope.concat r2 r1) :=
by
  simp [Rope.length]
  apply Nat.add_comm

theorem Rope_concat_legal_invariant:
  ∀r₁ r₂ : Rope, Rope.isLegal r₁ ∧ Rope.isLegal r₂
    → Rope.isLegal (Rope.concat r₁ r₂) :=
by
  intro r1 r2 h
  simp [Rope.isLegal]
  exact h


#check List.foldl_append

def stringJoin : List String → String
  | [] => ""
  | s :: ss => s ++ (stringJoin ss)



#check List.singleton_append


/-
The recursion direction is inconsistent with def,
so we need another lemma.
-/
theorem join_tail_append (l : List String) (x : String) :
  stringJoin (l ++ [x]) = stringJoin l ++ x :=
by
  induction l with
  | nil =>
    simp [stringJoin]
  | cons y ys ih =>
    simp [stringJoin, ih, List.append_assoc]
    simp [String.append_assoc]


theorem join_distribute (l r : List String):
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



theorem fold_empty (l : List String):
  List.foldl (fun r s => r ++ s) "" l = String.join  l :=
by
  rfl



theorem toString_eq_join_flatten (t : Rope) :
  Rope.toString t = stringJoin (Rope.flatten t) := by
  induction t with
  | leaf s =>
    simp [Rope.toString, Rope.flatten]
    simp [stringJoin]
  | node l r w ih_l ih_r =>
    simp [Rope.toString]
    simp [ih_l, ih_r]
    simp [Rope.flatten]
    simp [join_distribute]



-- theorem buildBalanced_inv1 (ss : List String) :
--   Rope.toString (buildBalanced ss) = String.join ss :=
-- by
--   induction ss with
--   | nil => rfl
--   | cons x xs ih =>
--     let mid := (x :: xs).length / 2
--     let (left, right) := (x :: xs).splitAt mid
--     let leftRope := buildBalanced left
--     let rightRope := buildBalanced right
--     have hmid : Rope.toString leftRope ++ Rope.toString rightRope = String.join (x :: xs) := by
--       sorry
--     rw [<-hmid]
--     rw [buildBalanced]
--     simp [toString]
--     sorry


-- theorem Rope_rebalance_invariant (t: Rope) :
--   Rope.toString t = Rope.toString (rebalance t) :=
-- by
--   simp [rebalance, Rope.flatten]
--   match t with
--   | Rope.leaf n => rfl
--   | Rope.node l w r =>
--     simp [Rope.flatten]
--     simp [Rope.toString]
--     rw [buildBalanced_inv1]
--     simp [toString_eq_join_flatten]
--     simp [String.join]
--     simp [fold_empty]
--     rw [fold_eq]


#print String.append
#check List.append_assoc
#check List.append_assoc


def r1 := Rope.leaf "123456"
def r2 := Rope.leaf "12345"
def r3 := Rope.leaf "123"
def r4 := Rope.leaf "12345"
def r5 := Rope.leaf "12"
def r6 := Rope.leaf "123"

def unbalancedRope :=
  Rope.node r1 6 (
    Rope.node r2 5 (
      Rope.node r3 3 (
        Rope.node r4 5 (
          Rope.node r5 2 r6
        )
      )
    )
  )


def rebalancedPretty := Rope.prettyPrintStr (rebalance unbalancedRope)

#eval IO.println "Unbalanced Rope Structure:"
#eval IO.println (Rope.prettyPrintStr unbalancedRope)

#eval IO.println "\nRebalanced Rope Structure:"
#eval IO.println rebalancedPretty

#eval Rope.length unbalancedRope
#eval Rope.length (rebalance unbalancedRope)

#eval Rope.isLegal unbalancedRope
