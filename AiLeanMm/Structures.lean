import Mathlib

open scoped Nat

#eval 5 !

example (n : ℕ) : n ! ≤ n ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [
      Nat.factorial_succ,
      Nat.pow_succ,
      Nat.mul_comm
    ]
    grw [ih]; gcongr; simp

theorem factorial_le_pow (n : ℕ) : n ! ≤ n ^ n := by
  cases n with
  | zero => simp
  | succ m =>
    rw [
      Nat.factorial_succ,
      Nat.pow_succ,
      Nat.mul_comm
    ]
    grw [factorial_le_pow m]; gcongr; simp

------------------ Структуры --------------------

structure Point : Type where
  x : ℤ
  y : ℤ

#check Point
#check Point.x

def pt₁ : Point := { x := 1, y := 2 }
def pt₂ : Point := ⟨-3, 4⟩

#eval Point.x pt₁

def Point.add (p₁ p₂ : Point) : Point :=
  {
    x := p₁.x + p₂.x
    y := p₁.y + p₂.y
  }

def Point.rotate (p : Point) : Point :=
  { x := p.y, y := -p.x }

def Point.add' (p₁ p₂ : Point) : Point :=
  ⟨p₁.x + p₂.x, p₁.y + p₂.y⟩

def Point.add'' (p₁ p₂ : Point) : Point :=
  match p₁, p₂ with
  | ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ => ⟨x₁ + x₂, y₁ + y₂⟩

def Point.add''' : Point → Point → Point :=
  fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ => ⟨x₁ + x₂, y₁ + y₂⟩

#eval Point.add pt₁ pt₂

#eval Point.x pt₁
#eval pt₁.x
#eval pt₁.add pt₂
#eval pt₁.rotate
#eval pt₁.rotate.add pt₂

namespace Hidden

structure Fin (n : ℕ) : Type where
  val : ℕ
  small : val < n

def two : Fin 5 := {
  val := 2
  small := by norm_num
}

def castUp {n m : ℕ} (x : Fin n) (h : n ≤ m) :
  Fin m := {
    val := x.val
    small := by
      have := x.small
      lia
  }

#check castUp two (show 5 ≤ 11 by norm_num)

end Hidden

----------------- Классы типов ------------------

example (x y : ℤ) :
  (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  apply add_sq

example (x y : ℚ) :
  (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  apply add_sq

example (x y : ℂ) :
  (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  exact add_sq x y

#check add_sq

example {K : Type*}
  [LT K] [Add K] [Div K] [OfNat K 2]
  (x y : K) (h : x < y) :
    x < (x + y) / 2 := by sorry

namespace GroupExample

class Group (G : Type*)
extends Add G, Zero G, Neg G where
  add_assoc : ∀ a b c : G, a + b + c = a + (b + c)
  zero_add : ∀ a : G, 0 + a = a
  add_zero : ∀ a : G, a + 0 = a
  neg_add_cancel : ∀ a : G, -a + a = 0

instance : Group ℤ where
  add_assoc := Int.add_assoc
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  neg_add_cancel := Int.add_left_neg

theorem zero_unique {G : Type*} [Group G] :
  ∀ e : G, (∀ a, e + a = a) → e = 0 := by
  intro e h
  have := h 0
  rw [Group.add_zero] at this
  exact this

class CommGroup (G : Type*) extends Group G where
  add_comm : ∀ a b : G, a + b = b + a

instance : CommGroup ℤ where
  add_comm := Int.add_comm

instance {X Y : Type*} [Group X] [Group Y] :
  Group (X × Y) where
  add_assoc a b c := by
    ext
    · exact Group.add_assoc a.1 b.1 c.1
    · exact Group.add_assoc a.2 b.2 c.2
  zero_add a := by
    ext
    · exact Group.zero_add a.1
    · exact Group.zero_add a.2
  add_zero a := by
    ext
    · exact Group.add_zero a.1
    · exact Group.add_zero a.2
  neg_add_cancel a := by
    ext
    · exact Group.neg_add_cancel a.1
    · exact Group.neg_add_cancel a.2

instance {X Y : Type*} [Group X] :
  Group (Y → X) where
  add_assoc a b c := by
    ext y
    exact Group.add_assoc (a y) (b y) (c y)
  zero_add a := by
    ext y
    exact Group.zero_add (a y)
  add_zero a := by
    ext y
    exact Group.add_zero (a y)
  neg_add_cancel a := by
    ext y
    exact Group.neg_add_cancel (a y)

#synth Group ℤ
#synth Group (ℤ × ℤ)
#synth Group (ℕ → ℤ)
#synth Group (ℕ → ℤ × (ℝ → ℤ)) -- A → B

example (e : ℤ) (h : ∀ a, e + a = a) :
  e = 0 := zero_unique e h
example (e : ℤ × ℤ) (h : ∀ a, e + a = a) :
  e = 0 := zero_unique e h
example (e : ℕ → ℤ) (h : ∀ a, e + a = a) :
  e = 0 := zero_unique e h
example {Y : Type*} (e : Y → ℤ) :
  (∀ a, e + a = a) → e = 0 := zero_unique e

end GroupExample
