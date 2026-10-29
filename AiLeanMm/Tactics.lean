import Mathlib

variable (P Q R S T : Prop)

example (foo : P) (h : P → Q) : Q := h foo

theorem ex (foo : P) (h : P → Q) : Q := by
  exact h foo

#print axioms ex

example (foo : P) (h : P → Q) : Q := by
  apply h
  exact foo

example : P → Q → P := by
  intro hP hQ
  exact hP

example (hPQ : P → Q) (hQR : Q → R) (hP : P) :
  R := by sorry

example (h : P → Q → R) (hPQ : P → Q) (hP : P) :
  R := by
  apply h
  · sorry
  · sorry

example (h : P → Q → R) (hPQ : P → Q) (hP : P) :
  R := by
  have hQ: Q := sorry
  sorry

example (h : P → Q → R) (hPQ : P → Q) (hP : P) :
  R := by
  suffices hQ: Q by sorry
  sorry

example :
  (P → R) → (S → Q) → (R → T) → (Q → R) → S → T
  := by sorry

example (h : False) : 7 * 6 = 42 → 7 * 6 = 41
  := by
  exfalso
  sorry

example (h1 : P) (h2 : ¬ P) : False := by
  change P → False at h2
  sorry

example : P → ¬¬P := by
  intro h1
  change ((P → False) → False)
  sorry

theorem dne : ¬¬P → P := by
  intro h
  by_cases hP: P
  · sorry
  · sorry

#print axioms dne

theorem contrapos : (P → Q) → ¬Q → ¬P := by sorry

example : P ∧ (Q ∧ R) → P := by
  intro h
  obtain ⟨hP, hQ, hR⟩ := h
  sorry

example : P ∧ (Q ∧ R) → P := by
  intro ⟨hP, hQ, hR⟩
  sorry

example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor
  · sorry
  · sorry

example : P ∧ Q → Q ∧ P := by sorry

example : P → P ∨ Q := by
  intro hP
  left
  sorry

example : Q → P ∨ Q := by
  intro hQ
  right
  sorry

example (h1 : P ∨ Q) (h2 : P → R) (h3 : Q → R) :
  R := by
  cases h1 with
  | inl h4 =>
  · sorry
  | inr h5 =>
  · sorry

example (h1 : P ∨ Q) (h2 : P → R) (h3 : Q → R) :
  R := by
  obtain h4 | h5 := h1
  · sorry
  · sorry

example : P ∨ Q → (P → R) → (Q → R) → R := by
  rintro (hP | hQ)
  · sorry
  · sorry

theorem deMorgan'1 : ¬(P ∨ Q) → ¬P ∧ ¬Q := by sorry

theorem deMorgan'2 : ¬(P ∧ Q) → ¬P ∨ ¬Q := by sorry

theorem deMorgan'3 : ¬P ∧ ¬Q → ¬(P ∨ Q) := by sorry

theorem deMorgan'4 : ¬P ∨ ¬Q → ¬(P ∧ Q) := by sorry

------------------ Natural numbers! ------------------

example : ∀ n, n + 20 > 8 := by lia

example : ∀ n, n + 20 > 8 := by simp

example (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 4) :
  f 20 ≤ 4 := by
  apply hf

example (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 4) :
  f 20 < 7 := by
  specialize hf 20
  lia

example (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 4) :
  f 20 + f 30 < 9 := by sorry

example : ∃ x : ℕ, x^2 + x - 1 = 11 := by
  use 3
  rfl

example (n : ℕ) : ∃ m, m > n := by
  exact ⟨n + 1, by lia⟩

example (n : ℕ) (h : ∃ m, m < n) : n ≠ 0 :=
  by sorry

example (x y z : ℕ) :
  x = y + z → z > 5 → x - y > 5 := by
  intro hx hz
  rw [hx]
  rw [Nat.add_sub_cancel_left]
  exact hz

example (x y z : ℕ) :
  x = y + z → z > 5 → x - y > 5 := by
  intro hx hz
  rw [hx, Nat.add_sub_cancel_left]
  exact hz

#eval (5 : ℕ) - (10 : ℕ)

example (x y : ℕ) :
  x + y = 12 → y ≥ 2 → x + (y - 2) = 10 := by
  intro hx hy
  rw [← Nat.add_sub_assoc]
  · rw [hx]
  · exact hy

example :
  (P ↔ R) → (Q ↔ S) → P ∧ ¬ Q → R ∧ ¬ S := by
  intro hPR hQS h
  rw [hPR, hQS] at h
  exact h

example : ∀ n m, n + m = 0 → n = 0 := by sorry

example (f : ℤ → ℤ) (h : ∀ n, n < f n) :
  4 < f (f 3) := by sorry

example {α : Type} (P : α → Prop) :
  (∃ a, ¬ P a) → ¬ ∀ a, P a := by sorry

example : ∃ n : ℕ, n ^ 2 + n + 1 = 7 := by sorry

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
