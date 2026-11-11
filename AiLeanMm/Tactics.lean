import Mathlib

variable (P Q R S T : Prop)

example (foo : P) (h : P → Q) : Q := h foo

theorem ex (foo : P) (h : P → Q) : Q := by
  exact h foo

#print axioms ex

axiom twoPlusTwoIsFour : 2 + 2 = 4

example (foo : P) (h : P → Q) : Q := by
  apply h
  exact foo

example : P → (Q → P) := by
  intro hP hQ
  exact hP

example (hPQ : P → Q) (hQR : Q → R) (hP : P) :
  R := by
  apply hQR
  apply hPQ
  exact hP

example (h : P → (Q → R))
  (hPQ : P → Q) (hP : P) :
  R := by
  apply h
  · exact hP -- \cdot
  · apply hPQ
    exact hP

example (h : P → Q → R) (hPQ : P → Q) (hP : P) :
  R := by
  have hQ: Q := by exact hPQ hP
  apply h <;> assumption

example (h : P → Q → R) (hPQ : P → Q) (hP : P) :
  R := by
  suffices hQ: Q by sorry
  sorry

example :
  (P → R) → (S → Q) → (R → T) → (Q → R) → S → T
  := by sorry

example (h : False) :
  7 * 6 = 42 → 7 * 6 = 41
  := by exfalso; assumption

example (h1 : P) (h2 : ¬ P) :
  False := by
  change P → False at h2
  apply h2; assumption

example : P → ¬¬P := by
  intro hP
  change ((P → False) → False)
  intro hNP
  apply hNP; assumption

theorem dne : ¬¬P → P := by
  intro h
  by_cases hP: P
  · assumption
  · exfalso; grind

#print axioms dne

theorem contrapos :
  (P → Q) → ¬Q → ¬P :=
  by sorry

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
  use 3; rfl

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
