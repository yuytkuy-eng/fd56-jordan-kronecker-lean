import FD56.SpectrumArithmetic

/-! The two-case numerical deduction from the claimed geometric Hilbert maximum.
The geometric maximum itself is not an assumption hidden in these lemmas. -/

namespace FD56

def threeHilbert (E c₀ c₁ c₂ d : ℤ) : ℤ :=
  c₀ * max 0 (d + 1 - E) + c₁ * max 0 (d - E) + c₂ * max 0 (d - E - 1)

def slLinear (E c₀ c₁ c₂ d : ℤ) : ℤ :=
  (c₀ + c₁ + c₂ + 1) * (d + 1) - (E * c₀ + (E + 1) * c₁ + (E + 2) * c₂) + 1

theorem threeHilbert_below (E c₀ c₁ c₂ d : ℤ) (h : d < E) :
    threeHilbert E c₀ c₁ c₂ d = 0 := by
  simp only [threeHilbert, max_eq_left (show d + 1 - E ≤ 0 by omega),
    max_eq_left (show d - E ≤ 0 by omega),
    max_eq_left (show d - E - 1 ≤ 0 by omega), mul_zero, add_zero]

theorem threeHilbert_at (E c₀ c₁ c₂ : ℤ) : threeHilbert E c₀ c₁ c₂ E = c₀ := by
  simp [threeHilbert]

theorem threeHilbert_above (E c₀ c₁ c₂ d : ℤ) (h : E + 1 ≤ d) :
    threeHilbert E c₀ c₁ c₂ d =
      c₀ * (d + 1 - E) + c₁ * (d - E) + c₂ * (d - E - 1) := by
  simp only [threeHilbert, max_eq_right (show 0 ≤ d + 1 - E by omega),
    max_eq_right (show 0 ≤ d - E by omega),
    max_eq_right (show 0 ≤ d - E - 1 by omega)]

theorem slLinear_at (E c₀ c₁ c₂ : ℤ) : slLinear E c₀ c₁ c₂ E = c₀ + E + 2 - c₂ := by
  unfold slLinear
  ring

theorem slLinear_above (E c₀ c₁ c₂ d : ℤ) (h : E + 1 ≤ d) :
    slLinear E c₀ c₁ c₂ d = threeHilbert E c₀ c₁ c₂ d + d + 2 := by
  rw [threeHilbert_above E c₀ c₁ c₂ d h]
  unfold slLinear
  ring

theorem threeHilbert_nonneg (E c₀ c₁ c₂ d : ℤ)
    (h₀ : 0 ≤ c₀) (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂) :
    0 ≤ threeHilbert E c₀ c₁ c₂ d := by
  unfold threeHilbert
  positivity

/-- The balanced branch of the Hilbert maximum, before Euclidean division. -/
theorem hilbert_balanced_branch (E c₀ c₁ c₂ d : ℤ)
    (h₀ : 0 ≤ c₀) (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂) (hd : 0 ≤ d)
    (hthreshold : c₂ ≤ E + 2) :
    max (threeHilbert E c₀ c₁ c₂ d) (slLinear E c₀ c₁ c₂ d) =
      max 0 (slLinear E c₀ c₁ c₂ d) := by
  by_cases hbelow : d < E
  · rw [threeHilbert_below E c₀ c₁ c₂ d hbelow]
  by_cases heq : d = E
  · subst d
    rw [threeHilbert_at, slLinear_at]
    rw [max_eq_right (by omega : c₀ ≤ c₀ + E + 2 - c₂),
      max_eq_right (by omega : 0 ≤ c₀ + E + 2 - c₂)]
  have habove : E + 1 ≤ d := by omega
  have hnonneg := threeHilbert_nonneg E c₀ c₁ c₂ d h₀ h₁ h₂
  have hlinear := slLinear_above E c₀ c₁ c₂ d habove
  rw [max_eq_right (by omega : threeHilbert E c₀ c₁ c₂ d ≤ slLinear E c₀ c₁ c₂ d),
    max_eq_right (by omega : 0 ≤ slLinear E c₀ c₁ c₂ d)]

/-- The nonbalanced branch, with exactly the multiplicity shift in the paper. -/
theorem hilbert_unbalanced_branch (E c₀ c₁ c₂ d : ℤ)
    (h₀ : 0 ≤ c₀) (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂)
    (hd : 0 ≤ d) (hthreshold : E + 2 < c₂) :
    max (threeHilbert E c₀ c₁ c₂ d) (slLinear E c₀ c₁ c₂ d) =
      threeHilbert E c₀ (c₁ + E + 3) (c₂ - E - 2) d := by
  by_cases hbelow : d < E
  · rw [threeHilbert_below E c₀ c₁ c₂ d hbelow,
      threeHilbert_below E c₀ (c₁ + E + 3) (c₂ - E - 2) d hbelow]
    apply max_eq_left
    unfold slLinear
    have hm := mul_nonneg (show 0 ≤ c₀ + c₁ + c₂ + 1 by omega)
      (show 0 ≤ E - 1 - d by omega)
    nlinarith
  by_cases heq : d = E
  · subst d
    rw [threeHilbert_at, threeHilbert_at, slLinear_at]
    apply max_eq_left
    omega
  have habove : E + 1 ≤ d := by omega
  have hlinear := slLinear_above E c₀ c₁ c₂ d habove
  rw [max_eq_right (by omega : threeHilbert E c₀ c₁ c₂ d ≤ slLinear E c₀ c₁ c₂ d)]
  rw [threeHilbert_above E c₀ (c₁ + E + 3) (c₂ - E - 2) d habove]
  unfold slLinear
  ring

/-- A balanced list's Hilbert function is the positive part of its Euler characteristic. -/
theorem balanced_hilbert (r a w d : ℤ) (hr : 0 < r) (hw : 0 ≤ w) (hwr : w < r) :
    (r - w) * max 0 (d - a + 1) + w * max 0 (d - a) =
      max 0 (r * (d + 1) - (r * a + w)) := by
  by_cases h : d < a
  · rw [max_eq_left (by omega : d - a + 1 ≤ 0), max_eq_left (by omega : d - a ≤ 0)]
    simp only [mul_zero, add_zero]
    symm
    apply max_eq_left
    nlinarith [mul_nonneg (le_of_lt hr) (show 0 ≤ a - d - 1 by omega)]
  · rw [max_eq_right (by omega : 0 ≤ d - a + 1), max_eq_right (by omega : 0 ≤ d - a)]
    have hnonneg : 0 ≤ r * (d + 1) - (r * a + w) := by
      nlinarith [mul_nonneg (le_of_lt hr) (show 0 ≤ d - a by omega)]
    rw [max_eq_right hnonneg]
    ring

end FD56
