/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedRectangular

/-! Degree-controlled polynomial preimages for rectangular block pencils. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K ι κ : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem bidiagonal_coefficient_surjective_of_length_le (m d : ℕ) (hm : m ≤ d + 1) :
    Function.Surjective (polynomialCoefficientMatrix (bidiagonalPencil (K := K) m) d).mulVec := by
  apply coefficient_surjective_of_kernel_finrank _ d (bidiagonalPencil_degree m)
  rw [bidiagonal_kernel_hilbert]
  simp only [Fintype.card_fin]
  have h := Nat.sub_add_cancel hm
  nlinarith

theorem rectangularBlockPencil_polynomial_preimage (e : ι → ℕ) (d : ℕ)
    (he : ∀ i, e i ≤ d + 1) (g : (Σ i, Fin (e i)) → K[X])
    (hg : ∀ x, (g x).natDegree ≤ d + 1) :
    ∃ v : (Σ i, Fin (e i + 1)) → K[X],
      (∀ x, (v x).natDegree ≤ d) ∧ rectangularBlockPencil e *ᵥ v = g := by
  have hlocal (i : ι) : ∃ v : Fin (e i + 1) → K[X],
      (∀ x, (v x).natDegree ≤ d) ∧
      bidiagonalPencil (e i) *ᵥ v = fun x => g ⟨i, x⟩ := by
    exact polynomial_preimage_of_coefficient_surjective _ d (bidiagonalPencil_degree (e i))
      (bidiagonal_coefficient_surjective_of_length_le (e i) d (he i)) _ (fun x => hg ⟨i, x⟩)
  choose v hv hmul using hlocal
  refine ⟨fun x => v x.1 x.2, fun x => hv x.1 x.2, ?_⟩
  funext ⟨i, x⟩
  rw [rectangularBlockPencil, blockDiagonal_mulVec]
  exact congrFun (hmul i) x

theorem rectangularBlockPencil_matrix_preimage (e : ι → ℕ) (d : κ → ℕ)
    (he : ∀ i j, e i ≤ d j + 1) (G : Matrix (Σ i, Fin (e i)) κ K[X])
    (hG : ∀ x j, (G x j).natDegree ≤ d j + 1) :
    ∃ W : Matrix (Σ i, Fin (e i + 1)) κ K[X],
      (∀ x j, (W x j).natDegree ≤ d j) ∧ rectangularBlockPencil e * W = G := by
  have hcol (j : κ) : ∃ v : (Σ i, Fin (e i + 1)) → K[X],
      (∀ x, (v x).natDegree ≤ d j) ∧
      rectangularBlockPencil e *ᵥ v = fun x => G x j :=
    rectangularBlockPencil_polynomial_preimage e (d j) (fun i => he i j) _ (fun x => hG x j)
  choose v hv hmul using hcol
  refine ⟨fun x j => v j x, fun x j => hv j x, ?_⟩
  apply Matrix.ext
  intro x j
  exact congrFun (hmul j) x

theorem rectangularBlockPencil_balanced_lift (e : ι → ℕ)
    (he : ∀ i j, e i ≤ e j + 1) (G : Matrix (Σ i, Fin (e i)) ι K[X])
    (hG : ∀ x j, (G x j).natDegree ≤ e j + 2) :
    ∃ W : Matrix (Σ i, Fin (e i + 1)) ι K[X],
      (∀ x j, (W x j).natDegree ≤ e j + 1) ∧ rectangularBlockPencil e * W = G := by
  apply rectangularBlockPencil_matrix_preimage e (fun j => e j + 1)
  · intro i j
    have h := he i j
    omega
  · simpa only [Nat.add_assoc] using hG

theorem rectangularBlockLengths_adjacent (n s : ℕ) :
    ∀ i j, rectangularBlockLengths n s i ≤ rectangularBlockLengths n s j + 1 := by
  intro i j
  cases i <;> cases j <;> (dsimp [rectangularBlockLengths]; omega)

theorem balanced_rectangular_block_lift (n s : ℕ)
    (G : Matrix (RectangularRows n s) (Fin (n % s) ⊕ Fin (s - n % s)) K[X])
    (hG : ∀ x j, (G x j).natDegree ≤ rectangularBlockLengths n s j + 2) :
    ∃ W : Matrix (RectangularColumns n s) (Fin (n % s) ⊕ Fin (s - n % s)) K[X],
      (∀ x j, (W x j).natDegree ≤ rectangularBlockLengths n s j + 1) ∧
      rectangularBlockPencil (rectangularBlockLengths n s) * W = G :=
  rectangularBlockPencil_balanced_lift _ (rectangularBlockLengths_adjacent n s) G hG

end FD56
