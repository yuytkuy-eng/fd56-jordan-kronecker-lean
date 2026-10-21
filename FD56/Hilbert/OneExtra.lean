/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.OneExtraLow
import FD56.Hilbert.KernelGrowth
import FD56.Hilbert.GenericTall

/-! The full generic SL Hilbert profile when m = n + 1 consists of
n + 1 copies of n - 1. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

theorem generic_one_extra_gl_kernel_hilbert (n d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters (Fin n) (Fin (n + 1))))
      (polynomialKernelAtDegree (glEquationMatrix
        (genericAffineSquare K (Fin n) (Fin (n + 1)))
        (genericAffineRows K (Fin n) (Fin (n + 1)))) d) = n * (d + 1 - n) := by
  let M := genericAffineSquare K (Fin n) (Fin (n + 1))
  let P := genericAffineRows K (Fin n) (Fin (n + 1))
  have hd : Module.finrank (AffineCoefficientField K (MatrixParameters (Fin n) (Fin (n + 1))))
      (LinearMap.ker (Matrix.toLin' ((glEquationMatrix M P).map (Polynomial.evalRingHom 0)))) ≤ n := by
    have hh := generic_affine_zero_gl_nullity (K := K) (n := Fin n) (m := Fin (n + 1)) (by simp)
    simpa [M, P] using le_of_eq hh
  have hz : ∀ k, k < n → Module.finrank
      (AffineCoefficientField K (MatrixParameters (Fin n) (Fin (n + 1))))
        (polynomialKernelAtDegree (glEquationMatrix M P) k) = 0 := by
    intro k hk
    exact generic_one_extra_gl_kernel_low n k hk
  have hu := polynomial_kernel_shift_bound (glEquationMatrix M P) n n hd hz d
  apply le_antisymm hu
  by_cases he : d + 1 < n
  · have hs : d + 1 - n = 0 := by omega
    simp [hs]
  · have hb := gl_kernel_dimension_lower M P (genericAffineRows_degree K _ _) d
    simp only [Fintype.card_fin] at hb
    have hs := Nat.sub_add_cancel (by omega : n ≤ d + 1)
    have hs' := congrArg (fun a : ℕ => n * a) hs
    nlinarith

theorem generic_one_extra_slHilbert (n : ℕ) (hn : 0 < n) (d : ℕ) :
    slHilbert (genericAffineSquare K (Fin n) (Fin (n + 1)))
      (genericAffineRows K (Fin n) (Fin (n + 1))) d =
        (n + 1) * (d + 1 - (n - 1)) := by
  let i₀ : Fin n := ⟨0, hn⟩
  let M := genericAffineSquare K (Fin n) (Fin (n + 1))
  let P := genericAffineRows K (Fin n) (Fin (n + 1))
  have hd : Module.finrank (AffineCoefficientField K (MatrixParameters (Fin n) (Fin (n + 1))))
      (LinearMap.ker (Matrix.toLin' ((slEquationMatrix M P i₀).map (Polynomial.evalRingHom 0)))) ≤ n + 1 := by
    have hh := generic_affine_zero_sl_nullity (K := K) (m := Fin (n + 1)) i₀ (by simp)
    simpa [M, P] using le_of_eq hh
  have hz : ∀ k, k < n - 1 → Module.finrank
      (AffineCoefficientField K (MatrixParameters (Fin n) (Fin (n + 1))))
        (polynomialKernelAtDegree (slEquationMatrix M P i₀) k) = 0 := by
    intro k hk
    rw [← slHilbert_eq_matrix_kernel M P i₀]
    exact generic_one_extra_slHilbert_low n k hn (by omega)
  have hu := polynomial_kernel_shift_bound (slEquationMatrix M P i₀) (n - 1) (n + 1) hd hz d
  rw [← slHilbert_eq_matrix_kernel M P i₀] at hu
  apply le_antisymm hu
  by_cases he : d + 1 < n - 1
  · have hs : d + 1 - (n - 1) = 0 := by omega
    simp [hs]
  · have hb := slHilbert_dimension_lower M P (genericAffineRows_degree K _ _) i₀ d
    simp only [Fintype.card_fin] at hb
    have hs := Nat.sub_add_cancel (by omega : n - 1 ≤ d + 1)
    have hs' := congrArg (fun a : ℕ => (n + 1) * a) hs
    have hn' : (n - 1) + 1 = n := by omega
    have hn'' := congrArg (fun a : ℕ => (n + 1) * a) hn'
    nlinarith

theorem generic_one_extra_slHilbert_profile (n : ℕ) (hn : 0 < n) :
    HasHilbertProfile (genericAffineSquare K (Fin n) (Fin (n + 1)))
      (genericAffineRows K (Fin n) (Fin (n + 1))) (fun _ : Fin (n + 1) => n - 1) := by
  intro d
  rw [generic_one_extra_slHilbert n hn d]
  simp [profile]

end FD56
