/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialMatrix
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! Descent of kernel coordinates through an injective ring homomorphism.
For polynomial matrices, the target may be the fraction field. The existence
of a polynomial left inverse and spanning over that field remain hypotheses. -/

namespace FD56
open Matrix
variable {R S a b k : Type*} [CommRing R] [CommRing S]
  [Fintype b] [Fintype k] [DecidableEq k]

open scoped BigOperators

/-- A Bezout identity between square compressions gives an explicit left inverse. -/
theorem left_inverse_of_bezout {ι : Type*} [Fintype ι]
    (Z : Matrix b k R) (E : ι → Matrix k b R) (w : ι → R)
    (hw : ∑ i, w i * Matrix.det (E i * Z) = 1) :
    ∃ L : Matrix k b R, L * Z = 1 := by
  refine ⟨∑ i, w i • (Matrix.adjugate (E i * Z) * E i), ?_⟩
  rw [Matrix.sum_mul]
  simp_rw [Matrix.smul_mul, Matrix.mul_assoc, Matrix.adjugate_mul, smul_smul]
  rw [← Finset.sum_smul, hw, one_smul]

theorem kernel_coordinates_descend (φ : R →+* S) (hφ : Function.Injective φ)
    (Z : Matrix b k R) (L : Matrix k b R) (hL : L * Z = 1)
    (Y : Matrix b Unit R) (c : Matrix k Unit S)
    (hc : Y.map φ = Z.map φ * c) : Y = Z * (L * Y) := by
  have hcoeff : (L * Y).map φ = c := by
    rw [Matrix.map_mul, hc, ← Matrix.mul_assoc,
      ← Matrix.map_mul, hL]
    simp
  have heq : Y.map φ = (Z * (L * Y)).map φ := by
    rw [Matrix.map_mul, hcoeff]
    exact hc
  ext i j
  exact hφ (congrArg (fun A => A i j) heq)

theorem kernel_basis_of_left_inverse_and_spanning
    (φ : R →+* S) (hφ : Function.Injective φ)
    (A : Matrix a b R) (Z : Matrix b k R) (L : Matrix k b R)
    (hL : L * Z = 1) (hAZ : A * Z = 0)
    (hspan : ∀ Y : Matrix b Unit R, A * Y = 0 →
      ∃ c : Matrix k Unit S, Y.map φ = Z.map φ * c) :
    ∀ Y : Matrix b Unit R, A * Y = 0 ↔ ∃! c : Matrix k Unit R, Y = Z * c := by
  intro Y
  constructor
  · intro hY
    obtain ⟨c, hc⟩ := hspan Y hY
    refine ⟨L * Y, kernel_coordinates_descend φ hφ Z L hL Y c hc, ?_⟩
    intro d hd
    rw [hd, ← Matrix.mul_assoc, hL, Matrix.one_mul]
  · rintro ⟨c, hc, _⟩
    rw [hc, ← Matrix.mul_assoc, hAZ, Matrix.zero_mul]

end FD56
