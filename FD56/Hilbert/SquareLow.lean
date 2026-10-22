/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericSLWitness
import FD56.Stabilizer.BidiagonalSL
import FD56.Hilbert.KernelGrowth
import FD56.Hilbert.GenericTall

/-! A triangular specialization proves generic SL vanishing below degree n - 1
when the translation matrix is square. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

def squareBidiagonalPencil (n : ℕ) : Matrix (Fin n) (Fin n) K[X] :=
  fun i j => bidiagonalPencil n j i.castSucc

theorem squareBidiagonalPencil_degree (n : ℕ) :
    DegreeBound (squareBidiagonalPencil (K := K) n) 1 :=
  fun i j => bidiagonalPencil_degree n j i.castSucc

theorem squareBidiagonalPencil_det (n : ℕ) :
    (squareBidiagonalPencil (K := K) n).det = Polynomial.X ^ n := by
  have htri : (squareBidiagonalPencil (K := K) n).BlockTriangular OrderDual.toDual := by
    intro i j hij
    change i < j at hij
    have h₁ : i.castSucc ≠ j.castSucc := by
      intro h
      have hh := congrArg Fin.val h
      change i.val = j.val at hh
      have hlt : i.val < j.val := hij
      omega
    have h₂ : i.castSucc ≠ j.succ := by
      intro h
      have hh := congrArg Fin.val h
      change i.val = j.val + 1 at hh
      have hlt : i.val < j.val := hij
      omega
    simp [squareBidiagonalPencil, bidiagonalPencil, h₁, h₂]
  rw [Matrix.det_of_lowerTriangular _ htri]
  have hdiag (i : Fin n) : squareBidiagonalPencil (K := K) n i i = Polynomial.X := by
    have h : i.castSucc ≠ i.succ := by
      intro hh
      have hv := congrArg Fin.val hh
      change i.val = i.val + 1 at hv
      omega
    simp [squareBidiagonalPencil, bidiagonalPencil, h]
  simp [hdiag]

theorem squareBidiagonalPencil_injective (n : ℕ) :
    Function.Injective (squareBidiagonalPencil (K := K) n).mulVec := by
  intro v w h
  apply sub_eq_zero.mp
  apply Matrix.eq_zero_of_mulVec_eq_zero (M := squareBidiagonalPencil n)
    (by rw [squareBidiagonalPencil_det]; exact pow_ne_zero _ Polynomial.X_ne_zero)
  rw [Matrix.mulVec_sub, h, sub_self]

theorem square_bidiagonal_scalar_low_degree_zero (n d : ℕ) (hd : d + 1 < n)
    (U : Matrix (Fin n) (Fin n) K[X]) (c : K[X])
    (hU : U * squareBidiagonalPencil n = c • (1 : Matrix (Fin n) (Fin n) K[X]))
    (hdeg : DegreeBound U d) : U = 0 ∧ c = 0 := by
  let V : Matrix (Fin n) (Fin (n + 1)) K[X] := fun i => Fin.lastCases 0 (U i)
  have hV : V * (bidiagonalPencil n).transpose =
      c • (1 : Matrix (Fin n) (Fin n) K[X]) := by
    have he : V * (bidiagonalPencil n).transpose = U * squareBidiagonalPencil n := by
      funext i j
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      rw [Fin.sum_univ_castSucc]
      simp [V, squareBidiagonalPencil]
    rw [he, hU]
  have hdegV : DegreeBound V d := by
    intro i j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [V]
    · simpa [V] using hdeg i k
  obtain ⟨hzero, hc⟩ := bidiagonal_scalar_low_degree_zero n d hd V c hV hdegV
  refine ⟨?_, hc⟩
  funext i j
  have hh := congrArg (fun A : Matrix (Fin n) (Fin (n + 1)) K[X] => A i j.castSucc) hzero
  simpa [V] using hh

theorem generic_square_sl_coefficient_injective (n d : ℕ)
    (hn : 0 < n) (hd : d + 1 < n) :
    Function.Injective (polynomialCoefficientMatrix
      (slEquationMatrix (genericAffineSquare K (Fin n) (Fin n))
        (genericAffineRows K (Fin n) (Fin n)) ⟨0, hn⟩) d).mulVec := by
  apply generic_sl_coefficient_injective_of_witness (squareBidiagonalPencil n)
    (squareBidiagonalPencil_degree n) (squareBidiagonalPencil_injective n) ⟨0, hn⟩ d
  intro U c hU hdeg
  exact (square_bidiagonal_scalar_low_degree_zero n d hd U c hU hdeg).1

theorem generic_square_slHilbert_low (n d : ℕ) (hn : 0 < n) (hd : d + 1 < n) :
    slHilbert (genericAffineSquare K (Fin n) (Fin n))
      (genericAffineRows K (Fin n) (Fin n)) d = 0 := by
  apply generic_slHilbert_zero_of_witness (squareBidiagonalPencil n)
    (squareBidiagonalPencil_degree n) (squareBidiagonalPencil_injective n) ⟨0, hn⟩ d
  intro U c hU hdeg
  exact (square_bidiagonal_scalar_low_degree_zero n d hd U c hU hdeg).1

theorem generic_square_slHilbert_upper (n : ℕ) (hn : 0 < n) (d : ℕ) :
    slHilbert (genericAffineSquare K (Fin n) (Fin n))
      (genericAffineRows K (Fin n) (Fin n)) d ≤ d + 1 - (n - 1) := by
  let i₀ : Fin n := ⟨0, hn⟩
  let M := genericAffineSquare K (Fin n) (Fin n)
  let P := genericAffineRows K (Fin n) (Fin n)
  have hd : Module.finrank (AffineCoefficientField K (MatrixParameters (Fin n) (Fin n)))
      (LinearMap.ker (Matrix.toLin' ((slEquationMatrix M P i₀).map
        (Polynomial.evalRingHom 0)))) ≤ 1 := by
    have hh := generic_affine_zero_sl_nullity (K := K) (m := Fin n) i₀ (by simp)
    simpa [M, P] using le_of_eq hh
  have hz : ∀ k, k < n - 1 → Module.finrank
      (AffineCoefficientField K (MatrixParameters (Fin n) (Fin n)))
        (polynomialKernelAtDegree (slEquationMatrix M P i₀) k) = 0 := by
    intro k hk
    rw [← slHilbert_eq_matrix_kernel M P i₀]
    exact generic_square_slHilbert_low n k hn (by omega)
  have hu := polynomial_kernel_shift_bound (slEquationMatrix M P i₀) (n - 1) 1 hd hz d
  rw [← slHilbert_eq_matrix_kernel M P i₀] at hu
  simpa only [one_mul] using hu

theorem generic_square_rows_det_ne_zero (n : ℕ) :
    (genericAffineRows K (Fin n) (Fin n)).det ≠ 0 := by
  let P := genericAffineRows K (Fin n) (Fin n)
  have hi := generic_affine_rows_zero_injective K (Fin n) (Fin n) (by simp)
  have hunit : IsUnit (P.map (Polynomial.evalRingHom 0)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hi)
  intro hz
  apply hunit.ne_zero
  calc
    (P.map (Polynomial.evalRingHom 0)).det = (Polynomial.evalRingHom 0) P.det :=
      ((Polynomial.evalRingHom 0).map_det P).symm
    _ = 0 := by
      change (Polynomial.evalRingHom 0) (genericAffineRows K (Fin n) (Fin n)).det = 0
      rw [hz, map_zero]

end FD56
