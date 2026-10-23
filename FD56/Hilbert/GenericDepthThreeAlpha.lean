/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeAlphaWitness
import FD56.Hilbert.GenericDepthTwoAlpha

/-! Balanced minimal degrees of the third generic observability stack. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m : Type*} [Field K]
  [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem generic_depth_three_alpha_hilbert
    (hmn : 3*Fintype.card m < Fintype.card n) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) 3) d) =
      (Fintype.card n-3*Fintype.card m)*(d+1)-6*Fintype.card m := by
  apply le_antisymm
  · obtain ⟨M,P,hM,hP,hH⟩ := exists_depth_three_alpha_full_witness (K := K) hmn
    let σ₀ : K →+* DepthThreeStackField K n m :=
      (algebraMap (MvPolynomial (PrescribedMatrixParameters n
        (depthThreeRowDegree (m := m))) K) _).comp MvPolynomial.C
    let σ : K →+* DepthThreeAlphaField K n m :=
      (algebraMap (DepthThreeStackField K n m)[X] _).comp (C.comp σ₀)
    exact (generic_observability_kernel_le_field_witness σ M P hM hP 3 d).trans (hH d)
  · have hh := prescribed_matrix_kernel_lower
      (observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) 3)
      (fun ij => ij.1.val+1)
      (fun i j => (observability_polynomial_degree_top _ _ 3
        (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) i j).1)
      (by simpa only [Fintype.card_prod,Fintype.card_fin] using hmn.le) d
    have hsum : ∑ ij : Fin 3 × m, (ij.1.val+1)=6*Fintype.card m := by
      simp [Fintype.sum_prod_type,Fin.sum_univ_succ]
      omega
    simpa only [Fintype.card_prod,Fintype.card_fin,hsum] using hh

theorem generic_depth_three_alpha_minimal_degrees
    (hmn : 3*Fintype.card m < Fintype.card n) :
    HasMinimalKernelDegrees (observabilityMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) 3)
      (balancedDegreeList (6*Fintype.card m) (Fintype.card n-3*Fintype.card m)) := by
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [generic_depth_three_alpha_hilbert hmn d,
    balancedDegreeList_hilbert _ _ d (by omega)]

end FD56
