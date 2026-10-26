/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedGLKronecker
import FD56.Stabilizer.SLKirillovPencil
import FD56.Hilbert.GenericMinimal
import FD56.Hilbert.LowDepthGLDimension

/-! Actual constant-congruence Kronecker decompositions for full SL radicals. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem slKirillovMatrix_kronecker (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (i₀ : n) (xs : List ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hmin : HasMinimalKernelDegrees (slEquationMatrix M P i₀) xs)
    (hcard : Fintype.card (SLChartInput n m i₀) = (xs.map (fun e => 2*e+1)).sum) :
    HasKroneckerDecomposition (slKirillovMatrix M P i₀) xs := by
  let A := fun i j => (slKirillovMatrix M P i₀ i j).coeff 0
  let B := fun i j => (slKirillovMatrix M P i₀ i j).coeff 1
  have he : affineMatrixPencil A B = slKirillovMatrix M P i₀ :=
    affineMatrixPencil_coefficients _ (slKirillovMatrix_degreeBound M P i₀ 1 hM hP)
  have hm : HasMinimalKernelDegrees (affineMatrixPencil A B) xs := by
    rw [he]
    exact (slKirillovMatrix_hasMinimalKernelDegrees_iff M P i₀ xs).mpr hmin
  obtain ⟨r, d, hp, T, S, hTS, hST, hc⟩ := exists_mixed_kronecker_canonical A B xs hm hcard
    (slKirillovMatrix_coefficient_skew M P i₀ 0)
    (slKirillovMatrix_coefficient_skew M P i₀ 1)
    (slKirillovMatrix_coefficient_alternating M P i₀ 0)
    (slKirillovMatrix_coefficient_alternating M P i₀ 1)
  exact ⟨r, d, hp, T, S, hTS, hST, he ▸ hc⟩

omit [Field K] in
theorem above_sl_dimension_budget (i₀ : n) (hnm : Fintype.card n < Fintype.card m) :
    Fintype.card (SLChartInput n m i₀) =
      ((balancedDegreeList (Fintype.card n*Fintype.card n-1)
        (Fintype.card n*(Fintype.card m-Fintype.card n)+1)).map (fun e => 2*e+1)).sum := by
  rw [slChartInput_card, nat_list_affine_sum,
    balancedDegreeList_sum _ _ (by omega), balancedDegreeList_length _ _ (by omega)]
  simp only [SLInput, Fintype.card_sum, Fintype.card_prod, one_mul]
  have hn : 0 < Fintype.card n := Fintype.card_pos_iff.mpr ⟨i₀⟩
  have hm : Fintype.card m = Fintype.card n+(Fintype.card m-Fintype.card n) := by omega
  have hsq : 1 ≤ Fintype.card n*Fintype.card n := Nat.mul_pos hn hn
  have he : Fintype.card n*Fintype.card n+Fintype.card n*Fintype.card m =
      2*(Fintype.card n*Fintype.card n)+Fintype.card n*(Fintype.card m-Fintype.card n) := by
    conv_lhs => rw [hm]
    ring
  rw [he]
  omega

theorem generic_above_sl_kronecker_decomposition (i₀ : n)
    (hnm : Fintype.card n < Fintype.card m) :
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) i₀)
      (balancedDegreeList (Fintype.card n*Fintype.card n-1)
        (Fintype.card n*(Fintype.card m-Fintype.card n)+1)) := by
  exact slKirillovMatrix_kronecker _ _ i₀ _
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m)
    (generic_above_sl_minimal_degrees i₀ hnm) (above_sl_dimension_budget i₀ hnm)

end FD56
