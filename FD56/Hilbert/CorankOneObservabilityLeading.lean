/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericDepthThreeRightInverse
import FD56.Hilbert.GenericTerminalObservability
import FD56.LinearAlgebra.LastRowBlockMinor
import FD56.LinearAlgebra.WeightedDeterminantDegree

/-! A terminal-block deletion minor has the expected exact corank-one degree. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m : Type*} [Field K]
  [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- Row-leading coefficients preserve the universal terminal column rank. -/
theorem generic_terminal_observability_leading_injective
    (q : ℕ) (hmn : q * Fintype.card m ≤ Fintype.card n)
    (hnm : Fintype.card n ≤ (q + 1) * Fintype.card m) :
    Function.Injective (Matrix.mulVec (fun (ij : Fin (q + 1) × m) x =>
      (observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m)
        (q + 1) ij x).coeff (ij.1.val + 1))) := by
  let φ : MvPolynomial (MatrixParameters n m) K →+*
      AffineCoefficientField K (MatrixParameters n m) :=
    (algebraMap (MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K) _).comp
      (MvPolynomial.rename (Sum.inr : MatrixParameters n m →
        MatrixParameters n m ⊕ MatrixParameters n m)).toRingHom
  have hφ : Function.Injective φ := by
    exact (IsFractionRing.injective
      (MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K)
      (AffineCoefficientField K (MatrixParameters n m))).comp
        (MvPolynomial.rename_injective (R := K)
          (Sum.inr : MatrixParameters n m → MatrixParameters n m ⊕ MatrixParameters n m)
          Sum.inr_injective)
  have hM : matrixCoeff (genericAffineSquare K n m) 1 = (universalSquare K n m).map φ := by
    ext i j
    simp [matrixCoeff, genericAffineSquare, universalSquare, affineParameterMap, φ]
  have hP : matrixCoeff (genericAffineRows K n m) 1 = (universalRows K n m).map φ := by
    ext i j
    simp [matrixCoeff, genericAffineRows, universalRows, affineParameterMap, φ]
  have he : (fun (ij : Fin (q + 1) × m) x =>
      (observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m)
        (q + 1) ij x).coeff (ij.1.val + 1)) =
      observabilityMatrix ((universalSquare K n m).map φ)
        ((universalRows K n m).map φ) (q + 1) := by
    funext ij x
    rw [(observability_polynomial_degree_top _ _ (q + 1)
      (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) ij x).2,
      hM, hP]
    rfl
  rw [he]
  exact universal_terminal_observability_injective q hmn hnm φ hφ

theorem generic_corank_one_terminal_leading_minor
    (hm : 2 ≤ Fintype.card m) (hn : Fintype.card n + 1 = 4 * Fintype.card m) :
    ∃ (j : m) (e : n ≃ {ij : Fin 4 × m // ij ≠ (Fin.last 3, j)}),
      (Matrix.det (fun x y =>
        (observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m)
          4 (e x).val y).coeff ((e x).val.1.val + 1))) ≠ 0 := by
  let A : Matrix (Fin 4 × m) n (AffineCoefficientField K (MatrixParameters n m)) :=
    fun ij x => (observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m)
      4 ij x).coeff (ij.1.val + 1)
  have hA : Function.Injective A.mulVec :=
    generic_terminal_observability_leading_injective 3 (by omega) (by omega)
  have hprefix : Function.Injective
      (A.submatrix (fun ij : Fin 3 × m => (ij.1.castSucc, ij.2)) id).transpose.mulVec :=
    generic_actual_depth_three_stack_leading_injective (by omega)
  exact exists_last_block_complement_minor 3 A hn hA hprefix

omit [DecidableEq n] in
/-- The deleted terminal row has weight four, leaving total row degree `10m - 4`. -/
theorem corank_one_terminal_minor_row_weight (j : m)
    (e : n ≃ {ij : Fin 4 × m // ij ≠ (Fin.last 3, j)}) :
    (∑ x : n, ((e x).val.1.val + 1)) = 10 * Fintype.card m - 4 := by
  classical
  let w : Fin 4 × m → ℕ := fun ij => ij.1.val + 1
  have ht : (∑ ij : Fin 4 × m, w ij) = 10 * Fintype.card m := by
    simp [w, Fintype.sum_prod_type, Fin.sum_univ_succ]
    omega
  have hs := (Equiv.optionSubtypeNe (Fin.last 3, j)).sum_comp w
  rw [Fintype.sum_option] at hs
  have he := e.sum_comp (fun ij => w ij.val)
  have hw : w (Fin.last 3, j) = 4 := rfl
  simp only [Equiv.optionSubtypeNe_none, Equiv.optionSubtypeNe_some] at hs
  rw [ht, hw] at hs
  change (∑ x : n, w (e x).val) = _
  rw [he]
  exact Nat.eq_sub_of_add_eq (by simpa only [Nat.add_comm] using hs)

/-- This is an actual generic polynomial minor, not only a degree bound or witness calculation. -/
theorem generic_corank_one_terminal_minor_exact_degree
    (hm : 2 ≤ Fintype.card m) (hn : Fintype.card n + 1 = 4 * Fintype.card m) :
    ∃ (j : m) (e : n ≃ {ij : Fin 4 × m // ij ≠ (Fin.last 3, j)}),
      ((observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) 4).submatrix
        (fun x => (e x).val) id).det.natDegree = 10 * Fintype.card m - 4 ∧
      ((observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) 4).submatrix
        (fun x => (e x).val) id).det ≠ 0 := by
  obtain ⟨j, e, hlead⟩ := generic_corank_one_terminal_leading_minor (K := K) hm hn
  let A := (observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) 4).submatrix
    (fun x => (e x).val) id
  let d : n → ℕ := fun x => (e x).val.1.val + 1
  have hA : ∀ x y, (A x y).natDegree ≤ d x := fun x y =>
    (observability_polynomial_degree_top _ _ 4 (genericAffineSquare_degree K n m)
      (genericAffineRows_degree K n m) (e x).val y).1
  refine ⟨j, e, ?_, polynomial_det_ne_zero_of_row_leading_det_ne_zero A d hA hlead⟩
  rw [polynomial_det_natDegree_eq_row_sum A d hA hlead]
  exact corank_one_terminal_minor_row_weight j e

end FD56
