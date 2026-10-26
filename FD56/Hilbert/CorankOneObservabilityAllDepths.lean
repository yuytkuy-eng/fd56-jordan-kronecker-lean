/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericObservabilityLeading
import FD56.Stabilizer.GenericObservabilityCoprime
import FD56.LinearAlgebra.CorankOneKernelGenerator
import FD56.LinearAlgebra.LastRowBlockMinor
import FD56.LinearAlgebra.WeightedDeterminantDegree
import FD56.Hilbert.ObservabilityBetaCofactorBound

/-! Exact terminal minors and short-relation vanishing in every corank-one depth. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_corank_one_all_depths_leading_minor (q : ℕ)
    (hm : 2 ≤ Fintype.card m)
    (hn : Fintype.card n + 1 = (q+1) * Fintype.card m) :
    ∃ (j : m) (e : n ≃ {ij : Fin (q+1) × m // ij ≠ (Fin.last q,j)}),
      (Matrix.det (fun x y =>
        (observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m)
          (q+1) (e x).val y).coeff ((e x).val.1.val+1))) ≠ 0 := by
  let A : Matrix (Fin (q+1) × m) n (AffineCoefficientField K (MatrixParameters n m)) :=
    fun ij x => (observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m)
      (q+1) ij x).coeff (ij.1.val+1)
  have hsize : q * Fintype.card m ≤ Fintype.card n := by nlinarith
  have hA : Function.Injective A.mulVec :=
    generic_tall_observability_leading_injective (q+1) (by omega)
  have hprefix : Function.Injective
      (A.submatrix (fun ij : Fin q × m => (ij.1.castSucc,ij.2)) id).transpose.mulVec :=
    generic_observability_row_leading_injective q hsize
  exact exists_last_block_complement_minor q A hn hA hprefix

omit [DecidableEq n] in
theorem corank_one_all_depths_minor_row_weight (q : ℕ) (j : m)
    (e : n ≃ {ij : Fin (q+1) × m // ij ≠ (Fin.last q,j)}) :
    (∑ x : n, ((e x).val.1.val+1)) =
      Fintype.card m * (∑ i : Fin (q+1), (i.val+1)) - (q+1) := by
  classical
  let w : Fin (q+1) × m → ℕ := fun ij => ij.1.val+1
  have ht : (∑ ij : Fin (q+1) × m, w ij) =
      Fintype.card m * (∑ i : Fin (q+1), (i.val+1)) := by
    simp only [w, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Finset.mul_sum]
  have hs := (Equiv.optionSubtypeNe (Fin.last q,j)).sum_comp w
  rw [Fintype.sum_option] at hs
  have he := e.sum_comp (fun ij => w ij.val)
  have hw : w (Fin.last q,j) = q+1 := rfl
  simp only [Equiv.optionSubtypeNe_none, Equiv.optionSubtypeNe_some] at hs
  rw [ht,hw] at hs
  change (∑ x : n, w (e x).val) = _
  rw [he]
  exact Nat.eq_sub_of_add_eq (by simpa only [Nat.add_comm] using hs)

theorem generic_corank_one_all_depths_minor_exact_degree (q : ℕ)
    (hm : 2 ≤ Fintype.card m)
    (hn : Fintype.card n + 1 = (q+1) * Fintype.card m) :
    ∃ (j : m) (e : n ≃ {ij : Fin (q+1) × m // ij ≠ (Fin.last q,j)}),
      ((observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) (q+1)).submatrix
        (fun x => (e x).val) id).det.natDegree =
          Fintype.card m * (∑ i : Fin (q+1), (i.val+1)) - (q+1) ∧
      ((observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) (q+1)).submatrix
        (fun x => (e x).val) id).det ≠ 0 := by
  obtain ⟨j,e,hlead⟩ := generic_corank_one_all_depths_leading_minor (K := K) q hm hn
  let A := (observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) (q+1)).submatrix
    (fun x => (e x).val) id
  let d : n → ℕ := fun x => (e x).val.1.val+1
  have hA : ∀ x y, (A x y).natDegree ≤ d x := fun x y =>
    (observability_polynomial_degree_top _ _ (q+1) (genericAffineSquare_degree K n m)
      (genericAffineRows_degree K n m) (e x).val y).1
  refine ⟨j,e,?_,polynomial_det_ne_zero_of_row_leading_det_ne_zero A d hA hlead⟩
  rw [polynomial_det_natDegree_eq_row_sum A d hA hlead]
  exact corank_one_all_depths_minor_row_weight q j e

theorem generic_corank_one_all_depths_beta_zero (q d : ℕ)
    (hm : 2 ≤ Fintype.card m)
    (hn : Fintype.card n + 1 = (q+1) * Fintype.card m)
    (hd : d < Fintype.card m * (∑ i : Fin (q+1), (i.val+1)) - (q+1)) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedObservabilityBetaKernel q (genericAffineSquare K n m)
        (genericAffineRows K n m) d) = 0 := by
  obtain ⟨j,e,hdeg,hne⟩ := generic_corank_one_all_depths_minor_exact_degree (K := K) q hm hn
  obtain ⟨c,hc,_,hgen⟩ := corank_one_kernel_generator
    (observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) (q+1))
    (Fin.last q,j) e (generic_affine_observability_common_divisor_isUnit (q+1) hm (by omega))
  apply boundedObservabilityBetaKernel_finrank_zero_of_relation_generator q
    (genericAffineSquare K n m) (genericAffineRows K n m) d c
    (fun y hy => ((hgen y).mp hy).exists) j
  · rwa [hc]
  · rwa [hc,hdeg]

end FD56
