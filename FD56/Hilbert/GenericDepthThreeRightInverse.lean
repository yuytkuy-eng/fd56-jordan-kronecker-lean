/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericDepthThreeAlpha
import FD56.Hilbert.DepthTwoRowLifting

/-! A polynomial right inverse for the actual third generic observability stack. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m : Type*} [Field K]
  [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem generic_depth_three_coefficient_surjective
    (hmn : 3*Fintype.card m < Fintype.card n) :
    Function.Surjective (weightedCoefficientMatrix
      (observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) 3)
      (fun _ => 6*Fintype.card m)
      (fun ij => 6*Fintype.card m+ij.1.val+1)).mulVec := by
  have hsum : ∑ ij : Fin 3 × m, (ij.1.val+1)=6*Fintype.card m := by
    simp [Fintype.sum_prod_type,Fin.sum_univ_succ]
    omega
  let O := observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) 3
  have hO : ∀ i j, (O i j).natDegree ≤ i.1.val+1 := fun i j =>
    (observability_polynomial_degree_top _ _ 3
      (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) i j).1
  simpa only [Nat.add_assoc] using
    (column_coefficient_surjective_of_kernel_hilbert O.transpose (fun ij => ij.1.val+1)
      (6*Fintype.card m) (fun j i => hO i j)
      (by simp only [Fintype.card_prod,Fintype.card_fin]; omega)
      (by
        rw [hsum]
        simp only [Fintype.card_prod,Fintype.card_fin]
        have hr : 1 ≤ Fintype.card n-3*Fintype.card m := by omega
        nlinarith)
      (by
        rw [Matrix.transpose_transpose,hsum]
        simp only [Fintype.card_prod,Fintype.card_fin]
        exact generic_depth_three_alpha_hilbert hmn _))

theorem generic_actual_depth_three_stack_right_inverse
    (hmn : 3*Fintype.card m < Fintype.card n) :
    ∃ R : Matrix n (Fin 3 × m) (AffineCoefficientField K (MatrixParameters n m))[X],
      DegreeBound R (6*Fintype.card m) ∧
      observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) 3*R=1 := by
  apply weighted_right_inverse_of_coefficient_surjective _ (fun ij => ij.1.val+1)
    (6*Fintype.card m)
  · intro i j
    exact (observability_polynomial_degree_top _ _ 3
      (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) i j).1
  · simpa only [Nat.add_assoc] using generic_depth_three_coefficient_surjective (K := K) hmn

omit [Fintype m] [DecidableEq n] [DecidableEq m] in
theorem row_leading_surjective_of_coefficient_surjective
    (A : Matrix m n K[X]) (e : m → ℕ) (d : ℕ)
    (hA : ∀ i j, (A i j).natDegree ≤ e i)
    (hs : Function.Surjective (weightedCoefficientMatrix A
      (fun _ => d) (fun i => d+e i)).mulVec) :
    Function.Surjective (Matrix.mulVec (fun i j => (A i j).coeff (e i))) := by
  classical
  intro w
  let z : (Σ i, Fin (d+e i+1)) → K := fun ik =>
    if ik.2.val=d+e ik.1 then w ik.1 else 0
  obtain ⟨v,hv⟩ := hs z
  let p := weightedCoefficientPolynomial (fun _ : n => d) v
  refine ⟨fun j => (p j).coeff d, ?_⟩
  funext i
  have ht := congrFun hv ⟨i,⟨d+e i,by omega⟩⟩
  rw [weightedCoefficientMatrix_mulVec] at ht
  have hc : ((A *ᵥ p) i).coeff (d+e i)=
      ∑ j, (A i j).coeff (e i)*(p j).coeff d := by
    simp only [Matrix.mulVec,dotProduct,Polynomial.finset_sum_coeff]
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.add_comm d]
    exact Polynomial.coeff_mul_add_eq_of_natDegree_le (hA i j)
      (weightedCoefficientPolynomial_degree (fun _ : n => d) v j)
  change ((A *ᵥ p) i).coeff (d+e i) = z ⟨i,⟨d+e i,by omega⟩⟩ at ht
  rw [hc] at ht
  simpa only [z,if_pos rfl,Matrix.mulVec,dotProduct] using ht

theorem generic_actual_depth_three_stack_leading_injective
    (hmn : 3*Fintype.card m < Fintype.card n) :
    Function.Injective (Matrix.mulVec (fun x ij =>
      (observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) 3 ij x).coeff
        (ij.1.val+1))) := by
  apply matrix_transpose_injective_of_surjective
  apply row_leading_surjective_of_coefficient_surjective
    (observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) 3)
    (fun ij => ij.1.val+1)
    (6*Fintype.card m)
  · intro i j
    exact (observability_polynomial_degree_top _ _ 3
      (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) i j).1
  · simpa only [Nat.add_assoc] using generic_depth_three_coefficient_surjective (K := K) hmn

end FD56
