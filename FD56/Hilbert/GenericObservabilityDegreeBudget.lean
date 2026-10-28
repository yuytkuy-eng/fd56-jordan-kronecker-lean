/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.PrimitiveRowDegreeBudget
import FD56.Hilbert.GenericObservabilityLeading
import FD56.Stabilizer.GenericWideObservabilityRightInverse

/-! The length and total degree of every generic wide observability kernel,
without a claim that its individual minimal degrees are balanced. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

private theorem observability_weight_twice (q : ℕ) :
    2*(∑ i : Fin q × m, (i.1.val+1))=Fintype.card m*q*(q+1) := by
  have ht (q : ℕ) : 2*(∑ i : Fin q, (i.val+1))=q*(q+1) := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.coe_castSucc,Fin.val_last]
      nlinarith
  have hs : (∑ i : Fin q × m, (i.1.val+1))=
      Fintype.card m*(∑ i : Fin q, (i.val+1)) := by
    simp [Fintype.sum_prod_type,Finset.mul_sum]
  rw [hs]
  nlinarith [ht q]

theorem generic_observability_kernel_degree_budget (q : ℕ)
    (hwide : q*Fintype.card m<Fintype.card n) (xs : List ℕ)
    (hmin : HasMinimalKernelDegrees (observabilityMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) q) xs) :
    xs.length+q*Fintype.card m=Fintype.card n ∧
      2*xs.sum=Fintype.card m*q*(q+1) := by
  let M := genericAffineSquare K n m
  let P := genericAffineRows K n m
  obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse (K:=K) q hwide
  have hlead : Function.Surjective (show Matrix (Fin q × m) n
      (AffineCoefficientField K (MatrixParameters n m)) from
      fun i j => (observabilityMatrix M P q i j).coeff (i.1.val+1)).mulVec := by
    have he : (show Matrix (Fin q × m) n (AffineCoefficientField K (MatrixParameters n m)) from
      fun i j => (observabilityMatrix M P q i j).coeff (i.1.val+1))=
        observabilityMatrix (matrixCoeff M 1) (matrixCoeff P 1) q := by
      funext i j
      exact (observability_polynomial_degree_top M P q
        (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) i j).2
    rw [he]
    exact generic_observability_leading_pair_surjective q hwide.le
  obtain ⟨hl,hs⟩ := minimal_degree_budget_of_right_inverse_and_leading
    (observabilityMatrix M P q) R hR (fun i => i.1.val+1)
    (fun i j => (observability_polynomial_degree_top M P q
      (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) i j).1)
    hlead xs hmin
  refine ⟨by simpa only [Fintype.card_prod,Fintype.card_fin] using hl,?_⟩
  rw [hs]
  exact observability_weight_twice q

end FD56
