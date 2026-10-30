/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericSixOutputCorankTwoSLTangentFactor
import FD56.Hilbert.ReducedFactorHilbertTests
import FD56.Hilbert.BalancedDegreeProfile

/-! Two tangent Hilbert tests determine the balanced SL profile and its
full Kronecker decomposition for six outputs and remainder four.
The two tests are retained as explicit hypotheses. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false

variable {K : Type*} [Field K] [CharZero K]

private abbrev CorankTwoCriterionField (q : ℕ) :=
  AffineCoefficientField K (MatrixParameters (Fin (6*q+4)) (Fin 6))

theorem generic_six_output_corank_two_sl_degrees_of_tangent_tests
    (q : ℕ) (hq : 0<q) (i₀ : Fin (6*q+4))
    (hzero : Module.finrank (CorankTwoCriterionField (K:=K) q)
      (polynomialKernelAtDegree
        (sixOutputPluckerTangent (genericSixOutputCorankTwoMinors (K:=K) q))
        (3*interiorFullWeight 4 2 q/9-1))=0)
    (hcritical : Module.finrank (CorankTwoCriterionField (K:=K) q)
      (polynomialKernelAtDegree
        (sixOutputPluckerTangent (genericSixOutputCorankTwoMinors (K:=K) q))
        (3*interiorFullWeight 4 2 q/9))≤9-(3*interiorFullWeight 4 2 q)%9) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (6*q+4)) (Fin 6))
      (genericAffineRows K (Fin (6*q+4)) (Fin 6)) i₀)
      (balancedDegreeList (9*(interiorFullWeight 4 2 q-1)-3*interiorFullWeight 4 2 q) 9) := by
  obtain ⟨B,e,C,hV,hlead,_,hC,hVC,hAC,hsum⟩ :=
    generic_six_output_corank_two_sl_tangent_factor (K:=K) q hq i₀
  have hk : 0<3*interiorFullWeight 4 2 q/9 := by
    have hW := six_output_corank_two_weight q
    have hlarge : 42≤3*interiorFullWeight 4 2 q := by nlinarith
    omega
  have hbalance := reduced_factor_balanced_of_two_kernel_tests
    (polynomialKernelBasisMatrix _ B) C e (interiorFullWeight 4 2 q-1)
    (3*interiorFullWeight 4 2 q/9) ((3*interiorFullWeight 4 2 q)%9)
    hV hlead hC hVC _ hAC hk
    (by simp only [Fintype.card_fin]; omega)
    (by
      simp only [Fintype.card_fin]
      have hdiv := Nat.mod_add_div (3*interiorFullWeight 4 2 q) 9
      omega)
    hzero hcritical
  have hesum : (∑ i, e i)=9*(interiorFullWeight 4 2 q-1)-3*interiorFullWeight 4 2 q := by
    omega
  rw [←hesum]
  exact reduced_kernel_basis_balanced_minimal_degrees _ (by decide) B e hV hlead hbalance

theorem generic_six_output_corank_two_sl_classification_of_tangent_tests
    (q : ℕ) (hq : 0<q) (i₀ : Fin (6*q+4))
    (hzero : Module.finrank (CorankTwoCriterionField (K:=K) q)
      (polynomialKernelAtDegree
        (sixOutputPluckerTangent (genericSixOutputCorankTwoMinors (K:=K) q))
        (3*interiorFullWeight 4 2 q/9-1))=0)
    (hcritical : Module.finrank (CorankTwoCriterionField (K:=K) q)
      (polynomialKernelAtDegree
        (sixOutputPluckerTangent (genericSixOutputCorankTwoMinors (K:=K) q))
        (3*interiorFullWeight 4 2 q/9))≤9-(3*interiorFullWeight 4 2 q)%9) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (6*q+4)) (Fin 6))
      (genericAffineRows K (Fin (6*q+4)) (Fin 6)) i₀)
      (balancedDegreeList (9*(interiorFullWeight 4 2 q-1)-3*interiorFullWeight 4 2 q) 9) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (6*q+4)) (Fin 6))
      (genericAffineRows K (Fin (6*q+4)) (Fin 6)) i₀)
      (balancedDegreeList (9*(interiorFullWeight 4 2 q-1)-3*interiorFullWeight 4 2 q) 9) := by
  let ys := balancedDegreeList
    (9*(interiorFullWeight 4 2 q-1)-3*interiorFullWeight 4 2 q) 9
  have hmin := generic_six_output_corank_two_sl_degrees_of_tangent_tests
    (K:=K) q hq i₀ hzero hcritical
  refine ⟨hmin,?_⟩
  obtain ⟨xs,_,_,hxs,hcanon⟩ := generic_nondivisible_sl_kronecker_structure
    (K:=K) (n:=Fin (6*q+4)) (m:=Fin 6) q hq i₀
    (by simp only [Fintype.card_fin]; omega) (by simp only [Fintype.card_fin]; omega)
  have hp : xs.Perm ys := by
    apply listHilbert_determines_indices
    intro d
    rw [listHilbert_nat,listHilbert_nat]
    exact_mod_cast ((hasMinimalKernelDegrees_iff_hilbert _ xs).mp hxs d).symm.trans
      ((hasMinimalKernelDegrees_iff_hilbert _ ys).mp hmin d)
  obtain ⟨k,e,he,T,U,hTU,hUT,hcanonical⟩ := hcanon
  exact ⟨k,e,he.trans hp,T,U,hTU,hUT,hcanonical⟩

end FD56
