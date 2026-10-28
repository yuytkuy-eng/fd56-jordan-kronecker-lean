/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MinimalDegreeBudgetTests
import FD56.Hilbert.GenericObservabilityBetaBudget

/-! At every strictly nondivisible depth, two finite tests determine the terminal
minimal degrees. Equal degrees require only one test. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n m r : Type*} [Field K] [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m]

theorem generic_observability_beta_degrees_of_budget_tests
    (q D a b : ℕ) (hm : 2≤Fintype.card m)
    (hlo : q*Fintype.card m<Fintype.card n) (hhi : Fintype.card n<(q+1)*Fintype.card m)
    (B : Basis r (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) q))))
    (hD : 0<D) (hlen : a+b=(q+1)*Fintype.card m-Fintype.card n)
    (hweight : 2*(D*(a+b)+b)=
      Fintype.card m*q*(q+1)+2*(q+1)*(Fintype.card n-q*Fintype.card m))
    (hzero : Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedObservabilityBetaKernel q (genericAffineSquare K n m)
        (genericAffineRows K n m) (D-1))=0)
    (hcritical : Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedObservabilityBetaKernel q (genericAffineSquare K n m)
        (genericAffineRows K n m) D)≤a) :
    HasMinimalKernelDegrees
      (genericAffineRows K n m*(genericAffineSquare K n m)^q*
        polynomialKernelBasisMatrix (observabilityMatrix
          (genericAffineSquare K n m) (genericAffineRows K n m) q) B).transpose
      (balancedDegreeList (D*(a+b)+b) (a+b)) := by
  let T := (genericAffineRows K n m*(genericAffineSquare K n m)^q*
    polynomialKernelBasisMatrix (observabilityMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) q) B).transpose
  obtain ⟨s,Bt,e,hT,hTL,_,_⟩ := polynomial_kernel_has_minimal_basis T
  have hmin : HasMinimalKernelDegrees T (List.ofFn e) := ⟨s,Bt,e,hT,hTL,List.Perm.refl _⟩
  obtain ⟨hl,hs⟩ := generic_observability_beta_degree_budget q hm hlo hhi B _ hmin
  have hstep : (q+1)*Fintype.card m=q*Fintype.card m+Fintype.card m := by ring
  apply minimal_degrees_balanced_of_budget_tests T _ hmin D a b hD
    (by omega) (by omega) (by omega)
  · rwa [← generic_observability_actual_beta_finrank q hlo B (D-1)]
  · rwa [← generic_observability_actual_beta_finrank q hlo B D]

theorem generic_observability_beta_degrees_of_single_budget_test
    (q D c : ℕ) (hm : 2≤Fintype.card m)
    (hlo : q*Fintype.card m<Fintype.card n) (hhi : Fintype.card n<(q+1)*Fintype.card m)
    (B : Basis r (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) q))))
    (hD : 0<D) (hlen : c=(q+1)*Fintype.card m-Fintype.card n)
    (hweight : 2*(D*c)=
      Fintype.card m*q*(q+1)+2*(q+1)*(Fintype.card n-q*Fintype.card m))
    (hzero : Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedObservabilityBetaKernel q (genericAffineSquare K n m)
        (genericAffineRows K n m) (D-1))=0) :
    HasMinimalKernelDegrees
      (genericAffineRows K n m*(genericAffineSquare K n m)^q*
        polynomialKernelBasisMatrix (observabilityMatrix
          (genericAffineSquare K n m) (genericAffineRows K n m) q) B).transpose
      (List.replicate c D) := by
  let T := (genericAffineRows K n m*(genericAffineSquare K n m)^q*
    polynomialKernelBasisMatrix (observabilityMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) q) B).transpose
  obtain ⟨s,Bt,e,hT,hTL,_,_⟩ := polynomial_kernel_has_minimal_basis T
  have hmin : HasMinimalKernelDegrees T (List.ofFn e) := ⟨s,Bt,e,hT,hTL,List.Perm.refl _⟩
  obtain ⟨hl,hs⟩ := generic_observability_beta_degree_budget q hm hlo hhi B _ hmin
  have hstep : (q+1)*Fintype.card m=q*Fintype.card m+Fintype.card m := by ring
  apply minimal_degrees_uniform_of_budget_test T _ hmin D c hD
    (by omega) (by omega) (by omega)
  rwa [← generic_observability_actual_beta_finrank q hlo B (D-1)]

end FD56
