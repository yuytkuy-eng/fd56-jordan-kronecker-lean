/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MinimalDegreeBudgetTests
import FD56.Hilbert.GenericObservabilityDegreeBudget

/-! Two finite Hilbert tests determine the first auxiliary degree list at every depth. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_observability_alpha_degrees_of_budget_tests
    (q D a b : ℕ) (hwide : q*Fintype.card m<Fintype.card n)
    (hD : 0<D) (hlen : a+b=Fintype.card n-q*Fintype.card m)
    (hweight : 2*(D*(a+b)+b)=Fintype.card m*q*(q+1))
    (hzero : Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) q) (D-1))=0)
    (hcritical : Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) q) D)≤a) :
    HasMinimalKernelDegrees (observabilityMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) q)
      (balancedDegreeList (D*(a+b)+b) (a+b)) := by
  let O := observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q
  obtain ⟨r,B,e,hV,hVL,_,_⟩ := polynomial_kernel_has_minimal_basis O
  have hmin : HasMinimalKernelDegrees O (List.ofFn e) := ⟨r,B,e,hV,hVL,List.Perm.refl _⟩
  obtain ⟨hl,hs⟩ := generic_observability_kernel_degree_budget (K:=K) q hwide _ hmin
  exact minimal_degrees_balanced_of_budget_tests O _ hmin D a b hD (by omega)
    (by omega) (by omega) hzero hcritical

theorem generic_observability_alpha_degrees_of_single_budget_test
    (q D r : ℕ) (hwide : q*Fintype.card m<Fintype.card n)
    (hD : 0<D) (hlen : r=Fintype.card n-q*Fintype.card m)
    (hweight : 2*(D*r)=Fintype.card m*q*(q+1))
    (hzero : Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) q) (D-1))=0) :
    HasMinimalKernelDegrees (observabilityMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) q) (List.replicate r D) := by
  let O := observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q
  obtain ⟨s,B,e,hV,hVL,_,_⟩ := polynomial_kernel_has_minimal_basis O
  have hmin : HasMinimalKernelDegrees O (List.ofFn e) := ⟨s,B,e,hV,hVL,List.Perm.refl _⟩
  obtain ⟨hl,hs⟩ := generic_observability_kernel_degree_budget (K:=K) q hwide _ hmin
  exact minimal_degrees_uniform_of_budget_test O _ hmin D r hD (by omega)
    (by omega) (by omega) hzero

end FD56
