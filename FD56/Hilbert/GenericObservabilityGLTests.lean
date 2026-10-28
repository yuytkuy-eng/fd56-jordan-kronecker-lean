/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericObservabilityAlphaTests
import FD56.Hilbert.GenericObservabilityBetaTests
import FD56.Hilbert.GenericObservabilityGL
import FD56.Hilbert.GeneralGLDimension
import FD56.Hilbert.MixedGLKronecker

/-! Four finite Hilbert tests certify the full balanced-auxiliary GL formula at
any strictly nondivisible depth. The tests remain explicit hypotheses. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

set_option maxHeartbeats 2000000 in
theorem generic_observability_gl_kronecker_of_four_tests
    (q Da a b Db c d : ℕ)
    (hlo : (q+1)*Fintype.card m<Fintype.card n)
    (hhi : Fintype.card n<(q+2)*Fintype.card m)
    (hDa : 0<Da) (hDb : 0<Db)
    (hlenA : a+b=Fintype.card n-(q+1)*Fintype.card m)
    (hlenB : c+d=(q+2)*Fintype.card m-Fintype.card n)
    (hweightA : 2*(Da*(a+b)+b)=Fintype.card m*(q+1)*(q+2))
    (hweightB : 2*(Db*(c+d)+d)=
      Fintype.card m*(q+1)*(q+2)+2*(q+2)*(Fintype.card n-(q+1)*Fintype.card m))
    (hzeroA : Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) (q+1)) (Da-1))=0)
    (hcriticalA : Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) (q+1)) Da)≤a)
    (hzeroB : Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedObservabilityBetaKernel (q+1) (genericAffineSquare K n m)
        (genericAffineRows K n m) (Db-1))=0)
    (hcriticalB : Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedObservabilityBetaKernel (q+1) (genericAffineSquare K n m)
        (genericAffineRows K n m) Db)≤c) :
    let xs := (degreeConvolution (balancedDegreeList (Da*(a+b)+b) (a+b))
      (balancedDegreeList (Db*(c+d)+d) (c+d))).map (fun e => e+q)
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m)) xs ∧
    HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m)) xs := by
  let alpha := balancedDegreeList (Da*(a+b)+b) (a+b)
  let beta := balancedDegreeList (Db*(c+d)+d) (c+d)
  let xs := (degreeConvolution alpha beta).map (fun e => e+q)
  have hstep : (q+2)*Fintype.card m=(q+1)*Fintype.card m+Fintype.card m := by ring
  have hm : 2≤Fintype.card m := by
    by_contra h
    have hc : Fintype.card m=0 ∨ Fintype.card m=1 := by omega
    rcases hc with h|h <;> simp only [h,Nat.mul_zero,Nat.mul_one] at hlo hhi <;> omega
  have ha : 0<a+b := by omega
  have hb : 0<c+d := by omega
  have hAlpha : HasMinimalKernelDegrees (observabilityMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) (q+1)) alpha :=
    generic_observability_alpha_degrees_of_budget_tests (q+1) Da a b hlo hDa hlenA
      (by simpa only [Nat.add_assoc] using hweightA) hzeroA hcriticalA
  obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse (K:=K) (q+1) hlo
  have hmin : HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m)) xs := by
    apply generic_observability_gl_minimal_degrees q hlo.le hhi.le R hR alpha beta hAlpha
    intro r B
    apply generic_observability_beta_degrees_of_budget_tests (q+1) Db c d hm hlo
      (by simpa only [Nat.add_assoc] using hhi) B hDb
      (by simpa only [Nat.add_assoc] using hlenB)
      (by simpa only [Nat.add_assoc] using hweightB) hzeroB hcriticalB
  refine ⟨hmin,?_⟩
  apply glKirillovMatrix_kronecker _ _ xs (genericAffineSquare_degree K n m)
    (genericAffineRows_degree K n m) hmin
  have hal : alpha.length=a+b := balancedDegreeList_length _ _ ha
  have hbl : beta.length=c+d := balancedDegreeList_length _ _ hb
  have has : alpha.sum=Da*(a+b)+b := balancedDegreeList_sum _ _ ha
  have hbs : beta.sum=Db*(c+d)+d := balancedDegreeList_sum _ _ hb
  have hsum : beta.sum=alpha.sum+(q+2)*alpha.length := by
    rw [has,hbs,hal]
    rw [← hlenA] at hweightB
    nlinarith
  have hdim := observability_gl_dimension_budget (Fintype.card m) (Fintype.card n) q
    alpha beta (by omega) (by omega) (by omega) hsum
  rw [hdim]
  simp only [SLInput,Fintype.card_sum,Fintype.card_prod]
  ring

end FD56
