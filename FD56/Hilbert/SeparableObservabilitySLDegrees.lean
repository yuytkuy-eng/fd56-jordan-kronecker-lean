/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ObservabilityScalarAdjugateDegree
import FD56.Hilbert.ObservabilityScalarFunctional
import FD56.Hilbert.MinimalDegreeNullity
import FD56.Stabilizer.SLKirillovPencil

/-! A separable square observability determinant determines the singleton SL minimal degree. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem slHilbert_positive_of_observability_adjugate
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (i₀ : n)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (level : n → ℕ) (row : n → m) (e : ℕ)
    (he : (∑ k, (level k+1))=e+1)
    (hLower : ∀ k s, s<level k → ∀ a, ∃ l, level l=s ∧ row l=a)
    (hd : (observabilitySelectedMatrix M P level row).det≠0) :
    0<slHilbert M P e := by
  letI : Nonempty n := ⟨i₀⟩
  let A := observabilitySelectedMatrix M P level row
  let X := observabilityScalarX M P A.adjugate level row
  let U := observabilityScalarU M A.adjugate level row
  obtain ⟨hX,hU,_⟩ := observability_adjugate_solution_degree M P hM hP level row e he
  obtain ⟨hPX,ht,hcomm⟩ := observability_adjugate_scalar_equations M P level row hLower
  have hr : SLRadical M P X U :=
    (slRadical_iff_equations M P X U).mpr ⟨ht,hPX,-A.det,hcomm⟩
  let z : boundedSLKernel M P e := ⟨(boundedMatrixOf X hX,boundedMatrixOf U hU),hr⟩
  apply (Module.finrank_pos_iff_exists_ne_zero (R := K) (M := boundedSLKernel M P e)).mpr
  refine ⟨z,?_⟩
  intro hz
  have hzX : X=0 := congrArg (fun v : boundedSLKernel M P e => entries v.val.1) hz
  have hzU : U=0 := congrArg (fun v : boundedSLKernel M P e => entries v.val.2) hz
  change M*X-X*M=U*P+(-A.det)•1 at hcomm
  simp only [hzX,hzU,Matrix.mul_zero,Matrix.zero_mul,sub_zero,zero_add] at hcomm
  have hh := congrFun (congrFun hcomm i₀) i₀
  apply hd
  simpa using hh.symm

theorem sl_minimal_degrees_of_separable_observability
    {F : Type*} [Field F] [Algebra K[X] F] [IsFractionRing K[X] F]
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (i₀ : n)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (level : n → ℕ) (row : n → m) (e : ℕ)
    (he : (∑ k, (level k+1))=e+1)
    (hLower : ∀ k s, s<level k → ∀ a, ∃ l, level l=s ∧ row l=a)
    (hs : (observabilitySelectedMatrix M P level row).det.Separable)
    (hdegree : (observabilitySelectedMatrix M P level row).det.natDegree=e+1)
    (hinj : Function.Injective (glEquationMatrix M P).mulVec)
    (hnull : Module.finrank F (LinearMap.ker (Matrix.toLin'
      ((slEquationMatrix M P i₀).map (algebraMap K[X] F))))=1) :
    HasMinimalKernelDegrees (slEquationMatrix M P i₀) [e] := by
  obtain ⟨r,B,d,hB,hL,_,_⟩ := polynomial_kernel_has_minimal_basis (slEquationMatrix M P i₀)
  have hmin : HasMinimalKernelDegrees (slEquationMatrix M P i₀) (List.ofFn d) :=
    ⟨r,B,d,hB,hL,List.Perm.refl _⟩
  have hl : (List.ofFn d).length=1 :=
    (hmin.length_eq_fraction_nullity (F := F)).trans hnull
  obtain ⟨D,hD⟩ := List.length_eq_one_iff.mp hl
  rw [hD] at hmin
  have hhilb (k : ℕ) : slHilbert M P k=k+1-D := by
    rw [slHilbert_eq_matrix_kernel M P i₀ k,
      (hasMinimalKernelDegrees_iff_hilbert _ _).mp hmin]
    simp
  have hpos := slHilbert_positive_of_observability_adjugate M P i₀ hM hP level row e he hLower hs.ne_zero
  rw [hhilb] at hpos
  have hDe : D≤e := by omega
  have hEq : D=e := by
    by_contra hn
    have hz := slHilbert_zero_of_separable_observability M P i₀ D hM hP level row hLower hs
      (by rw [hdegree]; omega) hinj
    rw [hhilb] at hz
    omega
  simpa only [hEq] using hmin

end FD56
