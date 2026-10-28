/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericObservabilityDegreeBudget
import FD56.Hilbert.GenericTerminalDegreeBudget
import FD56.Hilbert.GenericObservabilityGL
import FD56.Hilbert.GeneralGLDimension
import FD56.Hilbert.MixedGLKronecker

/-! Every strictly nondivisible generic GL pencil is a pure Kronecker pencil.
The block count and total degree are exact; individual degrees remain unspecified. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

private theorem convolution_list_length (alpha beta : List ℕ) :
    (degreeConvolution alpha beta).length=alpha.length*beta.length := by
  induction alpha with
  | nil => simp [degreeConvolution]
  | cons a alpha ih =>
    simp only [degreeConvolution,List.flatMap_cons,List.length_append,List.length_map,
      List.length_cons] at ih ⊢
    rw [ih]
    ring

theorem generic_nondivisible_gl_kronecker_structure
    (q : ℕ) (hq : 0<q)
    (hlo : q*Fintype.card m<Fintype.card n)
    (hhi : Fintype.card n<(q+1)*Fintype.card m) :
    ∃ xs : List ℕ,
      xs.length=(Fintype.card n-q*Fintype.card m)*((q+1)*Fintype.card m-Fintype.card n) ∧
      2*xs.sum+xs.length=Fintype.card n*(Fintype.card n+Fintype.card m) ∧
      HasMinimalKernelDegrees (glEquationMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m)) xs ∧
      HasKroneckerDecomposition (glKirillovMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m)) xs := by
  cases q with
  | zero => omega
  | succ q =>
    have hm : 2≤Fintype.card m := by
      by_contra h
      have hcase : Fintype.card m=0 ∨ Fintype.card m=1 := by omega
      rcases hcase with hm|hm <;> simp only [hm,Nat.mul_zero,Nat.mul_one] at hlo hhi <;> omega
    let M := genericAffineSquare K n m
    let P := genericAffineRows K n m
    let O := observabilityMatrix M P (q+1)
    obtain ⟨r,Bv,a,hV,hVL,_,_⟩ := polynomial_kernel_has_minimal_basis O
    let alpha := List.ofFn a
    have hAlpha : HasMinimalKernelDegrees O alpha := ⟨r,Bv,a,hV,hVL,List.Perm.refl _⟩
    obtain ⟨hAlen,hAsum⟩ := generic_observability_kernel_degree_budget (K:=K) (q+1) hlo alpha hAlpha
    let G := P*M^(q+1)*polynomialKernelBasisMatrix O Bv
    obtain ⟨s,Bt,b,hT,hTL,_,_⟩ := polynomial_kernel_has_minimal_basis G.transpose
    let beta := List.ofFn b
    have hBeta : HasMinimalKernelDegrees G.transpose beta := ⟨s,Bt,b,hT,hTL,List.Perm.refl _⟩
    obtain ⟨hBlen,hBsum⟩ := generic_terminal_kernel_degree_budget
      (K:=K) (q+1) hm hlo hhi Bv a hV hVL beta hBeta
    have haLen : alpha.length=r := List.length_ofFn
    have haSum : alpha.sum=∑ i, a i := List.sum_ofFn
    have hlen : alpha.length+beta.length=Fintype.card m := by
      simp only [Fintype.card_fin] at hBlen
      omega
    have hn : Fintype.card n=(q+1)*Fintype.card m+alpha.length := by omega
    have hb : beta.sum=alpha.sum+(q+2)*alpha.length := by
      simpa only [haSum,haLen,Fintype.card_fin] using hBsum
    obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse (K:=K) (q+1) hlo
    let xs := (degreeConvolution alpha beta).map (fun e => e+q)
    have hmin : HasMinimalKernelDegrees (glEquationMatrix M P) xs := by
      apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
      intro d
      rw [generic_observability_gl_kernel_hilbert_of_bases q hlo.le hhi.le
        Bv Bt R hR a b hV hT hVL hTL d]
      simpa only [xs,degreeConvolution,List.map_flatMap,List.map_map,Function.comp_def,
        show ∀ x y : ℕ, x+y+1+q=x+y+q+1 by omega] using
        sum_pairs_of_permuted_degrees a b alpha beta (List.Perm.refl _) (List.Perm.refl _)
          (fun x y => d+1-(x+y+q+1))
    have hdim : (xs.map (fun e => 2*e+1)).sum=
        Fintype.card n*(Fintype.card n+Fintype.card m) :=
      observability_gl_dimension_budget _ _ q alpha beta hlen hn hAsum hb
    have hcanon : HasKroneckerDecomposition (glKirillovMatrix M P) xs := by
      apply glKirillovMatrix_kronecker M P xs (genericAffineSquare_degree K n m)
        (genericAffineRows_degree K n m) hmin
      rw [hdim]
      simp only [SLInput,Fintype.card_sum,Fintype.card_prod]
      ring
    refine ⟨xs,?_,?_,hmin,hcanon⟩
    · change (List.map (fun e => e+q) (degreeConvolution alpha beta)).length=_
      rw [List.length_map,convolution_list_length]
      have hstep : (q+1+1)*Fintype.card m=(q+1)*Fintype.card m+Fintype.card m := by ring
      have hA : alpha.length=Fintype.card n-(q+1)*Fintype.card m := by omega
      have hB : beta.length=(q+1+1)*Fintype.card m-Fintype.card n := by omega
      rw [hA,hB]
    · rw [nat_list_affine_sum] at hdim
      simpa only [one_mul] using hdim

end FD56
