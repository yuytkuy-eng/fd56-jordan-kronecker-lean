/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.KernelDimension
import Mathlib.Algebra.Polynomial.Inductions

/-! Evaluation bounds the growth of bounded polynomial kernels. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K a b : Type*} [Field K] [Fintype b] [DecidableEq b]

def kernelEvalZero (A : Matrix a b K[X]) (d : ℕ) :
    polynomialKernelAtDegree A d →ₗ[K] (b → K) where
  toFun v j := (v.val j).val.eval 0
  map_add' v w := by funext j; simp
  map_smul' c v := by funext j; simp

theorem kernelEvalZero_range_le (A : Matrix a b K[X]) (d : ℕ) :
    LinearMap.range (kernelEvalZero A d) ≤
      LinearMap.ker (Matrix.toLin' (A.map (Polynomial.evalRingHom 0))) := by
  rintro _ ⟨v, rfl⟩
  have hv : A *ᵥ (fun j => (v.val j).val) = 0 := v.property
  have hh := congrArg (fun w : a → K[X] => fun i => (w i).eval 0) hv
  change (A.map (Polynomial.evalRingHom 0) *ᵥ (fun j => (v.val j).val.eval 0)) = 0
  simpa only [Matrix.mulVec, dotProduct, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_zero, Pi.zero_apply, Matrix.map_apply,
    Polynomial.coe_evalRingHom] using hh

omit [DecidableEq b] in
theorem kernelEvalZero_const {A : Matrix a b K[X]} {d : ℕ}
    (v : LinearMap.ker (kernelEvalZero A d)) (j : b) :
    (v.val.val j).val.coeff 0 = 0 := by
  have hh := congrFun v.property j
  change (v.val.val j).val.eval 0 = 0 at hh
  rwa [Polynomial.coeff_zero_eq_eval_zero]

def kernelEvalDivX (A : Matrix a b K[X]) (d : ℕ) :
    LinearMap.ker (kernelEvalZero A (d + 1)) →ₗ[K] polynomialKernelAtDegree A d where
  toFun v := ⟨fun j => boundedPolyOf (v.val.val j).val.divX (by
    have hh := boundedPoly_degree (d + 1) (v.val.val j)
    rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
    omega), by
    change A *ᵥ (fun j => (v.val.val j).val.divX) = 0
    have he : (fun j => (v.val.val j).val) =
        (Polynomial.X : K[X]) • (fun j => (v.val.val j).val.divX) := by
      funext j
      have hh := Polynomial.X_mul_divX_add (v.val.val j).val
      rw [kernelEvalZero_const v j] at hh
      simpa using hh.symm
    have hz := v.val.property
    change A *ᵥ (fun j => (v.val.val j).val) = 0 at hz
    rw [he, Matrix.mulVec_smul] at hz
    funext i
    have hh := congrFun hz i
    change Polynomial.X * (A *ᵥ (fun j => (v.val.val j).val.divX)) i = 0 at hh
    exact (mul_eq_zero.mp hh).resolve_left (by simp)⟩
  map_add' v w := by
    apply Subtype.ext
    funext j
    apply Subtype.ext
    exact Polynomial.divX_add
  map_smul' c v := by
    apply Subtype.ext
    funext j
    apply Subtype.ext
    change (c • (v.val.val j).val).divX = c • (v.val.val j).val.divX
    simpa only [Polynomial.smul_eq_C_mul] using
      (Polynomial.divX_C_mul (a := c) (p := (v.val.val j).val))

omit [DecidableEq b] in
theorem kernelEvalDivX_injective (A : Matrix a b K[X]) (d : ℕ) :
    Function.Injective (kernelEvalDivX A d) := by
  intro v w h
  apply Subtype.ext
  apply Subtype.ext
  funext j
  apply Subtype.ext
  have hh := congrArg (fun u : polynomialKernelAtDegree A d => (u.val j).val) h
  change (v.val.val j).val.divX = (w.val.val j).val.divX at hh
  have hv := Polynomial.X_mul_divX_add (v.val.val j).val
  have hw := Polynomial.X_mul_divX_add (w.val.val j).val
  rw [kernelEvalZero_const v j] at hv
  rw [kernelEvalZero_const w j] at hw
  rw [hh] at hv
  exact hv.symm.trans hw

theorem finrank_le_of_kernel_injection {V W Z : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup Z] [Module K Z]
    [Module.Finite K V] [Module.Finite K W] [Module.Finite K Z]
    (f : V →ₗ[K] W) (S : Submodule K W) (hS : LinearMap.range f ≤ S)
    (g : LinearMap.ker f →ₗ[K] Z) (hg : Function.Injective g) :
    Module.finrank K V ≤ Module.finrank K Z + Module.finrank K S := by
  have hker := LinearMap.finrank_le_finrank_of_injective hg
  have hrange := Submodule.finrank_mono hS
  have hd := f.finrank_range_add_finrank_ker
  omega

attribute [local irreducible] kernelEvalDivX kernelEvalZero

theorem polynomial_kernel_growth (A : Matrix a b K[X]) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree A (d + 1)) ≤
      Module.finrank K (polynomialKernelAtDegree A d) +
        Module.finrank K (LinearMap.ker (Matrix.toLin' (A.map (Polynomial.evalRingHom 0)))) := by
  letI : Module.Finite K (polynomialKernelAtDegree A d) :=
    Module.Finite.of_injective (polynomialKernelAtDegree A d).subtype Subtype.val_injective
  letI : Module.Finite K (polynomialKernelAtDegree A (d + 1)) :=
    Module.Finite.of_injective (polynomialKernelAtDegree A (d + 1)).subtype Subtype.val_injective
  exact finrank_le_of_kernel_injection
    (V := polynomialKernelAtDegree A (d + 1)) (W := b → K) (Z := polynomialKernelAtDegree A d)
    (kernelEvalZero A (d + 1)) _
    (kernelEvalZero_range_le A (d + 1)) (kernelEvalDivX A d) (kernelEvalDivX_injective A d)

omit [DecidableEq b] in
theorem kernelEvalZero_zero_injective (A : Matrix a b K[X]) :
    Function.Injective (kernelEvalZero A 0) := by
  intro v w h
  apply Subtype.ext
  funext j
  apply Subtype.ext
  have hh := congrFun h j
  change (kernelEvalZero A 0 v) j = (kernelEvalZero A 0 w) j at hh
  simp only [kernelEvalZero] at hh
  change (v.val j).val.eval 0 = (w.val j).val.eval 0 at hh
  rw [← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coeff_zero_eq_eval_zero] at hh
  rw [Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero (boundedPoly_degree 0 (v.val j))),
    Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero (boundedPoly_degree 0 (w.val j))), hh]

theorem polynomial_kernel_shift_bound (A : Matrix a b K[X]) (e r : ℕ)
    (hdim : Module.finrank K (LinearMap.ker
      (Matrix.toLin' (A.map (Polynomial.evalRingHom 0)))) ≤ r)
    (hzero : ∀ d, d < e → Module.finrank K (polynomialKernelAtDegree A d) = 0)
    (d : ℕ) : Module.finrank K (polynomialKernelAtDegree A d) ≤ r * (d + 1 - e) := by
  induction d with
  | zero =>
    by_cases he : e = 0
    · have hi := LinearMap.finrank_range_of_inj (f := kernelEvalZero A 0)
        (kernelEvalZero_zero_injective A)
      have hb := Submodule.finrank_mono (kernelEvalZero_range_le A 0)
      simpa [he, hi] using hb.trans hdim
    · rw [hzero 0 (by omega)]
      exact Nat.zero_le _
  | succ d ih =>
    by_cases he : d + 1 < e
    · rw [hzero (d + 1) he]
      exact Nat.zero_le _
    · have hh := polynomial_kernel_growth A d
      have ht : d + 1 + 1 - e = (d + 1 - e) + 1 := by omega
      rw [ht, Nat.mul_add, Nat.mul_one]
      omega

end FD56
