/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.WeightedCoefficients
import FD56.Hilbert.KernelGrowth

/-! Evaluation bounds growth when all coordinate degree bounds increase together. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K a b : Type*} [Field K] [Fintype b] [DecidableEq b]

def weightedKernelEvalZero (A : Matrix a b K[X]) (g : b → ℕ) :
    weightedPolynomialKernel A g →ₗ[K] (b → K) where
  toFun v j := (v.val j).val.eval 0
  map_add' _ _ := by funext j; simp
  map_smul' _ _ := by funext j; simp

theorem weightedKernelEvalZero_range_le (A : Matrix a b K[X]) (g : b → ℕ) :
    LinearMap.range (weightedKernelEvalZero A g) ≤
      LinearMap.ker (Matrix.toLin' (A.map (Polynomial.evalRingHom 0))) := by
  rintro _ ⟨v,rfl⟩
  have hv : A *ᵥ (fun j => (v.val j).val) = 0 := v.property
  have hh := congrArg (fun w : a → K[X] => fun i => (w i).eval 0) hv
  change (A.map (Polynomial.evalRingHom 0) *ᵥ (fun j => (v.val j).val.eval 0)) = 0
  simpa only [Matrix.mulVec, dotProduct, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_zero, Pi.zero_apply, Matrix.map_apply,
    Polynomial.coe_evalRingHom] using hh

omit [DecidableEq b] in
theorem weightedKernelEvalZero_const {A : Matrix a b K[X]} {g : b → ℕ}
    (v : LinearMap.ker (weightedKernelEvalZero A g)) (j : b) :
    (v.val.val j).val.coeff 0 = 0 := by
  have hh := congrFun v.property j
  change (v.val.val j).val.eval 0 = 0 at hh
  rwa [Polynomial.coeff_zero_eq_eval_zero]

def weightedKernelEvalDivX (A : Matrix a b K[X]) (g : b → ℕ) :
    LinearMap.ker (weightedKernelEvalZero A (fun j => g j+1)) →ₗ[K]
      weightedPolynomialKernel A g where
  toFun v := ⟨fun j => boundedPolyOf (v.val.val j).val.divX (by
    have hh := boundedPoly_degree (g j+1) (v.val.val j)
    rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
    omega), by
    change A *ᵥ (fun j => (v.val.val j).val.divX) = 0
    have he : (fun j => (v.val.val j).val) =
        (Polynomial.X : K[X]) • (fun j => (v.val.val j).val.divX) := by
      funext j
      have hh := Polynomial.X_mul_divX_add (v.val.val j).val
      rw [weightedKernelEvalZero_const v j] at hh
      simpa using hh.symm
    have hz : A *ᵥ (fun j => (v.val.val j).val) = 0 := v.val.property
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
theorem weightedKernelEvalDivX_injective (A : Matrix a b K[X]) (g : b → ℕ) :
    Function.Injective (weightedKernelEvalDivX A g) := by
  intro v w h
  apply Subtype.ext
  apply Subtype.ext
  funext j
  apply Subtype.ext
  have hh := congrArg (fun u : weightedPolynomialKernel A g => (u.val j).val) h
  change (v.val.val j).val.divX = (w.val.val j).val.divX at hh
  have hv := Polynomial.X_mul_divX_add (v.val.val j).val
  have hw := Polynomial.X_mul_divX_add (w.val.val j).val
  rw [weightedKernelEvalZero_const v j] at hv
  rw [weightedKernelEvalZero_const w j] at hw
  rw [hh] at hv
  exact hv.symm.trans hw

attribute [local irreducible] weightedKernelEvalDivX weightedKernelEvalZero

theorem weighted_polynomial_kernel_growth (A : Matrix a b K[X]) (g : b → ℕ) :
    Module.finrank K (weightedPolynomialKernel A (fun j => g j+1)) ≤
      Module.finrank K (weightedPolynomialKernel A g) +
        Module.finrank K (LinearMap.ker (Matrix.toLin' (A.map (Polynomial.evalRingHom 0)))) := by
  letI : Module.Finite K (weightedPolynomialKernel A g) :=
    Module.Finite.of_injective (weightedPolynomialKernel A g).subtype Subtype.val_injective
  letI : Module.Finite K (weightedPolynomialKernel A (fun j => g j+1)) :=
    Module.Finite.of_injective (weightedPolynomialKernel A (fun j => g j+1)).subtype Subtype.val_injective
  exact finrank_le_of_kernel_injection
    (V := weightedPolynomialKernel A (fun j => g j+1)) (W := b → K)
    (Z := weightedPolynomialKernel A g) (weightedKernelEvalZero A _) _
    (weightedKernelEvalZero_range_le A _) (weightedKernelEvalDivX A g)
    (weightedKernelEvalDivX_injective A g)

end FD56
