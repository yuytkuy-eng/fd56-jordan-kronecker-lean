/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ObservabilityBetaVectorBound

/-! Several observability-kernel columns jointly bound the terminal relations. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K m n r : Type*} [Field K] [Fintype m] [Fintype n]
  [DecidableEq n]

def observabilityBetaMatrixProjection (q : ℕ) (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (V : Matrix n r K[X])
    (hV : observabilityMatrix M P q * V = 0) (d : ℕ) :
    boundedObservabilityBetaKernel q M P d →ₗ[K]
      polynomialKernelAtDegree ((P * M ^ q * V).transpose) d where
  toFun z := ⟨z.val.1, by
    have h := congrArg (fun x : n → K[X] => V.transpose *ᵥ x)
      (boundedObservabilityBetaKernel_relation q M P d z)
    dsimp only at h
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
      Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hV] at h
    simpa only [Matrix.transpose_zero, Matrix.zero_mulVec] using h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem observabilityBetaMatrixProjection_injective (q : ℕ) (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (V : Matrix n r K[X])
    (hV : observabilityMatrix M P q * V = 0)
    (hO : Function.Injective (observabilityMatrix M P q).transpose.mulVec) (d : ℕ) :
    Function.Injective (observabilityBetaMatrixProjection q M P V hV d) := by
  intro z w hzw
  have ht : z.val.1 = w.val.1 := congrArg Subtype.val hzw
  have hc : (observabilityMatrix M P q).transpose *ᵥ (fun i => (z.val.2 i).val) =
      (observabilityMatrix M P q).transpose *ᵥ (fun i => (w.val.2 i).val) := by
    rw [← boundedObservabilityBetaKernel_relation q M P d z,
      ← boundedObservabilityBetaKernel_relation q M P d w, ht]
  have hd := hO hc
  apply Subtype.ext
  apply Prod.ext ht
  funext i
  exact Subtype.ext (congrFun hd i)

theorem observability_beta_finrank_le_matrix_relations (q : ℕ)
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (V : Matrix n r K[X])
    (hV : observabilityMatrix M P q * V = 0)
    (hO : Function.Injective (observabilityMatrix M P q).transpose.mulVec) (d : ℕ) :
    Module.finrank K (boundedObservabilityBetaKernel q M P d) ≤
      Module.finrank K (polynomialKernelAtDegree ((P * M ^ q * V).transpose) d) :=
  LinearMap.finrank_le_finrank_of_injective
    (observabilityBetaMatrixProjection_injective q M P V hV hO d)

end FD56
