/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ObservabilityBetaKernel
import FD56.Hilbert.CofactorKernelDegrees

/-! A kernel vector bounds auxiliary relations by its terminal polynomial relations. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]
  [DecidableEq n]

def observabilityBetaVectorProjection (q : ℕ) (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (v : n → K[X])
    (hv : observabilityMatrix M P q *ᵥ v = 0) (d : ℕ) :
    boundedObservabilityBetaKernel q M P d →ₗ[K]
      polynomialKernelAtDegree (fun _ : Unit => (P * M ^ q) *ᵥ v) d where
  toFun z := ⟨z.val.1, by
    have h := congrArg (fun x : n → K[X] => v ⬝ᵥ x)
      (boundedObservabilityBetaKernel_relation q M P d z)
    dsimp only at h
    rw [dotProduct_mulVec, Matrix.vecMul_transpose,
      dotProduct_mulVec, Matrix.vecMul_transpose, hv, zero_dotProduct] at h
    change (fun _ : Unit => (P * M ^ q) *ᵥ v) *ᵥ
      (fun i => (z.val.1 i).val) = 0
    funext i
    exact h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem observabilityBetaVectorProjection_injective (q : ℕ) (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (v : n → K[X])
    (hv : observabilityMatrix M P q *ᵥ v = 0)
    (hO : Function.Injective (observabilityMatrix M P q).transpose.mulVec) (d : ℕ) :
    Function.Injective (observabilityBetaVectorProjection q M P v hv d) := by
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

theorem observability_beta_finrank_le_vector_relations (q : ℕ)
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (v : n → K[X])
    (hv : observabilityMatrix M P q *ᵥ v = 0)
    (hO : Function.Injective (observabilityMatrix M P q).transpose.mulVec) (d : ℕ) :
    Module.finrank K (boundedObservabilityBetaKernel q M P d) ≤
      Module.finrank K
        (polynomialKernelAtDegree (fun _ : Unit => (P * M ^ q) *ᵥ v) d) :=
  LinearMap.finrank_le_finrank_of_injective
    (observabilityBetaVectorProjection_injective q M P v hv hO d)

theorem observability_beta_finrank_le_scaled_cofactors {N : ℕ} (q : ℕ)
    (M : Matrix n n K[X]) (P : Matrix (Fin (N + 1)) n K[X]) (v : n → K[X])
    (F : Fin (N + 1) → K[X]) (hF : (P * M ^ q) *ᵥ v = F)
    (hv : observabilityMatrix M P q *ᵥ v = 0)
    (hO : Function.Injective (observabilityMatrix M P q).transpose.mulVec)
    (Z : Matrix (Fin (N + 1)) (Fin N) K[X]) (w : Fin (N + 1) → K[X])
    (κ δ : K) (hκ : κ ≠ 0) (hδ : δ ≠ 0)
    (hcof : rectangularCofactors Z = C κ • F) (hbez : F ⬝ᵥ w = C δ)
    (e : Fin N → ℕ) (hZ : ∀ i j, (Z i j).natDegree ≤ e j)
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (Z i j).coeff (e j))))
    (d : ℕ) :
    Module.finrank K (boundedObservabilityBetaKernel q M P d) ≤
      ∑ j, (d + 1 - e j) := by
  have h := observability_beta_finrank_le_vector_relations q M P v hv hO d
  rw [hF, scaled_cofactor_row_kernel_hilbert Z F w κ δ hκ hδ hcof hbez e hZ hlead d] at h
  exact h

end FD56
