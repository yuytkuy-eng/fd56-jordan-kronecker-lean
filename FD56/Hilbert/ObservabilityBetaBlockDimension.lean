/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ObservabilityBetaBlocks

/-! The bounded auxiliary kernel of a block diagonal pair splits into its components. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K m n t : Type*} [Field K] [Fintype m] [Fintype n] [Fintype t]
  [DecidableEq m] [DecidableEq n] [DecidableEq t]

def observabilityBetaBlockProjection (M : t → Matrix n n K[X])
    (P : t → Matrix m n K[X]) (q d : ℕ) :
    boundedObservabilityBetaKernel q (blockDiagonal M) (blockDiagonal P) d →ₗ[K]
      ∀ k, boundedObservabilityBetaKernel q (M k) (P k) d where
  toFun z k := ⟨(fun i => z.val.1 (i,k), fun i => z.val.2 (i.1,(i.2,k))), by
    change (P k * (M k)^q).transpose *ᵥ (fun i => (z.val.1 (i,k)).val) -
      (observabilityMatrix (M k) (P k) q).transpose *ᵥ
        (fun i => (z.val.2 (i.1,(i.2,k))).val) = 0
    exact sub_eq_zero.mpr (observability_beta_block_relation M P q d z k)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem observabilityBetaBlockProjection_injective (M : t → Matrix n n K[X])
    (P : t → Matrix m n K[X]) (q d : ℕ) :
    Function.Injective (observabilityBetaBlockProjection M P q d) := by
  intro z w h
  have hc (k : t) := congrArg Subtype.val (congrFun h k)
  apply Subtype.ext
  apply Prod.ext
  · funext i
    exact congrFun (congrArg Prod.fst (hc i.2)) i.1
  · funext i
    exact congrFun (congrArg Prod.snd (hc i.2.2)) (i.1,i.2.1)

theorem observabilityBetaBlockProjection_surjective (M : t → Matrix n n K[X])
    (P : t → Matrix m n K[X]) (q d : ℕ) :
    Function.Surjective (observabilityBetaBlockProjection M P q d) := by
  intro y
  refine ⟨⟨(fun i => (y i.2).val.1 i.1,
    fun i => (y i.2.2).val.2 (i.1,i.2.1)), ?_⟩, rfl⟩
  change (blockDiagonal P * (blockDiagonal M)^q).transpose *ᵥ
    (fun i => ((y i.2).val.1 i.1).val) -
      (observabilityMatrix (blockDiagonal M) (blockDiagonal P) q).transpose *ᵥ
        (fun i => ((y i.2.2).val.2 (i.1,i.2.1)).val) = 0
  apply sub_eq_zero.mpr
  funext j
  have h := congrFun (boundedObservabilityBetaKernel_relation q (M j.2) (P j.2) d (y j.2)) j.1
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, observabilityMatrix,
    observability_block_product, Matrix.blockDiagonal_apply, Fintype.sum_prod_type] at h ⊢
  simpa only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

def observabilityBetaBlockEquiv (M : t → Matrix n n K[X])
    (P : t → Matrix m n K[X]) (q d : ℕ) :
    boundedObservabilityBetaKernel q (blockDiagonal M) (blockDiagonal P) d ≃ₗ[K]
      ∀ k, boundedObservabilityBetaKernel q (M k) (P k) d :=
  LinearEquiv.ofBijective (observabilityBetaBlockProjection M P q d)
    ⟨observabilityBetaBlockProjection_injective M P q d,
      observabilityBetaBlockProjection_surjective M P q d⟩

theorem observability_beta_blocks_finrank (M : t → Matrix n n K[X])
    (P : t → Matrix m n K[X]) (q d : ℕ) :
    Module.finrank K (boundedObservabilityBetaKernel q (blockDiagonal M) (blockDiagonal P) d) =
      ∑ k, Module.finrank K (boundedObservabilityBetaKernel q (M k) (P k) d) := by
  letI (k : t) : Module.Finite K (boundedObservabilityBetaKernel q (M k) (P k) d) :=
    Module.Finite.of_injective (boundedObservabilityBetaKernel q (M k) (P k) d).subtype
      Subtype.val_injective
  letI (k : t) : Module.Free K (boundedObservabilityBetaKernel q (M k) (P k) d) :=
    Module.Free.of_basis (Basis.ofVectorSpace K (boundedObservabilityBetaKernel q (M k) (P k) d))
  rw [(observabilityBetaBlockEquiv M P q d).finrank_eq, Module.finrank_pi_fintype]

theorem observability_beta_blocks_finrank_le (M : t → Matrix n n K[X])
    (P : t → Matrix m n K[X]) (q d : ℕ) :
    Module.finrank K (boundedObservabilityBetaKernel q (blockDiagonal M) (blockDiagonal P) d) ≤
      ∑ k, Module.finrank K (boundedObservabilityBetaKernel q (M k) (P k) d) := by
  exact (observability_beta_blocks_finrank M P q d).le

end FD56
