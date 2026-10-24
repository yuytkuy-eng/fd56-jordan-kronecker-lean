/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ObservabilityBetaKernel
import Mathlib.Data.Matrix.Block

/-! Vanishing bounded auxiliary relations are preserved by diagonal block repetition. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K m n t : Type*} [Field K] [Fintype m] [Fintype n] [Fintype t]
  [DecidableEq m] [DecidableEq n] [DecidableEq t]

theorem observability_block_product (M : t → Matrix n n K[X])
    (P : t → Matrix m n K[X]) (q : ℕ) :
    blockDiagonal P * (blockDiagonal M)^q = blockDiagonal (fun k => P k * (M k)^q) := by
  rw [← blockDiagonal_pow,← blockDiagonal_mul]
  rfl

theorem observability_beta_block_relation (M : t → Matrix n n K[X])
    (P : t → Matrix m n K[X]) (q d : ℕ)
    (z : boundedObservabilityBetaKernel q (blockDiagonal M) (blockDiagonal P) d) (k : t) :
    (P k*(M k)^q).transpose *ᵥ (fun i => (z.val.1 (i,k)).val) =
      (observabilityMatrix (M k) (P k) q).transpose *ᵥ
        (fun i => (z.val.2 (i.1,(i.2,k))).val) := by
  funext j
  have hh := congrFun (boundedObservabilityBetaKernel_relation q
    (blockDiagonal M) (blockDiagonal P) d z) (j,k)
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,observabilityMatrix,
    observability_block_product,Matrix.blockDiagonal_apply,Fintype.sum_prod_type] at hh ⊢
  simpa only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true] using hh

theorem observability_beta_blocks_eq_bot (M : t → Matrix n n K[X])
    (P : t → Matrix m n K[X]) (q d : ℕ)
    (hz : ∀ k, boundedObservabilityBetaKernel q (M k) (P k) d = ⊥) :
    boundedObservabilityBetaKernel q (blockDiagonal M) (blockDiagonal P) d = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro z h
  let w : boundedObservabilityBetaKernel q (blockDiagonal M) (blockDiagonal P) d := ⟨z,h⟩
  have he (k : t) : (fun i => z.1 (i,k),fun i : Fin q × m => z.2 (i.1,(i.2,k))) = 0 := by
    apply (Submodule.eq_bot_iff _).mp (hz k)
    change (P k*(M k)^q).transpose *ᵥ (fun i => (z.1 (i,k)).val) -
      (observabilityMatrix (M k) (P k) q).transpose *ᵥ
        (fun i => (z.2 (i.1,(i.2,k))).val) = 0
    exact sub_eq_zero.mpr (observability_beta_block_relation M P q d w k)
  apply Prod.ext
  · funext i
    exact congrFun (congrArg Prod.fst (he i.2)) i.1
  · funext i
    exact congrFun (congrArg Prod.snd (he i.2.2)) (i.1,i.2.1)

end FD56
