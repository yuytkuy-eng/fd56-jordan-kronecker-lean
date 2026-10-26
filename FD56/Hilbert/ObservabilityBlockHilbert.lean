/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ObservabilityBetaBlocks
import FD56.Hilbert.Coefficients

/-! Bounded kernels of block observability matrices split into their actual block kernels. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K m n t : Type*} [Field K] [Fintype m] [Fintype n] [Fintype t]
  [DecidableEq m] [DecidableEq n] [DecidableEq t]

theorem observability_block_mulVec (M : t → Matrix n n K[X]) (P : t → Matrix m n K[X])
    (q : ℕ) (v : n × t → K[X]) (i : Fin q) (j : m) (k : t) :
    (observabilityMatrix (blockDiagonal M) (blockDiagonal P) q *ᵥ v) (i,(j,k)) =
      (observabilityMatrix (M k) (P k) q *ᵥ (fun x => v (x,k))) (i,j) := by
  simp only [Matrix.mulVec,dotProduct,observabilityMatrix,observability_block_product,
    Matrix.blockDiagonal_apply,Fintype.sum_prod_type,ite_mul,zero_mul,
    Finset.sum_ite_eq,Finset.mem_univ,if_true]

def observabilityBlockKernelEquiv (M : t → Matrix n n K[X]) (P : t → Matrix m n K[X])
    (q d : ℕ) :
    polynomialKernelAtDegree (observabilityMatrix (blockDiagonal M) (blockDiagonal P) q) d ≃ₗ[K]
      ∀ k, polynomialKernelAtDegree (observabilityMatrix (M k) (P k) q) d where
  toFun v k := ⟨fun j => v.val (j,k),by
    funext ij
    have hh := congrFun v.property (ij.1,(ij.2,k))
    change (observabilityMatrix (blockDiagonal M) (blockDiagonal P) q *ᵥ
      (fun j => (v.val j).val)) (ij.1,(ij.2,k)) = 0 at hh
    rw [observability_block_mulVec] at hh
    exact hh⟩
  invFun v := ⟨fun jk => (v jk.2).val jk.1,by
    change observabilityMatrix (blockDiagonal M) (blockDiagonal P) q *ᵥ
      (fun jk => ((v jk.2).val jk.1).val) = 0
    funext ij
    rw [observability_block_mulVec]
    exact congrFun (v ij.2.2).property (ij.1,ij.2.1)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem observability_blocks_kernel_finrank (M : t → Matrix n n K[X])
    (P : t → Matrix m n K[X]) (q d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree
      (observabilityMatrix (blockDiagonal M) (blockDiagonal P) q) d) =
      ∑ k, Module.finrank K (polynomialKernelAtDegree (observabilityMatrix (M k) (P k) q) d) := by
  letI (k : t) : Module.Finite K (polynomialKernelAtDegree (observabilityMatrix (M k) (P k) q) d) :=
    Module.Finite.of_injective (polynomialKernelAtDegree _ d).subtype Subtype.val_injective
  letI (k : t) : Module.Free K (polynomialKernelAtDegree (observabilityMatrix (M k) (P k) q) d) :=
    Module.Free.of_basis (Basis.ofVectorSpace K
      (polynomialKernelAtDegree (observabilityMatrix (M k) (P k) q) d))
  rw [(observabilityBlockKernelEquiv M P q d).finrank_eq,Module.finrank_pi_fintype]

theorem blockDiagonal_degreeBound_one (M : t → Matrix m n K[X])
    (hM : ∀ k, DegreeBound (M k) 1) : DegreeBound (blockDiagonal M) 1 := by
  intro i j
  rw [Matrix.blockDiagonal_apply]
  split_ifs
  · exact hM i.2 i.1 j.1
  · simp

end FD56
