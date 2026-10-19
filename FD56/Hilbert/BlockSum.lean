/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.KroneckerBlock
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-! Bounded polynomial kernels split over block diagonal sums. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K a b c e : Type*} [Field K] [Fintype b] [Fintype e]

theorem blockSum_kernel_iff (A : Matrix a b K[X]) (B : Matrix c e K[X])
    (v : b ⊕ e → K[X]) :
    Matrix.fromBlocks A 0 0 B *ᵥ v = 0 ↔
      A *ᵥ (fun i => v (.inl i)) = 0 ∧ B *ᵥ (fun j => v (.inr j)) = 0 := by
  simp only [Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
  constructor
  · intro h
    exact ⟨funext (fun i => congrFun h (.inl i)),
      funext (fun j => congrFun h (.inr j))⟩
  · rintro ⟨hA, hB⟩
    funext i
    rcases i with i | j
    · exact congrFun hA i
    · exact congrFun hB j

def blockSumKernelEquiv (A : Matrix a b K[X]) (B : Matrix c e K[X]) (d : ℕ) :
    polynomialKernelAtDegree (Matrix.fromBlocks A 0 0 B) d ≃ₗ[K]
      polynomialKernelAtDegree A d × polynomialKernelAtDegree B d where
  toFun v :=
    (⟨fun i => v.val (.inl i), ((blockSum_kernel_iff A B _).mp v.property).1⟩,
     ⟨fun j => v.val (.inr j), ((blockSum_kernel_iff A B _).mp v.property).2⟩)
  invFun w := ⟨Sum.elim w.1.val w.2.val,
    (blockSum_kernel_iff A B _).mpr ⟨w.1.property, w.2.property⟩⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    cases i <;> rfl
  right_inv w := rfl
  map_add' v w := rfl
  map_smul' s v := rfl

theorem blockSum_kernel_hilbert (A : Matrix a b K[X]) (B : Matrix c e K[X])
    (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (Matrix.fromBlocks A 0 0 B) d) =
      Module.finrank K (polynomialKernelAtDegree A d) +
      Module.finrank K (polynomialKernelAtDegree B d) := by
  classical
  letI : Module.Free K (polynomialKernelAtDegree A d) :=
    Module.Free.of_basis (Basis.ofVectorSpace K (polynomialKernelAtDegree A d))
  letI : Module.Free K (polynomialKernelAtDegree B d) :=
    Module.Free.of_basis (Basis.ofVectorSpace K (polynomialKernelAtDegree B d))
  rw [(blockSumKernelEquiv A B d).finrank_eq]
  exact Module.finrank_prod

theorem twoKroneckerBlocks_kernel_hilbert (m n d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree
      (Matrix.fromBlocks (kroneckerBlockPencil (K := K) m) 0 0
        (kroneckerBlockPencil n)) d) = (d + 1 - m) + (d + 1 - n) := by
  rw [blockSum_kernel_hilbert, kroneckerBlock_kernel_hilbert,
    kroneckerBlock_kernel_hilbert]

theorem regular_kernel_eq_bot {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K[X]) (hA : A.det ≠ 0) (d : ℕ) :
    polynomialKernelAtDegree A d = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  have hz := Matrix.eq_zero_of_mulVec_eq_zero hA hv
  funext i
  exact Subtype.ext (congrFun hz i)

theorem regular_kernel_hilbert {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K[X]) (hA : A.det ≠ 0) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree A d) = 0 := by
  rw [regular_kernel_eq_bot A hA d]
  exact finrank_bot K (n → BoundedPoly K d)

theorem blockSum_regular_kernel_hilbert {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix a b K[X]) (R : Matrix n n K[X]) (hR : R.det ≠ 0) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (Matrix.fromBlocks A 0 0 R) d) =
      Module.finrank K (polynomialKernelAtDegree A d) := by
  rw [blockSum_kernel_hilbert, regular_kernel_hilbert R hR, add_zero]

end FD56

