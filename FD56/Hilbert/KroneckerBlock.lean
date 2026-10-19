/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.Bidiagonal

/-! A standard alternating Kronecker block has one polynomial kernel
generator of degree m and Hilbert function max(0, d + 1 - m). -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

def kroneckerBlockPencil (m : ℕ) :
    Matrix (Fin m ⊕ Fin (m + 1)) (Fin m ⊕ Fin (m + 1)) K[X] :=
  Matrix.fromBlocks 0 (bidiagonalPencil m) (-(bidiagonalPencil m).transpose) 0

theorem kroneckerBlockPencil_kernel_iff (m : ℕ) (v : Fin m ⊕ Fin (m + 1) → K[X]) :
    kroneckerBlockPencil m *ᵥ v = 0 ↔
      (fun i => v (.inl i)) = 0 ∧ bidiagonalPencil m *ᵥ (fun j => v (.inr j)) = 0 := by
  simp only [kroneckerBlockPencil, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec,
    zero_add, add_zero, Matrix.neg_mulVec]
  constructor
  · intro h
    have hx : (bidiagonalPencil (K := K) m).transpose *ᵥ (fun i => v (.inl i)) = 0 := by
      funext j
      simpa using congrFun h (.inr j)
    refine ⟨bidiagonalPencil_transpose_injective m (hx.trans (Matrix.mulVec_zero _).symm), ?_⟩
    funext i
    exact congrFun h (.inl i)
  · rintro ⟨hx, hy⟩
    change Sum.elim _ _ = (0 : Fin m ⊕ Fin (m + 1) → K[X])
    funext i
    rcases i with i | j
    · exact congrFun hy i
    · have hh : (bidiagonalPencil (K := K) m).transpose *ᵥ (fun i => v (.inl i)) = 0 := by
        rw [hx, Matrix.mulVec_zero]
      simpa using congrArg Neg.neg (congrFun hh j)

theorem kroneckerBlockPencil_skew (m : ℕ) :
    (kroneckerBlockPencil (K := K) m).transpose = -kroneckerBlockPencil m := by
  funext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [kroneckerBlockPencil]

def kroneckerBlockKernelEquiv (m d : ℕ) :
    polynomialKernelAtDegree (kroneckerBlockPencil (K := K) m) d ≃ₗ[K]
      polynomialKernelAtDegree (bidiagonalPencil (K := K) m) d where
  toFun v := ⟨fun j => v.val (.inr j),
    ((kroneckerBlockPencil_kernel_iff m (fun i => (v.val i).val)).mp v.property).2⟩
  invFun w := ⟨Sum.elim (fun _ => 0) w.val, by
    apply (kroneckerBlockPencil_kernel_iff m _).mpr
    exact ⟨rfl, w.property⟩⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    rcases i with i | j
    · apply Subtype.ext
      have h := ((kroneckerBlockPencil_kernel_iff m (fun i => (v.val i).val)).mp v.property).1
      exact (congrFun h i).symm
    · rfl
  right_inv w := rfl
  map_add' v w := rfl
  map_smul' c v := rfl

theorem kroneckerBlock_kernel_hilbert (m d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (kroneckerBlockPencil (K := K) m) d) =
      d + 1 - m := by
  rw [(kroneckerBlockKernelEquiv m d).finrank_eq, bidiagonal_kernel_hilbert]

end FD56
