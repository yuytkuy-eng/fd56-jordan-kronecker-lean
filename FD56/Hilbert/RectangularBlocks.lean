/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.Bidiagonal
import FD56.Hilbert.Coefficients
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Direct sums of rectangular Kronecker pencils and their bounded kernels. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
variable {a b : ι → Type*} [∀ i, Fintype (b i)]

theorem blockDiagonal_mulVec (P : ∀ i, Matrix (a i) (b i) K[X])
    (v : (Σ i, b i) → K[X]) (i : ι) (j : a i) :
    (Matrix.blockDiagonal' P *ᵥ v) ⟨i, j⟩ = (P i *ᵥ (fun k => v ⟨i, k⟩)) j := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  rw [Fintype.sum_eq_single i]
  · simp
  · intro k hk
    apply Finset.sum_eq_zero
    intro l _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hk.symm, zero_mul]

theorem blockDiagonal_kernel_iff (P : ∀ i, Matrix (a i) (b i) K[X])
    (v : (Σ i, b i) → K[X]) :
    Matrix.blockDiagonal' P *ᵥ v = 0 ↔ ∀ i, P i *ᵥ (fun j => v ⟨i, j⟩) = 0 := by
  constructor
  · intro h i
    funext j
    rw [← blockDiagonal_mulVec]
    exact congrFun h ⟨i, j⟩
  · intro h
    funext ⟨i, j⟩
    rw [blockDiagonal_mulVec, h]
    rfl

def blockDiagonalKernelEquiv (P : ∀ i, Matrix (a i) (b i) K[X]) (d : ℕ) :
    polynomialKernelAtDegree (Matrix.blockDiagonal' P) d ≃ₗ[K]
      ∀ i, polynomialKernelAtDegree (P i) d where
  toFun v i := ⟨fun j => v.val ⟨i, j⟩, (blockDiagonal_kernel_iff P _).mp v.property i⟩
  invFun v := ⟨fun ij => (v ij.1).val ij.2,
    (blockDiagonal_kernel_iff P _).mpr (fun i => (v i).property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem blockDiagonal_kernel_hilbert (P : ∀ i, Matrix (a i) (b i) K[X]) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (Matrix.blockDiagonal' P) d) =
      ∑ i, Module.finrank K (polynomialKernelAtDegree (P i) d) := by
  classical
  letI (i : ι) : Module.Finite K (polynomialKernelAtDegree (P i) d) :=
    Module.Finite.of_injective (polynomialKernelAtDegree (P i) d).subtype Subtype.val_injective
  letI (i : ι) : Module.Free K (polynomialKernelAtDegree (P i) d) :=
    Module.Free.of_basis (Basis.ofVectorSpace K (polynomialKernelAtDegree (P i) d))
  rw [(blockDiagonalKernelEquiv P d).finrank_eq, Module.finrank_pi_fintype]

def rectangularBlockPencil (e : ι → ℕ) :
    Matrix (Σ i, Fin (e i)) (Σ i, Fin (e i + 1)) K[X] :=
  Matrix.blockDiagonal' (fun i => bidiagonalPencil (e i))

omit [Fintype ι] in
theorem rectangularBlockPencil_degree (e : ι → ℕ) :
    DegreeBound (rectangularBlockPencil (K := K) e) 1 := by
  intro ⟨i, j⟩ ⟨k, l⟩
  by_cases h : i = k
  · subst k
    simpa only [rectangularBlockPencil, Matrix.blockDiagonal'_apply_eq] using
      bidiagonalPencil_degree (K := K) (e i) j l
  · simp [rectangularBlockPencil, Matrix.blockDiagonal'_apply_ne _ _ _ h]

theorem rectangularBlockPencil_kernel_hilbert (e : ι → ℕ) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (rectangularBlockPencil (K := K) e) d) =
      ∑ i, (d + 1 - e i) := by
  rw [rectangularBlockPencil, blockDiagonal_kernel_hilbert]
  simp_rw [bidiagonal_kernel_hilbert]

theorem rectangularBlockPencil_transpose_injective (e : ι → ℕ) :
    Function.Injective (rectangularBlockPencil (K := K) e).transpose.mulVec := by
  intro v w h
  have he : Matrix.blockDiagonal' (fun i => (bidiagonalPencil (K := K) (e i)).transpose) *ᵥ v =
      Matrix.blockDiagonal' (fun i => (bidiagonalPencil (K := K) (e i)).transpose) *ᵥ w := by
    simpa only [rectangularBlockPencil, Matrix.blockDiagonal'_transpose] using h
  funext ⟨i, j⟩
  have hb : (bidiagonalPencil (K := K) (e i)).transpose *ᵥ (fun j => v ⟨i, j⟩) =
      (bidiagonalPencil (K := K) (e i)).transpose *ᵥ (fun j => w ⟨i, j⟩) := by
    funext k
    have hh := congrFun he ⟨i, k⟩
    simpa only [blockDiagonal_mulVec] using hh
  exact congrFun (bidiagonalPencil_transpose_injective (e i) hb) j

theorem matrix_mulVec_injective_submatrix_equiv {a₁ b₁ a₂ b₂ : Type*}
    [Fintype b₁] [Fintype b₂] (A : Matrix a₁ b₁ K[X])
    (er : a₂ ≃ a₁) (ec : b₂ ≃ b₁) (hA : Function.Injective A.mulVec) :
    Function.Injective (A.submatrix er ec).mulVec := by
  intro v w h
  rw [Matrix.submatrix_mulVec_equiv, Matrix.submatrix_mulVec_equiv] at h
  have he : A *ᵥ (v ∘ ec.symm) = A *ᵥ (w ∘ ec.symm) := by
    funext i
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using congrFun h (er.symm i)
  have hh := hA he
  funext j
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using congrFun hh (ec j)

theorem rectangularBlockPencil_submatrix_transpose_injective
    {a₁ b₁ : Type*} [Fintype a₁] (e : ι → ℕ)
    (er : a₁ ≃ (Σ i, Fin (e i))) (ec : b₁ ≃ (Σ i, Fin (e i + 1))) :
    Function.Injective ((rectangularBlockPencil (K := K) e).submatrix er ec).transpose.mulVec := by
  rw [Matrix.transpose_submatrix]
  exact matrix_mulVec_injective_submatrix_equiv _ ec er
    (rectangularBlockPencil_transpose_injective e)

end FD56
