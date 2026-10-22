/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ScalarBlockObstruction
import FD56.Hilbert.RectangularBlocks

/-! A repeated block matrix has a product of identical bounded kernels. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K ι a b : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Fintype b]

def repeatedBlockKernelEquiv (G : Matrix a b K[X]) (d : ℕ) :
    polynomialKernelAtDegree (repeatedBlockMatrix ι G) d ≃ₗ[K]
      (ι → polynomialKernelAtDegree G d) where
  toFun v i := ⟨fun j => v.val (i, j), by
    funext x
    have h := congrFun v.property (i, x)
    simpa only [boundedKernelMap, LinearMap.coe_mk, AddHom.coe_mk,
      repeatedBlockMatrix_mulVec] using h⟩
  invFun v := ⟨fun ij => (v ij.1).val ij.2, by
    change repeatedBlockMatrix ι G *ᵥ (fun ij => ((v ij.1).val ij.2).val) = 0
    funext ⟨i, x⟩
    rw [repeatedBlockMatrix_mulVec]
    exact congrFun (v i).property x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem repeatedBlockMatrix_kernel_hilbert (G : Matrix a b K[X]) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (repeatedBlockMatrix ι G) d) =
      Fintype.card ι * Module.finrank K (polynomialKernelAtDegree G d) := by
  classical
  letI : Module.Finite K (polynomialKernelAtDegree G d) :=
    Module.Finite.of_injective (polynomialKernelAtDegree G d).subtype Subtype.val_injective
  letI : Module.Free K (polynomialKernelAtDegree G d) :=
    Module.Free.of_basis (Basis.ofVectorSpace K (polynomialKernelAtDegree G d))
  rw [(repeatedBlockKernelEquiv G d).finrank_eq, Module.finrank_pi_fintype]
  simp

end FD56
