/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.Tall
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! When the rectangular pencil is injective, its transpose kernel
parametrizes each translation row of the full GL stabilizer. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

def glRowKernelEquiv (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hP : Function.Injective P.mulVec) (d : ℕ) :
    polynomialKernelAtDegree (glEquationMatrix M P) d ≃ₗ[K]
      (n → polynomialKernelAtDegree P.transpose d) where
  toFun v i := ⟨fun j => v.val (.inr (i, j)), by
    have hh := ((gl_kernel_equations_of_injective M P hP _).mp v.property).2
    funext k
    have he := congrArg (fun A : Matrix n n K[X] => A i k) hh
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_comm] using he⟩
  invFun U := ⟨Sum.elim (fun _ => 0) (fun ij => (U ij.1).val ij.2), by
    apply (gl_kernel_equations_of_injective M P hP _).mpr
    constructor
    · rfl
    · funext i k
      have hh : P.transpose *ᵥ (fun j => ((U i).val j).val) = 0 := (U i).property
      have he := congrFun hh k
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_comm] using he⟩
  left_inv v := by
    apply Subtype.ext
    funext ij
    rcases ij with ij | ij
    · apply Subtype.ext
      have hh := ((gl_kernel_equations_of_injective M P hP _).mp v.property).1
      exact (congrArg (fun A : Matrix n n K[X] => A ij.1 ij.2) hh).symm
    · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem gl_kernel_hilbert_of_injective (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hP : Function.Injective P.mulVec) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d) =
      Fintype.card n * Module.finrank K (polynomialKernelAtDegree P.transpose d) := by
  classical
  letI : Module.Finite K (polynomialKernelAtDegree P.transpose d) :=
    Module.Finite.of_injective (polynomialKernelAtDegree P.transpose d).subtype
      Subtype.val_injective
  letI : Module.Free K (polynomialKernelAtDegree P.transpose d) :=
    Module.Free.of_basis (Basis.ofVectorSpace K (polynomialKernelAtDegree P.transpose d))
  rw [(glRowKernelEquiv M P hP d).finrank_eq, Module.finrank_pi_fintype]
  simp

end FD56
