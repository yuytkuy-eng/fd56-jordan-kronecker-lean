/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.KernelDimension

/-! Constant invertible changes of coordinates preserve bounded kernel dimensions. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K a b : Type*} [Field K] [Fintype a] [Fintype b]
  [DecidableEq b]

def constantBoundedMul (V : Matrix b b K) (d : ℕ) :
    (b → BoundedPoly K d) →ₗ[K] (b → BoundedPoly K d) where
  toFun v i := boundedPolyOf ((V.map Polynomial.C *ᵥ (fun j => (v j).val)) i) (by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    exact (Polynomial.natDegree_mul_le).trans (by simpa using boundedPoly_degree d (v j)))
  map_add' v w := by
    funext i
    apply Subtype.ext
    exact congrFun (Matrix.mulVec_add (V.map Polynomial.C)
      (fun j => (v j).val) (fun j => (w j).val)) i
  map_smul' s v := by
    funext i
    apply Subtype.ext
    exact congrFun (Matrix.mulVec_smul (V.map Polynomial.C) s
      (fun j => (v j).val)) i

def constantKernelMap (A B : Matrix a b K[X]) (U : Matrix a a K)
    (V : Matrix b b K) (h : A * V.map Polynomial.C = U.map Polynomial.C * B)
    (d : ℕ) : polynomialKernelAtDegree B d →ₗ[K] polynomialKernelAtDegree A d where
  toFun v := ⟨constantBoundedMul V d v.val, by
    change A *ᵥ (V.map Polynomial.C *ᵥ (fun j => (v.val j).val)) = 0
    have hv : B *ᵥ (fun j => (v.val j).val) = 0 := v.property
    rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]⟩
  map_add' v w := by
    apply Subtype.ext
    exact (constantBoundedMul V d).map_add v.val w.val
  map_smul' s v := by
    apply Subtype.ext
    exact (constantBoundedMul V d).map_smul s v.val

def constantKernelEquiv (A B : Matrix a b K[X])
    (U U' : Matrix a a K) (V V' : Matrix b b K)
    (h : A * V.map Polynomial.C = U.map Polynomial.C * B)
    (h' : B * V'.map Polynomial.C = U'.map Polynomial.C * A)
    (hVV' : V * V' = 1) (hV'V : V' * V = 1) (d : ℕ) :
    polynomialKernelAtDegree B d ≃ₗ[K] polynomialKernelAtDegree A d where
  toLinearMap := constantKernelMap A B U V h d
  invFun := constantKernelMap B A U' V' h' d
  left_inv v := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    change (V'.map Polynomial.C *ᵥ (V.map Polynomial.C *ᵥ
      (fun j => (v.val j).val))) i = _
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hV'V, Matrix.map_one,
      Matrix.one_mulVec] <;> simp
  right_inv v := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    change (V.map Polynomial.C *ᵥ (V'.map Polynomial.C *ᵥ
      (fun j => (v.val j).val))) i = _
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hVV', Matrix.map_one,
      Matrix.one_mulVec] <;> simp

theorem constant_equivalence_kernel_hilbert (A B : Matrix a b K[X])
    (U U' : Matrix a a K) (V V' : Matrix b b K)
    (h : A * V.map Polynomial.C = U.map Polynomial.C * B)
    (h' : B * V'.map Polynomial.C = U'.map Polynomial.C * A)
    (hVV' : V * V' = 1) (hV'V : V' * V = 1) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree B d) =
      Module.finrank K (polynomialKernelAtDegree A d) :=
  (constantKernelEquiv A B U U' V V' h h' hVV' hV'V d).finrank_eq

end FD56
