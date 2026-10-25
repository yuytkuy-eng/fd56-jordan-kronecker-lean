/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.AffineKernelCoefficientGap

/-! Polynomial kernel coefficients are jointly isotropic for both skew affine forms. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K b : Type*} [Field K] [Fintype b]

theorem skew_vector_pairing_swap (A : Matrix b b K) (hA : A.transpose = -A)
    (x y : b → K) : x ⬝ᵥ (A *ᵥ y) = -(y ⬝ᵥ (A *ᵥ x)) := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, Matrix.neg_mulVec,
    neg_dotProduct, dotProduct_comm]

theorem affine_kernel_coefficient_initial (A B : Matrix b b K) (v : b → K[X])
    (hv : affineMatrixPencil A B *ᵥ v = 0) :
    A *ᵥ (fun i => (v i).coeff 0) = 0 := by
  funext i
  have h := congrArg (fun z : b → K[X] => (z i).coeff 0) hv
  dsimp only at h
  simpa only [affineMatrixPencil_mulVec_coeff_zero, Pi.zero_apply, Polynomial.coeff_zero] using h

theorem affine_kernel_coefficient_recurrence (A B : Matrix b b K) (v : b → K[X])
    (hv : affineMatrixPencil A B *ᵥ v = 0) (k : ℕ) :
    A *ᵥ (fun i => (v i).coeff (k + 1)) + B *ᵥ (fun i => (v i).coeff k) = 0 := by
  funext i
  have h := congrArg (fun z : b → K[X] => (z i).coeff (k + 1)) hv
  dsimp only at h
  simpa only [affineMatrixPencil_mulVec_coeff_succ, Pi.zero_apply, Pi.add_apply,
    Polynomial.coeff_zero] using h

theorem affine_kernel_coefficients_isotropic_constant (A B : Matrix b b K)
    (hA : A.transpose = -A) (hB : B.transpose = -B) (u v : b → K[X])
    (hu : affineMatrixPencil A B *ᵥ u = 0) (hv : affineMatrixPencil A B *ᵥ v = 0)
    (k l : ℕ) :
    (fun i => (u i).coeff k) ⬝ᵥ (A *ᵥ fun i => (v i).coeff l) = 0 := by
  induction k generalizing l with
  | zero =>
    rw [skew_vector_pairing_swap A hA, affine_kernel_coefficient_initial A B u hu,
      dotProduct_zero, neg_zero]
  | succ k ih =>
    have hu' := eq_neg_of_add_eq_zero_left (affine_kernel_coefficient_recurrence A B u hu k)
    have hv' := eq_neg_of_add_eq_zero_right (affine_kernel_coefficient_recurrence A B v hv l)
    rw [skew_vector_pairing_swap A hA, hu', dotProduct_neg, neg_neg,
      skew_vector_pairing_swap B hB, hv', dotProduct_neg, neg_neg]
    exact ih (l + 1)

theorem affine_kernel_coefficients_isotropic_linear (A B : Matrix b b K)
    (hA : A.transpose = -A) (hB : B.transpose = -B) (u v : b → K[X])
    (hu : affineMatrixPencil A B *ᵥ u = 0) (hv : affineMatrixPencil A B *ᵥ v = 0)
    (k l : ℕ) :
    (fun i => (u i).coeff k) ⬝ᵥ (B *ᵥ fun i => (v i).coeff l) = 0 := by
  have hv' := eq_neg_of_add_eq_zero_right (affine_kernel_coefficient_recurrence A B v hv l)
  rw [hv', dotProduct_neg, affine_kernel_coefficients_isotropic_constant A B hA hB u v hu hv,
    neg_zero]

theorem kernel_coefficient_matrix_isotropic {j s : Type*} (A B : Matrix b b K)
    (hA : A.transpose = -A) (hB : B.transpose = -B) (V : Matrix b j K[X])
    (hV : affineMatrixPencil A B * V = 0) (chain : s → j) (degree : s → ℕ) :
    let W : Matrix b s K := fun i c => (V i (chain c)).coeff (degree c)
    W.transpose * A * W = 0 ∧ W.transpose * B * W = 0 := by
  have hcol (l : j) : affineMatrixPencil A B *ᵥ (fun i => V i l) = 0 := by
    funext i
    exact congrFun (congrFun hV i) l
  constructor
  · rw [Matrix.mul_assoc]
    ext c d
    have h := affine_kernel_coefficients_isotropic_constant A B hA hB
      (fun i => V i (chain c)) (fun i => V i (chain d))
      (hcol (chain c)) (hcol (chain d)) (degree c) (degree d)
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
      Finset.mul_sum, Finset.sum_mul, mul_assoc, Matrix.zero_apply] using h
  · rw [Matrix.mul_assoc]
    ext c d
    have h := affine_kernel_coefficients_isotropic_linear A B hA hB
      (fun i => V i (chain c)) (fun i => V i (chain d))
      (hcol (chain c)) (hcol (chain d)) (degree c) (degree d)
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
      Finset.mul_sum, Finset.sum_mul, mul_assoc, Matrix.zero_apply] using h

theorem uniform_kernel_coefficient_matrix_isotropic {j : Type*} (A B : Matrix b b K)
    (hA : A.transpose = -A) (hB : B.transpose = -B) (V : Matrix b j K[X])
    (hV : affineMatrixPencil A B * V = 0) (e : ℕ) :
    let W : Matrix b (Fin (e + 1) × j) K := fun i kj => (V i kj.2).coeff kj.1.val
    W.transpose * A * W = 0 ∧ W.transpose * B * W = 0 :=
  kernel_coefficient_matrix_isotropic (s := Fin (e + 1) × j) A B hA hB V hV
    Prod.snd (fun kj => kj.1.val)

end FD56
