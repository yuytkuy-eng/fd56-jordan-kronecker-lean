/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialKernelCompletion

/-! Augmented determinants factor through the terminal matrix with one common
nonzero scalar. An explicit equivalence handles arbitrary state indexing. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K a k : Type*} [Field K] [Fintype a] [Fintype k]
  [DecidableEq a] [DecidableEq k]

theorem augmented_matrix_kernel_completion_mul
    (A : Matrix a (a ⊕ k) K[X]) (R : Matrix (a ⊕ k) a K[X]) (hAR : A*R=1)
    (B : Basis k K[X] (LinearMap.ker (Matrix.toLin' A)))
    (T : Matrix k (a ⊕ k) K[X]) :
    Matrix.fromRows A T*Matrix.fromCols R (polynomialKernelBasisMatrix A B)=
      Matrix.fromBlocks 1 0 (T*R) (T*polynomialKernelBasisMatrix A B) := by
  rw [Matrix.fromRows_mul_fromCols,hAR,polynomialKernelBasisMatrix_mul]

theorem augmented_det_mul_kernel_completion_det
    (A : Matrix a (a ⊕ k) K[X]) (R : Matrix (a ⊕ k) a K[X]) (hAR : A*R=1)
    (B : Basis k K[X] (LinearMap.ker (Matrix.toLin' A)))
    (T : Matrix k (a ⊕ k) K[X]) :
    (Matrix.fromRows A T).det*(Matrix.fromCols R (polynomialKernelBasisMatrix A B)).det=
      (T*polynomialKernelBasisMatrix A B).det := by
  rw [← Matrix.det_mul,augmented_matrix_kernel_completion_mul A R hAR B T,
    Matrix.det_fromBlocks_zero₁₂,Matrix.det_one,one_mul]

theorem augmented_det_common_scalar
    (A : Matrix a (a ⊕ k) K[X]) (R : Matrix (a ⊕ k) a K[X]) (hAR : A*R=1)
    (B : Basis k K[X] (LinearMap.ker (Matrix.toLin' A))) :
    ∃ c : K, c≠0 ∧ ∀ T : Matrix k (a ⊕ k) K[X],
      (Matrix.fromRows A T).det=C c*(T*polynomialKernelBasisMatrix A B).det := by
  obtain ⟨c,hc,hdet⟩ := polynomial_kernel_completion_det_constant A R hAR B
  refine ⟨c⁻¹,inv_ne_zero hc,?_⟩
  intro T
  have h := augmented_det_mul_kernel_completion_det A R hAR B T
  rw [hdet] at h
  calc
    (Matrix.fromRows A T).det = C c⁻¹*((Matrix.fromRows A T).det*C c) := by
      rw [mul_comm (Matrix.fromRows A T).det,← mul_assoc,← Polynomial.C_mul,
        inv_mul_cancel₀ hc,Polynomial.C_1,one_mul]
    _ = _ := by rw [h]

theorem selected_augmented_minors_common_scalar {m : Type*}
    (A : Matrix a (a ⊕ k) K[X]) (R : Matrix (a ⊕ k) a K[X]) (hAR : A*R=1)
    (B : Basis k K[X] (LinearMap.ker (Matrix.toLin' A)))
    (T : Matrix m (a ⊕ k) K[X]) :
    ∃ c : K, c≠0 ∧ ∀ row : k → m,
      (Matrix.fromRows A (T.submatrix row id)).det=
        C c*((T*polynomialKernelBasisMatrix A B).submatrix row id).det := by
  obtain ⟨c,hc,h⟩ := augmented_det_common_scalar A R hAR B
  refine ⟨c,hc,?_⟩
  intro row
  simpa only [Matrix.submatrix_mul,Matrix.submatrix_id_id] using h (T.submatrix row id)

theorem augmented_det_common_scalar_equiv {b : Type*} [Fintype b] [DecidableEq b]
    (e : b ≃ a ⊕ k) (A : Matrix a b K[X]) (R : Matrix b a K[X]) (hAR : A*R=1)
    (B : Basis k K[X] (LinearMap.ker (Matrix.toLin' A))) :
    ∃ c : K, c≠0 ∧ ∀ T : Matrix k b K[X],
      ((Matrix.fromRows A T).submatrix e id).det=
        C c*(T*polynomialKernelBasisMatrix A B).det := by
  obtain ⟨L,_,_,_,_,hHJ⟩ := polynomial_kernel_basis_completion A R hAR B
  let H := Matrix.fromCols R (polynomialKernelBasisMatrix A B)
  let J := Matrix.fromRows A L
  have hunit : H.submatrix id e*J.submatrix e id=1 := by
    rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_id_id]
    exact hHJ
  have hd : (H.submatrix id e).det*(J.submatrix e id).det=1 := by
    rw [← Matrix.det_mul,hunit,Matrix.det_one]
  have hu : IsUnit (H.submatrix id e).det := isUnit_iff_dvd_one.mpr ⟨_,hd.symm⟩
  obtain ⟨c,hc,hdet⟩ := Polynomial.isUnit_iff.mp hu
  refine ⟨c⁻¹,inv_ne_zero hc.ne_zero,?_⟩
  intro T
  have hprod : Matrix.fromRows A T*H=
      Matrix.fromBlocks 1 0 (T*R) (T*polynomialKernelBasisMatrix A B) := by
    dsimp only [H]
    rw [Matrix.fromRows_mul_fromCols,hAR,polynomialKernelBasisMatrix_mul]
  have hf : ((Matrix.fromRows A T).submatrix e id).det*C c=
      (T*polynomialKernelBasisMatrix A B).det := by
    rw [hdet,← Matrix.det_mul,
      ← Matrix.submatrix_mul (Matrix.fromRows A T) H e id e Function.bijective_id,
      Matrix.det_submatrix_equiv_self,hprod,Matrix.det_fromBlocks_zero₁₂,
      Matrix.det_one,one_mul]
  calc
    ((Matrix.fromRows A T).submatrix e id).det=
        C c⁻¹*(((Matrix.fromRows A T).submatrix e id).det*C c) := by
      rw [mul_comm ((Matrix.fromRows A T).submatrix e id).det,← mul_assoc,
        ← Polynomial.C_mul,inv_mul_cancel₀ hc.ne_zero,Polynomial.C_1,one_mul]
    _ = _ := by rw [hf]

theorem selected_augmented_minors_common_scalar_equiv {b m : Type*}
    [Fintype b] [DecidableEq b]
    (e : b ≃ a ⊕ k) (A : Matrix a b K[X]) (R : Matrix b a K[X]) (hAR : A*R=1)
    (B : Basis k K[X] (LinearMap.ker (Matrix.toLin' A))) (T : Matrix m b K[X]) :
    ∃ c : K, c≠0 ∧ ∀ row : k → m,
      ((Matrix.fromRows A (T.submatrix row id)).submatrix e id).det=
        C c*((T*polynomialKernelBasisMatrix A B).submatrix row id).det := by
  obtain ⟨c,hc,h⟩ := augmented_det_common_scalar_equiv e A R hAR B
  refine ⟨c,hc,?_⟩
  intro row
  simpa only [Matrix.submatrix_mul,Matrix.submatrix_id_id] using h (T.submatrix row id)

end FD56
