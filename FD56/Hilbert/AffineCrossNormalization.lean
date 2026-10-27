/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SimpleRegularPoles
import FD56.LinearAlgebra.AlternatingCongruence
import FD56.Stabilizer.SquareGLNormalization

/-! Constant normalization of an alternating pencil with a common isotropic half-space. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

def alternatingCrossPencil (A B P₀ P₁ : Matrix n n K) : Matrix (n ⊕ n) (n ⊕ n) K[X] :=
  Matrix.fromBlocks (affineMatrixPencil A B) (affineMatrixPencil P₀ P₁)
    (-(affineMatrixPencil P₀ P₁).transpose) 0

omit [DecidableEq n] in
theorem alternatingCrossPencil_basis_change (A B P₀ P₁ E F : Matrix n n K) :
    let Q := Matrix.fromBlocks E 0 0 F
    (Q.map C).transpose * alternatingCrossPencil A B P₀ P₁ * Q.map C =
      alternatingCrossPencil (E.transpose*A*E) (E.transpose*B*E)
        (E.transpose*P₀*F) (E.transpose*P₁*F) := by
  intro Q
  have hp : (F.map C).transpose * (affineMatrixPencil P₀ P₁).transpose * E.map C =
      (affineMatrixPencil (E.transpose*P₀*F) (E.transpose*P₁*F)).transpose := by
    rw [← affineMatrixPencil_constant_mul]
    simp only [Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  simp only [Q, alternatingCrossPencil, Matrix.fromBlocks_map,
    Matrix.map_zero _ (map_zero C), Matrix.fromBlocks_transpose, Matrix.transpose_zero,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_neg, Matrix.neg_mul]
  rw [hp]
  simp only [neg_zero, add_zero, ← Matrix.transpose_map, affineMatrixPencil_constant_mul]

theorem alternatingCrossPencil_eigenbasis_normalization
    (A B P₀ P₁ V S T : Matrix n n K)
    (hST : S*T=1) (hTS : T*S=1) (hP₁V : P₁*V=1) (hVP₁ : V*P₁=1)
    (lam : n → K) (hdiag : (-V*P₀)*S=S*Matrix.diagonal lam) :
    ∃ Q R : Matrix (n ⊕ n) (n ⊕ n) K,
      Q*R=1 ∧ R*Q=1 ∧
      (Q.map C).transpose * alternatingCrossPencil A B P₀ P₁ * Q.map C =
        regularPolePencil lam ((T*V)*A*(T*V).transpose) ((T*V)*B*(T*V).transpose) := by
  obtain ⟨hleft,hright,hrow⟩ := squareGL_eigenbasis_row_normalization
    P₀ P₁ V S T hST hTS hP₁V hVP₁ lam hdiag
  refine ⟨Matrix.fromBlocks (T*V).transpose 0 0 S,
    Matrix.fromBlocks (P₁*S).transpose 0 0 T, ?_, ?_, ?_⟩
  · simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      zero_add, add_zero, ← Matrix.transpose_mul, hright, hST, Matrix.transpose_one,
      Matrix.fromBlocks_one]
  · simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      zero_add, add_zero, ← Matrix.transpose_mul, hleft, hTS, Matrix.transpose_one,
      Matrix.fromBlocks_one]
  · rw [alternatingCrossPencil_basis_change]
    simp only [Matrix.transpose_transpose, alternatingCrossPencil, hrow,
      regularPolePencil, regularPoleDiagonal, Matrix.diagonal_transpose]

theorem alternatingCrossPencil_simple_jordan_of_eigenbasis
    (A B P₀ P₁ V S T : Matrix n n K)
    (hST : S*T=1) (hTS : T*S=1) (hP₁V : P₁*V=1) (hVP₁ : V*P₁=1)
    (hA : ∀ v, v ⬝ᵥ (A *ᵥ v)=0) (hB : ∀ v, v ⬝ᵥ (B *ᵥ v)=0)
    (lam : n → K) (hlam : Function.Injective lam)
    (hdiag : (-V*P₀)*S=S*Matrix.diagonal lam) :
    ∃ Q : Matrix (n ⊕ n) ((Fin 1 ⊕ Fin 1) × n) K,
    ∃ R : Matrix ((Fin 1 ⊕ Fin 1) × n) (n ⊕ n) K,
      Q*R=1 ∧ R*Q=1 ∧
      (Q.map C).transpose * alternatingCrossPencil A B P₀ P₁ * Q.map C =
        Matrix.blockDiagonal (fun i => skewJordanBlockPencil (lam i) 1) := by
  obtain ⟨Q,R,hQR,hRQ,hcong⟩ := alternatingCrossPencil_eigenbasis_normalization
    A B P₀ P₁ V S T hST hTS hP₁V hVP₁ lam hdiag
  let U := (T*V).transpose
  have hA' : ∀ v, v ⬝ᵥ (((T*V)*A*(T*V).transpose) *ᵥ v)=0 := by
    simpa only [U, Matrix.transpose_transpose] using matrix_congruence_alternating A U hA
  have hB' : ∀ v, v ⬝ᵥ (((T*V)*B*(T*V).transpose) *ᵥ v)=0 := by
    simpa only [U, Matrix.transpose_transpose] using matrix_congruence_alternating B U hB
  obtain ⟨E,F,hEF,hFE,hEFcong⟩ := simple_regular_pole_decomposition lam hlam _ _
    (alternating_matrix_transpose _ hA') (alternating_matrix_transpose _ hB')
    (alternating_matrix_diag_zero _ hA') (alternating_matrix_diag_zero _ hB')
  refine ⟨Q*E,F*R,?_,?_,?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc E, hEF, Matrix.one_mul, hQR]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc R, hRQ, Matrix.one_mul, hFE]
  · rw [Matrix.map_mul, Matrix.transpose_mul]
    calc
      _ = (E.map C).transpose * ((Q.map C).transpose * alternatingCrossPencil A B P₀ P₁ *
          Q.map C) * E.map C := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hcong,hEFcong]

end FD56
