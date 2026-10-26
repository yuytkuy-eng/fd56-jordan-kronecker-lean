/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GLSquareBasisChange
import FD56.Stabilizer.SquareGLDiagonalJordan

/-! Normalize an invertible-leading square row pencil by an actual constant
Kirillov congruence and assemble its regular Jordan decomposition. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem affineMatrixPencil_constant_mul (S A B T : Matrix n n K) :
    S.map C * affineMatrixPencil A B * T.map C = affineMatrixPencil (S*A*T) (S*B*T) := by
  have haff (U V : Matrix n n K) : affineMatrixPencil U V = U.map C + (X : K[X]) • V.map C := by
    funext i j
    simp [affineMatrixPencil,smul_eq_mul]
  simp only [haff,Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,← Matrix.map_mul]

theorem glSquare_constant_basis_congruence (A B P₀ P₁ S T W Z : Matrix n n K)
    (hST : S*T=1) (hTS : T*S=1) (hWZ : W*Z=1) (hZW : Z*W=1) :
    ∃ G H : Matrix (SLInput n n) (SLInput n n) K,
      G*H=1 ∧ H*G=1 ∧
      (G.map C).transpose * glKirillovMatrix (affineMatrixPencil A B) (affineMatrixPencil P₀ P₁) *
          G.map C =
        glKirillovMatrix (affineMatrixPencil (T*A*S) (T*B*S))
          (affineMatrixPencil (W*P₀*S) (W*P₁*S)) := by
  refine ⟨glSquareBasisChange S T W,glSquareBasisChange T S Z,
    glSquareBasisChange_inverse S T W Z hST hZW,
    glSquareBasisChange_inverse T S Z W hTS hWZ,?_⟩
  have hTS' : T.map C * S.map C = (1 : Matrix n n K[X]) := by
    rw [← Matrix.map_mul,hTS,Matrix.map_one _ (map_zero C) (map_one C)]
  rw [glSquareBasisChange_map,glSquareBasisChange_congruence _ _ _ _ _ hTS',
    affineMatrixPencil_constant_mul,affineMatrixPencil_constant_mul]

theorem squareGL_eigenbasis_row_normalization (P₀ P₁ V S T : Matrix n n K)
    (hST : S*T=1) (hTS : T*S=1) (hP₁V : P₁*V=1) (hVP₁ : V*P₁=1)
    (lam : n → K) (hdiag : (-V*P₀)*S=S*Matrix.diagonal lam) :
    (T*V)*(P₁*S)=1 ∧ (P₁*S)*(T*V)=1 ∧
      affineMatrixPencil ((T*V)*P₀*S) ((T*V)*P₁*S) =
        Matrix.diagonal (fun i => X-C (lam i)) := by
  have h₁ : (T*V)*P₁*S=1 := by
    rw [Matrix.mul_assoc T V P₁,hVP₁,Matrix.mul_one,hTS]
  have h₀ : (T*V)*P₀*S = -Matrix.diagonal lam := by
    have hh : -((T*V)*P₀*S) = Matrix.diagonal lam := by
      calc
        _ = T*((-V*P₀)*S) := by simp [Matrix.mul_assoc]
        _ = T*(S*Matrix.diagonal lam) := by rw [hdiag]
        _ = _ := by rw [← Matrix.mul_assoc,hTS,Matrix.one_mul]
    exact neg_eq_iff_eq_neg.mp hh
  refine ⟨?_,?_,?_⟩
  · simpa only [← Matrix.mul_assoc] using h₁
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc S T,hST,Matrix.one_mul,hP₁V]
  · rw [h₀,h₁]
    funext i j
    by_cases hij : i=j
    · subst j
      simp [affineMatrixPencil,Matrix.diagonal_apply,Matrix.one_apply]
      ring
    · simp [affineMatrixPencil,Matrix.diagonal_apply,Matrix.one_apply,hij]

theorem squareGL_normalized_jordan_decomposition (A B P₀ P₁ V S T : Matrix n n K)
    (hST : S*T=1) (hTS : T*S=1) (hP₁V : P₁*V=1) (hVP₁ : V*P₁=1)
    (lam : n → K) (hlam : Function.Injective lam)
    (hdiag : (-V*P₀)*S=S*Matrix.diagonal lam)
    (j : n → n) (hj : ∀ i, i≠j i)
    (hres : ∀ i, (T*A*S) (j i) i+lam i*(T*B*S) (j i) i≠0) :
    ∃ G : Matrix (SLInput n n) (squareGLJordanIndex j) K,
    ∃ H : Matrix (squareGLJordanIndex j) (SLInput n n) K,
      G*H=1 ∧ H*G=1 ∧
      (G.map C).transpose * glKirillovMatrix (affineMatrixPencil A B)
          (affineMatrixPencil P₀ P₁) * G.map C = squareGLJordanTarget lam j := by
  obtain ⟨hWZ,hZW,hrow⟩ :=
    squareGL_eigenbasis_row_normalization P₀ P₁ V S T hST hTS hP₁V hVP₁ lam hdiag
  obtain ⟨G₀,H₀,hGH₀,hHG₀,hcong₀⟩ := glSquare_constant_basis_congruence
    A B P₀ P₁ S T (T*V) (P₁*S) hST hTS hWZ hZW
  rw [hrow] at hcong₀
  obtain ⟨G₁,H₁,hGH₁,hHG₁,hcong₁⟩ :=
    squareGL_diagonal_jordan_decomposition lam hlam (T*A*S) (T*B*S) j hj hres
  refine ⟨G₀*G₁,H₁*H₀,?_,?_,?_⟩
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc G₁,hGH₁,Matrix.one_mul,hGH₀]
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc H₀,hHG₀,Matrix.one_mul,hHG₁]
  · rw [Matrix.map_mul,Matrix.transpose_mul]
    calc
      _ = (G₁.map C).transpose *
          ((G₀.map C).transpose * glKirillovMatrix (affineMatrixPencil A B)
            (affineMatrixPencil P₀ P₁) * G₀.map C) * G₁.map C := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hcong₀,hcong₁]

end FD56
