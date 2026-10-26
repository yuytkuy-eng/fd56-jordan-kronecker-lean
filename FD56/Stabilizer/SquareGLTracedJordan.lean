/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.SquareGLTracedPoles
import FD56.Stabilizer.SquareGLDiagonalJordan
import FD56.Stabilizer.SquareGLNormalization

/-! The actual diagonal square GL Jordan congruence identifies the traceless
subspace with the sum-zero hyperplane in the first coordinates of the large blocks. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem squareGL_diagonal_jordan_trace_decomposition (lam : n → K) (hlam : Function.Injective lam)
    (A B : Matrix n n K) (j : n → n) (hj : ∀ i, i≠j i)
    (hres : ∀ i, A (j i) i+lam i*B (j i) i≠0) :
    ∃ G : Matrix (SLInput n n) (squareGLJordanIndex j) K,
    ∃ H : Matrix (squareGLJordanIndex j) (SLInput n n) K,
      G*H=1 ∧ H*G=1 ∧
      (G.map C).transpose * glKirillovMatrix (affineMatrixPencil A B)
          (Matrix.diagonal (fun i => X-C (lam i))) * G.map C = squareGLJordanTarget lam j ∧
      (∀ v : squareGLJordanIndex j → K,
        Matrix.trace (matrixPairEquiv K K n n (G*ᵥv)).1 = ∑ i, v ⟨i,.inl (.inl 0)⟩) := by
  letI : LinearOrder (n × n) :=
    LinearOrder.lift' (Fintype.equivFin (n × n)) (Fintype.equivFin (n × n)).injective
  let w := fun i k => -(A k i+lam i*B k i)
  let U := fun i => starJordanConstantChange i (j i) (hj i) (w i)
  have hlocal (i : n) := starJordanConstantChange_certificate i (j i) (hj i) (w i)
    (neg_ne_zero.mpr (hres i)) (lam i)
  choose V hUV hVU hlocalCong using hlocal
  let e := squareGLSigmaIndex n
  let P := (Matrix.blockDiagonal' U).submatrix e id
  let Q := (Matrix.blockDiagonal' V).submatrix id e
  let F := fun i => pairedCoupling ((starCoupling i (w i)).map C) (X-C (lam i))
  have hPQ : P*Q=1 := by
    change (Matrix.blockDiagonal' U).submatrix e (Equiv.refl _) *
      (Matrix.blockDiagonal' V).submatrix (Equiv.refl _) e = 1
    rw [Matrix.submatrix_mul_equiv,← Matrix.blockDiagonal'_mul]
    rw [show (fun k => U k*V k) = (1 : ∀ _ : n, Matrix (n ⊕ n) (n ⊕ n) K)
      from funext hUV,Matrix.blockDiagonal'_one]
    exact Matrix.submatrix_one_equiv e
  have hQP : Q*P=1 := by
    dsimp [P,Q]
    rw [Matrix.submatrix_mul_equiv,← Matrix.blockDiagonal'_mul]
    rw [show (fun k => V k*U k) =
      (1 : ∀ i : n, Matrix ((Fin 2 ⊕ Fin 2) ⊕ ((Fin 1 ⊕ Fin 1) × {k : n // k≠i ∧ k≠j i}))
        ((Fin 2 ⊕ Fin 2) ⊕ ((Fin 1 ⊕ Fin 1) × {k : n // k≠i ∧ k≠j i})) K)
      from funext hVU,Matrix.blockDiagonal'_one,Matrix.submatrix_id_id]
  have hglobal : (P.map C).transpose * Matrix.blockDiagonal F * P.map C =
      squareGLJordanTarget lam j := by
    change ((Matrix.blockDiagonal' U).map C).transpose.submatrix id e *
      (Matrix.blockDiagonal' F).submatrix e e *
      ((Matrix.blockDiagonal' U).map C).submatrix e id = _
    rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,Matrix.submatrix_id_id,
      Matrix.blockDiagonal'_map _ _ (map_zero C),Matrix.blockDiagonal'_transpose,
      ← Matrix.blockDiagonal'_mul,← Matrix.blockDiagonal'_mul]
    exact congrArg Matrix.blockDiagonal' (funext hlocalCong)
  have htrace (v : squareGLJordanIndex j → K) :
      ∑ i, (P*ᵥv) (.inl i,i) = ∑ i, v ⟨i,.inl (.inl 0)⟩ := by
    apply Finset.sum_congr rfl
    intro i _
    change (Matrix.blockDiagonal' U*ᵥv) ⟨i,.inl i⟩ = _
    have he : (Matrix.blockDiagonal' U*ᵥv) ⟨i,.inl i⟩ =
        (U i*ᵥfun x => v ⟨i,x⟩) (.inl i) := by
      simp only [Matrix.mulVec,dotProduct,Fintype.sum_sigma]
      rw [Finset.sum_eq_single i]
      · simp only [Matrix.blockDiagonal'_apply_eq]
      · intro k _ hki
        simp [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hki)]
      · simp
    rw [he]
    exact starJordanConstantChange_pivot i (j i) (hj i) (w i) _
  let G₀ := squareGLPoleConstantChange lam A B
  obtain ⟨H₀,hGH₀,hHG₀,hcong₀⟩ := squareGLPoleConstantChange_certificate lam hlam A B
  refine ⟨G₀*P,Q*H₀,?_,?_,?_,?_⟩
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc P,hPQ,Matrix.one_mul,hGH₀]
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc H₀,hHG₀,Matrix.one_mul,hQP]
  · rw [Matrix.map_mul,Matrix.transpose_mul]
    calc
      _ = (P.map C).transpose * ((G₀.map C).transpose *
          glKirillovMatrix (affineMatrixPencil A B) (Matrix.diagonal (fun i => X-C (lam i))) * G₀.map C) * P.map C := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hcong₀]; exact hglobal
  · intro v
    rw [← Matrix.mulVec_mulVec,squareGLPoleConstantChange_trace]
    exact htrace v

theorem squareGL_normalized_jordan_trace_decomposition (A B P₀ P₁ V S T : Matrix n n K)
    (hST : S*T=1) (hTS : T*S=1) (hP₁V : P₁*V=1) (hVP₁ : V*P₁=1)
    (lam : n → K) (hlam : Function.Injective lam)
    (hdiag : (-V*P₀)*S=S*Matrix.diagonal lam)
    (j : n → n) (hj : ∀ i, i≠j i)
    (hres : ∀ i, (T*A*S) (j i) i+lam i*(T*B*S) (j i) i≠0) :
    ∃ G : Matrix (SLInput n n) (squareGLJordanIndex j) K,
    ∃ H : Matrix (squareGLJordanIndex j) (SLInput n n) K,
      G*H=1 ∧ H*G=1 ∧
      (G.map C).transpose * glKirillovMatrix (affineMatrixPencil A B)
          (affineMatrixPencil P₀ P₁) * G.map C = squareGLJordanTarget lam j ∧
      (∀ v : squareGLJordanIndex j → K,
        Matrix.trace (matrixPairEquiv K K n n (G*ᵥv)).1 = ∑ i, v ⟨i,.inl (.inl 0)⟩) := by
  obtain ⟨hWZ,hZW,hrow⟩ :=
    squareGL_eigenbasis_row_normalization P₀ P₁ V S T hST hTS hP₁V hVP₁ lam hdiag
  let G₀ := glSquareBasisChange S T (T*V)
  let H₀ := glSquareBasisChange T S (P₁*S)
  have hGH₀ : G₀*H₀=1 := glSquareBasisChange_inverse S T (T*V) (P₁*S) hST hZW
  have hHG₀ : H₀*G₀=1 := glSquareBasisChange_inverse T S (P₁*S) (T*V) hTS hWZ
  have hTS' : T.map C*S.map C=(1 : Matrix n n K[X]) := by
    rw [← Matrix.map_mul,hTS,Matrix.map_one _ (map_zero C) (map_one C)]
  have hcong₀ : (G₀.map C).transpose * glKirillovMatrix (affineMatrixPencil A B) (affineMatrixPencil P₀ P₁) *
      G₀.map C = glKirillovMatrix (affineMatrixPencil (T*A*S) (T*B*S))
        (Matrix.diagonal (fun i => X-C (lam i))) := by
    rw [glSquareBasisChange_map,glSquareBasisChange_congruence _ _ _ _ _ hTS',
      affineMatrixPencil_constant_mul,affineMatrixPencil_constant_mul,hrow]
  obtain ⟨G₁,H₁,hGH₁,hHG₁,hcong₁,htrace₁⟩ :=
    squareGL_diagonal_jordan_trace_decomposition lam hlam (T*A*S) (T*B*S) j hj hres
  refine ⟨G₀*G₁,H₁*H₀,?_,?_,?_,?_⟩
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc G₁,hGH₁,Matrix.one_mul,hGH₀]
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc H₀,hHG₀,Matrix.one_mul,hHG₁]
  · rw [Matrix.map_mul,Matrix.transpose_mul]
    calc
      _ = (G₁.map C).transpose * ((G₀.map C).transpose *
          glKirillovMatrix (affineMatrixPencil A B) (affineMatrixPencil P₀ P₁) * G₀.map C) * G₁.map C := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hcong₀,hcong₁]
  · intro v
    rw [← Matrix.mulVec_mulVec,glSquareBasisChange_trace _ _ _ hTS,htrace₁]

end FD56
