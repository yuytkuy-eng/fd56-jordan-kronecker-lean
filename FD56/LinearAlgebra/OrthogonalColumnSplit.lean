/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.ColumnComplement
import FD56.LinearAlgebra.AlternatingSchurSplit

/-! Complete a nondegenerate column family by its orthogonal complement. -/

noncomputable section
namespace FD56
open Matrix

theorem alternating_orthogonal_column_split {K n a : Type*} [Field K]
    [Fintype n] [Fintype a] [DecidableEq n] [DecidableEq a]
    (B : Matrix n n K) (Q : Matrix n a K)
    (hB : ∀ v : n → K, v ⬝ᵥ (B *ᵥ v)=0) (hdet : B.det≠0)
    (hG : (Q.transpose*B*Q).det≠0) :
    ∃ S : Matrix n (a ⊕ Fin (Fintype.card n-Fintype.card a)) K,
    ∃ T : Matrix (a ⊕ Fin (Fintype.card n-Fintype.card a)) n K,
    ∃ D : Matrix (Fin (Fintype.card n-Fintype.card a))
      (Fin (Fintype.card n-Fintype.card a)) K,
      S*T=1 ∧ T*S=1 ∧ S.submatrix id Sum.inl=Q ∧
      Q.transpose*B*S.submatrix id Sum.inr=0 ∧
      S.transpose*B*S=Matrix.fromBlocks (Q.transpose*B*Q) 0 0 D ∧
      (∀ w, w ⬝ᵥ (D *ᵥ w)=0) ∧ D.det≠0 := by
  let G := Q.transpose*B*Q
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  let L := G⁻¹*Q.transpose*B
  have hLQ : L*Q=1 := by
    change G⁻¹*Q.transpose*B*Q=1
    rw [Matrix.mul_assoc,Matrix.mul_assoc]
    simpa only [G,Matrix.mul_assoc] using Matrix.nonsing_inv_mul G hu
  obtain ⟨S,T,hST,hTS,hSQ,hLS⟩ := matrix_left_inverse_column_completion Q L hLQ
  let R := S.submatrix id Sum.inr
  let D := R.transpose*B*R
  have hGR : Q.transpose*B*R=0 := by
    have hh := congrArg (fun M => G*M) hLS
    change G*(G⁻¹*Q.transpose*B*R)=G*0 at hh
    simpa only [← Matrix.mul_assoc,Matrix.mul_nonsing_inv G hu,
      Matrix.one_mul,Matrix.mul_zero] using hh
  have hRG : R.transpose*B*Q=0 := by
    have hh := congrArg Matrix.transpose hGR
    rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose,
      alternating_matrix_transpose B hB,Matrix.transpose_zero] at hh
    have hn : -(R.transpose*B*Q)=0 := by
      simpa only [Matrix.mul_neg,Matrix.neg_mul,Matrix.mul_assoc] using hh
    exact neg_eq_zero.mp hn
  have hS : S=Matrix.fromCols Q R := by
    rw [← hSQ]
    exact (Matrix.fromCols_toCols S).symm
  have he : S.transpose*B*S=Matrix.fromBlocks G 0 0 D := by
    rw [hS,Matrix.transpose_fromCols,Matrix.fromRows_mul,Matrix.fromRows_mul_fromCols,hGR,hRG]
  refine ⟨S,T,D,hST,hTS,hSQ,hGR,he,?_,?_⟩
  · exact matrix_congruence_alternating B R hB
  · have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hdet
    have hright : (S.transpose*B*S)*(T*B⁻¹*T.transpose)=1 := by
      calc
        _ = S.transpose*B*(S*T)*B⁻¹*T.transpose := by simp only [Matrix.mul_assoc]
        _ = S.transpose*(B*B⁻¹)*T.transpose := by rw [hST]; simp only [Matrix.mul_one,Matrix.mul_assoc]
        _ = 1 := by rw [Matrix.mul_nonsing_inv B hBu,Matrix.mul_one,← Matrix.transpose_mul,hTS,Matrix.transpose_one]
    intro hz
    have hh := congrArg Matrix.det hright
    rw [he,Matrix.det_mul,Matrix.det_fromBlocks_zero₂₁,hz,mul_zero,zero_mul,Matrix.det_one] at hh
    exact zero_ne_one hh

end FD56
