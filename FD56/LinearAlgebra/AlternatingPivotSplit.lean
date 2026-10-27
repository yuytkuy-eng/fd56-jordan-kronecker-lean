/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.AlternatingSchurSplit

/-! A nonzero alternating pivot splits off a standard symplectic plane. -/

noncomputable section
namespace FD56
open Matrix

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem alternating_nonzero_pivot_split (B : Matrix (Fin 2 ⊕ n) (Fin 2 ⊕ n) K)
    (hB : ∀ w : Fin 2 ⊕ n → K, w ⬝ᵥ (B *ᵥ w)=0)
    (hc : B (Sum.inl 0) (Sum.inl 1) ≠ 0) :
    ∃ T U : Matrix (Fin 2 ⊕ n) (Fin 2 ⊕ n) K,
    ∃ D : Matrix n n K,
      T*U=1 ∧ U*T=1 ∧
      T.transpose*B*T=Matrix.fromBlocks (![![0,1],![-1,0]] : Matrix (Fin 2) (Fin 2) K) 0 0 D ∧
      (∀ w : n → K, w ⬝ᵥ (D *ᵥ w)=0) := by
  let c := B (Sum.inl 0) (Sum.inl 1)
  have hc' : c≠0 := hc
  have hd := alternating_matrix_diag_zero B hB
  have ht := alternating_matrix_transpose B hB
  have h10 : B (Sum.inl 1) (Sum.inl 0) = -c :=
    congrArg (fun A => A (Sum.inl 0) (Sum.inl 1)) ht
  have hA : B.toBlocks₁₁ = (![![0,c],![-c,0]] : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.toBlocks₁₁,hd,h10,c]
  have hdet : IsUnit B.toBlocks₁₁.det := by
    apply isUnit_iff_ne_zero.mpr
    rw [hA,Matrix.det_fin_two]
    simp [hc']
  obtain ⟨T,U,D,hTU,hUT,he,hD⟩ := alternating_matrix_schur_split B hB
    B.toBlocks₁₁⁻¹ (Matrix.mul_nonsing_inv _ hdet) (Matrix.nonsing_inv_mul _ hdet)
  let Q : Matrix (Fin 2) (Fin 2) K := ![![1,0],![0,c⁻¹]]
  let R : Matrix (Fin 2) (Fin 2) K := ![![1,0],![0,c]]
  have hQR : Q*R=1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Q,R,Matrix.mul_apply,Fin.sum_univ_succ,hc',Matrix.one_apply]
  have hRQ : R*Q=1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Q,R,Matrix.mul_apply,Fin.sum_univ_succ,hc',Matrix.one_apply]
  have hQA : Q.transpose*B.toBlocks₁₁*Q=![![0,1],![-1,0]] := by
    rw [hA]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Q,Matrix.mul_apply,Fin.sum_univ_succ,hc',← mul_assoc]
  let F : Matrix (Fin 2 ⊕ n) (Fin 2 ⊕ n) K := Matrix.fromBlocks Q 0 0 1
  let G : Matrix (Fin 2 ⊕ n) (Fin 2 ⊕ n) K := Matrix.fromBlocks R 0 0 1
  have hFG : F*G=1 := by simp [F,G,Matrix.fromBlocks_multiply,hQR,Matrix.fromBlocks_one]
  have hGF : G*F=1 := by simp [F,G,Matrix.fromBlocks_multiply,hRQ,Matrix.fromBlocks_one]
  refine ⟨T*F,G*U,D,?_,?_,?_,hD⟩
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc F,hFG,Matrix.one_mul,hTU]
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc U,hUT,Matrix.one_mul,hGF]
  · rw [Matrix.transpose_mul]
    calc
      _ = F.transpose*(T.transpose*B*T)*F := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [he]
        simp only [F,Matrix.fromBlocks_transpose,Matrix.transpose_zero,Matrix.transpose_one,
          Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,
          Matrix.one_mul,Matrix.mul_one,hQA]

theorem alternating_nondegenerate_pivot_split (B : Matrix (Fin 2 ⊕ n) (Fin 2 ⊕ n) K)
    (hB : ∀ w : Fin 2 ⊕ n → K, w ⬝ᵥ (B *ᵥ w)=0)
    (hc : B (Sum.inl 0) (Sum.inl 1) ≠ 0) (hdet : B.det≠0) :
    ∃ T U : Matrix (Fin 2 ⊕ n) (Fin 2 ⊕ n) K,
    ∃ D : Matrix n n K,
      T*U=1 ∧ U*T=1 ∧
      T.transpose*B*T=Matrix.fromBlocks (![![0,1],![-1,0]] : Matrix (Fin 2) (Fin 2) K) 0 0 D ∧
      (∀ w : n → K, w ⬝ᵥ (D *ᵥ w)=0) ∧ D.det≠0 := by
  obtain ⟨T,U,D,hTU,hUT,he,hD⟩ := alternating_nonzero_pivot_split B hB hc
  refine ⟨T,U,D,hTU,hUT,he,hD,?_⟩
  have hT : T.det≠0 := by
    intro hz
    have hh := congrArg Matrix.det hTU
    simp [Matrix.det_mul,hz] at hh
  have hh := congrArg Matrix.det he
  rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,
    Matrix.det_fromBlocks_zero₂₁,Matrix.det_fin_two] at hh
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    zero_mul,mul_zero,one_mul,neg_mul,sub_neg_eq_add,zero_add] at hh
  exact hh ▸ mul_ne_zero (mul_ne_zero hT hdet) hT

end FD56
