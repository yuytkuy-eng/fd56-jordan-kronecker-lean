/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SymplecticSimpleJordan
import FD56.LinearAlgebra.NilpotentFourNormalForm
import FD56.LinearAlgebra.NilpotentFourGram
import FD56.LinearAlgebra.RankTwoOrthogonalDecomposition
import FD56.LinearAlgebra.AlternatingRankTwoNilpotent
import Mathlib.Data.Matrix.Rank

/-! Constant Jordan coordinates for a rank-two nilpotent alternating pencil. -/

noncomputable section
set_option maxHeartbeats 2000000
namespace FD56
open Matrix Polynomial

variable {K : Type*} [Field K]

abbrev rankTwoJordanIndex (k : ℕ) :=
  (Fin 2 ⊕ Fin 2) ⊕ ((Fin 1 ⊕ Fin 1) × Fin k)

def rankTwoJordanPencil (a : K) (k : ℕ) :
    Matrix (rankTwoJordanIndex k) (rankTwoJordanIndex k) K[X] :=
  Matrix.fromBlocks (skewJordanBlockPencil a 2) 0 0
    (Matrix.blockDiagonal (fun _ : Fin k => skewJordanBlockPencil a 1))

theorem nilpotent_four_sum_jordan_decomposition (d a : K) (k : ℕ) :
    ∃ T : Matrix ((Fin 2 ⊕ Fin 2) ⊕ (Fin 2 × Fin k)) (rankTwoJordanIndex k) K,
    ∃ U : Matrix (rankTwoJordanIndex k) ((Fin 2 ⊕ Fin 2) ⊕ (Fin 2 × Fin k)) K,
      T*U=1 ∧ U*T=1 ∧
      (T.map C).transpose *
        (Matrix.fromBlocks ((X-C a) • (nilpotentFourGram d).map C-nilpotentFourShift.map C)
          0 0 ((X-C a) • (standardSymplecticMatrix K k).map C)) * T.map C =
        rankTwoJordanPencil a k := by
  obtain ⟨Q,R,hQR,hRQ,hQ⟩ := nilpotentFour_jordan_decomposition d a
  let F : Matrix ((Fin 2 ⊕ Fin 2) ⊕ (Fin 2 × Fin k))
      ((Fin 2 ⊕ Fin 2) ⊕ (Fin 2 × Fin k)) K := Matrix.fromBlocks Q 0 0 1
  let G : Matrix ((Fin 2 ⊕ Fin 2) ⊕ (Fin 2 × Fin k))
      ((Fin 2 ⊕ Fin 2) ⊕ (Fin 2 × Fin k)) K := Matrix.fromBlocks R 0 0 1
  let e : rankTwoJordanIndex k ≃ ((Fin 2 ⊕ Fin 2) ⊕ (Fin 2 × Fin k)) :=
    Equiv.sumCongr (Equiv.refl _) (symplecticJordanIndex (Fin k))
  have hFG : F*G=1 := by simp [F,G,Matrix.fromBlocks_multiply,hQR,Matrix.fromBlocks_one]
  have hGF : G*F=1 := by simp [F,G,Matrix.fromBlocks_multiply,hRQ,Matrix.fromBlocks_one]
  have hcong : (F.map C).transpose *
      (Matrix.fromBlocks ((X-C a) • (nilpotentFourGram d).map C-nilpotentFourShift.map C)
        0 0 ((X-C a) • (standardSymplecticMatrix K k).map C)) * F.map C =
      Matrix.fromBlocks (skewJordanBlockPencil a 2) 0 0
        ((X-C a) • (standardSymplecticMatrix K k).map C) := by
    simpa only [F,Matrix.fromBlocks_map,Matrix.map_zero,Polynomial.C_0,
      Matrix.map_one,Polynomial.C_1,Matrix.fromBlocks_transpose,Matrix.transpose_zero,
      Matrix.transpose_one,Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,
      zero_add,add_zero,Matrix.one_mul,Matrix.mul_one] using
      congrArg (fun A => Matrix.fromBlocks A 0 0
        ((X-C a) • (standardSymplecticMatrix K k).map C)) hQ
  refine ⟨F.submatrix id e,G.submatrix e id,?_,?_,?_⟩
  · rw [Matrix.submatrix_mul_equiv,hFG,Matrix.submatrix_id_id]
  · change G.submatrix e (Equiv.refl _) * F.submatrix (Equiv.refl _) e=1
    rw [Matrix.submatrix_mul_equiv,hGF]
    exact Matrix.submatrix_one_equiv e
  · simp only [← Matrix.submatrix_map]
    change (F.map C).transpose.submatrix e (Equiv.refl _) *
      (Matrix.fromBlocks ((X-C a) • (nilpotentFourGram d).map C-nilpotentFourShift.map C)
        0 0 ((X-C a) • (standardSymplecticMatrix K k).map C)).submatrix
          (Equiv.refl _) (Equiv.refl _) * (F.map C).submatrix (Equiv.refl _) e=_
    rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,hcong]
    apply Matrix.ext
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · rfl
    · rfl
    · exact congrFun (congrFun (standardSymplecticMatrix_simple_jordan k a) i) j

theorem nonzero_matrix_unit_pair {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (hA : A≠0) :
    ∃ u v : n → K, u ⬝ᵥ (A *ᵥ v)=1 := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hA
  obtain ⟨j,hij⟩ := Function.ne_iff.mp hi
  change A i j≠0 at hij
  refine ⟨(Pi.single i 1 : n → K),(A i j)⁻¹ • (Pi.single j 1 : n → K),?_⟩
  simp only [Matrix.mulVec_smul,dotProduct_smul,smul_eq_mul]
  simp [Matrix.mulVec,dotProduct,Pi.single_apply,hij]

theorem nilpotent_rank_two_jordan_decomposition {n : Type*} [Fintype n] [DecidableEq n]
    (B N : Matrix n n K) (a : K)
    (hB : ∀ v, v ⬝ᵥ (B *ᵥ v)=0)
    (hBN : ∀ v, v ⬝ᵥ ((B*N) *ᵥ v)=0)
    (hdet : B.det≠0) (hn : IsNilpotent N)
    (hr : Module.finrank K (LinearMap.range (Matrix.toLin' N))=2) :
    ∃ k : ℕ, Fintype.card n=4+2*k ∧
    ∃ T : Matrix n (rankTwoJordanIndex k) K,
    ∃ U : Matrix (rankTwoJordanIndex k) n K,
      T*U=1 ∧ U*T=1 ∧
      (T.map C).transpose*((X-C a) • B.map C-(B*N).map C)*T.map C=
        rankTwoJordanPencil a k := by
  classical
  have hrA : Module.finrank K (LinearMap.range (Matrix.toLin' (B*N)))=2 := by
    change (B*N).rank=2
    rw [Matrix.rank_mul_eq_right_of_isUnit_det B N (isUnit_iff_ne_zero.mpr hdet)]
    exact hr
  have hA : B*N≠0 := by
    intro hz
    change (B*N).rank=2 at hrA
    rw [hz,Matrix.rank_zero] at hrA
    omega
  obtain ⟨u,v,hpair⟩ := nonzero_matrix_unit_pair (B*N) hA
  have hpair' : u ⬝ᵥ (B *ᵥ (N *ᵥ v))=1 := by
    rwa [Matrix.mulVec_mulVec]
  have hinv : B⁻¹*(B*N)=N := by
    rw [← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),Matrix.one_mul]
  have hs : N*N=0 := by
    have hsq := alternating_rank_two_nilpotent_ratio (B*N) B B⁻¹
      (Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)) hBN hB (by omega)
      (by rwa [hinv])
    simpa only [hinv,pow_two] using hsq
  let Q := nilpotentFourColumns N u v
  have hGram := nilpotent_four_gram_pair B N u v hB hBN hs hpair'
  have hG : (Q.transpose*B*Q).det≠0 := by
    rw [show Q.transpose*B*Q=nilpotentFourGram (u ⬝ᵥ (B *ᵥ v)) from hGram.1,
      nilpotentFourGram_det]
    exact one_ne_zero
  obtain ⟨k,hk,S,T,hST,hTS,_,hAS,hBS⟩ := rank_two_alternating_pair_decomposition
    (B*N) B N Q (nilpotent_four_self_adjoint B N hB hBN) hBN hB (by omega)
      hdet hG u v (by rw [hpair]; exact one_ne_zero) (Sum.inr 0) (Sum.inr 1) rfl rfl
  have hcard : Fintype.card n=4+2*k := by
    let e : (((Fin 2 ⊕ Fin 2) ⊕ (Fin 2 × Fin k)) → K) ≃ₗ[K] (n → K) :=
      { Matrix.toLin' S with
        invFun := Matrix.toLin' T
        left_inv := by
          intro w
          change T *ᵥ (S *ᵥ w)=w
          rw [Matrix.mulVec_mulVec,hTS,Matrix.one_mulVec]
        right_inv := by
          intro w
          change S *ᵥ (T *ᵥ w)=w
          rw [Matrix.mulVec_mulVec,hST,Matrix.one_mulVec] }
    simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_sum,Fintype.card_prod,
      Fintype.card_fin] using e.finrank_eq.symm
  have hmapB : (S.map C).transpose*B.map C*S.map C=
      (Matrix.fromBlocks (nilpotentFourGram (u ⬝ᵥ (B *ᵥ v))) 0 0
        (standardSymplecticMatrix K k)).map C := by
    change S.transpose.map C*B.map C*S.map C=_
    rw [← Matrix.map_mul,← Matrix.map_mul,hBS]
    exact congrArg (fun A => (Matrix.fromBlocks A 0 0 (standardSymplecticMatrix K k)).map C) hGram.1
  have hmapA : (S.map C).transpose*(B*N).map C*S.map C=
      (Matrix.fromBlocks (nilpotentFourShift (K:=K)) 0 0
        (0 : Matrix (Fin 2 × Fin k) (Fin 2 × Fin k) K)).map C := by
    change S.transpose.map C*(B*N).map C*S.map C=_
    rw [← Matrix.map_mul,← Matrix.map_mul,hAS]
    exact congrArg (fun A => (Matrix.fromBlocks A 0 0
      (0 : Matrix (Fin 2 × Fin k) (Fin 2 × Fin k) K)).map C) hGram.2
  have hP : (S.map C).transpose*((X-C a) • B.map C-(B*N).map C)*S.map C=
      Matrix.fromBlocks ((X-C a) • (nilpotentFourGram (u ⬝ᵥ (B *ᵥ v))).map C-
        nilpotentFourShift.map C) 0 0 ((X-C a) • (standardSymplecticMatrix K k).map C) := by
    rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,hmapB,hmapA]
    apply Matrix.ext
    intro i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.smul_apply,smul_eq_mul]
  obtain ⟨V,W,hVW,hWV,hV⟩ := nilpotent_four_sum_jordan_decomposition (u ⬝ᵥ (B *ᵥ v)) a k
  refine ⟨k,hcard,S*V,W*T,?_,?_,?_⟩
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc V,hVW,Matrix.one_mul,hST]
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc T,hTS,Matrix.one_mul,hWV]
  · rw [Matrix.map_mul,Matrix.transpose_mul]
    calc
      _ = (V.map C).transpose*((S.map C).transpose*
        ((X-C a) • B.map C-(B*N).map C)*S.map C)*V.map C := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP,hV]

end FD56
