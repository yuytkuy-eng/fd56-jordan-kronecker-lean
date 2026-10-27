/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.AlternatingCrossDeterminant
import FD56.Hilbert.RegularJordanBlock

/-! An explicit constant Jordan normalization for a four-dimensional nilpotent pair. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

def nilpotentFourGram (d : K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks ![![0,d],![-d,0]] ![![0,1],![-1,0]] ![![0,1],![-1,0]] 0

def nilpotentFourShift : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks ![![0,1],![-1,0]] 0 0 0

def nilpotentFourChange (d : K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks ![![1,0],![0,-1]] 0 ![![0,0],![0,d]] ![![0,1],![1,0]]

def nilpotentFourChangeInverse (d : K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks ![![1,0],![0,-1]] 0 ![![0,d],![0,0]] ![![0,1],![1,0]]

theorem nilpotentFourGram_det (d : K) : (nilpotentFourGram d).det=1 := by
  have ht : -Matrix.transpose (![![0,1],![-1,0]] : Matrix (Fin 2) (Fin 2) K)=
      ![![0,1],![-1,0]] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  change (Matrix.fromBlocks (![![0,d],![-d,0]] : Matrix (Fin 2) (Fin 2) K)
    ![![0,1],![-1,0]] ![![0,1],![-1,0]] 0).det=1
  have he := alternating_cross_block_det (![![0,d],![-d,0]] : Matrix (Fin 2) (Fin 2) K)
    (![![0,1],![-1,0]] : Matrix (Fin 2) (Fin 2) K)
  rw [ht] at he
  rw [he,Matrix.det_fin_two]
  norm_num

theorem nilpotentFourChange_inverse (d : K) :
    nilpotentFourChange d*nilpotentFourChangeInverse d=1 ∧
      nilpotentFourChangeInverse d*nilpotentFourChange d=1 := by
  constructor <;> ext i j <;>
    rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [nilpotentFourChange,nilpotentFourChangeInverse,Matrix.mul_apply,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Matrix.one_apply]

theorem nilpotentFourChange_pair (d : K) :
    (nilpotentFourChange d).transpose*nilpotentFourGram d*nilpotentFourChange d=
      Matrix.fromBlocks 0 (1 : Matrix (Fin 2) (Fin 2) K) (-1) 0 ∧
    (nilpotentFourChange d).transpose*(-nilpotentFourShift)*nilpotentFourChange d=
      nilpotentFourShift := by
  constructor <;> ext i j <;>
    rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [nilpotentFourChange,nilpotentFourGram,nilpotentFourShift,Matrix.mul_apply,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Matrix.one_apply]

theorem nilpotentFour_jordan_decomposition (d a : K) :
    ∃ T S : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K,
      T*S=1 ∧ S*T=1 ∧
      (T.map C).transpose*((X-C a)•(nilpotentFourGram d).map C-
        nilpotentFourShift.map C)*T.map C=skewJordanBlockPencil a 2 := by
  let Q := nilpotentFourChange d
  let R := nilpotentFourChangeInverse d
  have hQR : Q*R=1 := (nilpotentFourChange_inverse d).1
  have hRQ : R*Q=1 := (nilpotentFourChange_inverse d).2
  have hcong : (Q.map C).transpose*((X-C a)•(nilpotentFourGram d).map C-
      nilpotentFourShift.map C)*Q.map C=rankTwoRegularCoupling (X-C a) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      simp [Q,nilpotentFourChange,nilpotentFourGram,nilpotentFourShift,rankTwoRegularCoupling,
        Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_succ,Matrix.one_apply] <;> ring
  obtain ⟨U,V,hUV,hVU,hJ⟩ := rankTwoRegularCoupling_constant_congruence a
  refine ⟨Q*U,V*R,?_,?_,?_⟩
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc U,hUV,Matrix.one_mul,hQR]
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc R,hRQ,Matrix.one_mul,hVU]
  · rw [Matrix.map_mul,Matrix.transpose_mul]
    calc
      _ = (U.map C).transpose*((Q.map C).transpose*
        ((X-C a)•(nilpotentFourGram d).map C-nilpotentFourShift.map C)*Q.map C)*U.map C := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hcong,hJ]

end FD56
