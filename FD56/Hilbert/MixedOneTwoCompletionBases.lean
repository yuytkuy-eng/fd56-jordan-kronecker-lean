/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.CubicTwoParity
import FD56.Hilbert.MixedOneTwoBases

/-! Explicit reduced completions for the two cubic induction bases. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option maxHeartbeats 1200000

variable {K : Type*} [Field K] [CharZero K]

def mixedOneTwoEvenCoordinates : Matrix (Fin 2) (Fin 2) K[X] :=
  C (1/4 : K) • mixedOneTwoEvenAdjugate

def mixedOneTwoOddCoordinates : Matrix (Fin 2) (Fin 2) K[X] :=
  C (1/8 : K) • mixedOneTwoOddAdjugate

theorem mixedOneTwoEvenCoordinates_scaled :
    (4 : K[X]) • mixedOneTwoEvenCoordinates (K := K)=mixedOneTwoEvenAdjugate := by
  have h : (4 : K[X])*C (1/4 : K)=1 := by
    have hh := congrArg (Polynomial.C : K → K[X]) (show (4 : K)*(1/4)=1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using hh
  simp only [mixedOneTwoEvenCoordinates, smul_smul, h, one_smul]

theorem mixedOneTwoOddCoordinates_scaled :
    (8 : K[X]) • mixedOneTwoOddCoordinates (K := K)=mixedOneTwoOddAdjugate := by
  have h : (8 : K[X])*C (1/8 : K)=1 := by
    have hh := congrArg (Polynomial.C : K → K[X]) (show (8 : K)*(1/8)=1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using hh
  simp only [mixedOneTwoOddCoordinates, smul_smul, h, one_smul]

omit [CharZero K] in
private theorem polynomial_matrix_smul_cancel {a b : Type*} (s : K[X]) (hs : s≠0)
    {A B : Matrix a b K[X]} (h : s • A=s • B) : A=B := by
  apply Matrix.ext
  intro i j
  exact mul_left_cancel₀ hs (congrArg (fun M : Matrix a b K[X] => M i j) h)

omit [CharZero K] in
private theorem scale_triple_middle {a b c d : Type*} [Fintype b] [Fintype c]
    (s : K[X]) (A : Matrix a b K[X]) (B : Matrix b c K[X]) (C : Matrix c d K[X]) :
    s • (A*B*C)=A*(s • B)*C := by
  simp only [Matrix.smul_mul,Matrix.mul_smul]

def mixedOneTwoEvenSelector : Matrix (Fin 4) (Fin 2) K[X] :=
  ![![1,0], ![0,1], ![0,0], ![0,0]]

def mixedOneTwoEvenRightInverse : Matrix (Fin 2) (Fin 4) K[X] :=
  ![![0,0,-1,-X^2], ![0,0,0,-1]]

def mixedOneTwoEvenKernel : Matrix (Fin 2) (Fin 4) K[X] :=
  ![![2+X,-X^2,X^4,0], ![1,2-X,2*X^2+X^3,4*X^4]]

theorem mixedOneTwoEven_gDegree :
    ∀ x j, (mixedOneTwoEvenBase (K := K) x j).natDegree≤(fun _ : Fin 2 => 2) j+2 := by
  dsimp only [mixedOneTwoEvenSelector,mixedOneTwoEvenRightInverse,mixedOneTwoEvenKernel]
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [mixedOneTwoEvenBase,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.head_cons,
    Matrix.head_fin_const, Nat.reduceAdd]
  all_goals first | exact natDegree_add_le_of_degree_le (by simp) (by simp) | simp

theorem mixedOneTwoEven_sDegree :
    DegreeBound (mixedOneTwoEvenSelector (K := K)) 0 := by
  dsimp only [mixedOneTwoEvenSelector,mixedOneTwoEvenRightInverse,mixedOneTwoEvenKernel]
  intro i j; fin_cases i <;> fin_cases j <;> norm_num

theorem mixedOneTwoEven_vDegree :
    ∀ j x, (mixedOneTwoEvenKernel (K := K) j x).natDegree≤4+0*j.val := by
  dsimp only [mixedOneTwoEvenSelector,mixedOneTwoEvenRightInverse,mixedOneTwoEvenKernel]
  intro j i
  fin_cases j <;> fin_cases i <;> simp only [Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.head_cons, Matrix.head_fin_const,
    Nat.zero_mul, Nat.add_zero, sub_eq_add_neg]
  · exact natDegree_add_le_of_degree_le (by simp) (by simp)
  · simp
  · simp
  · simp
  · simp
  · exact natDegree_add_le_of_degree_le (by simp) (by simp)
  · exact natDegree_add_le_of_degree_le (natDegree_mul_le.trans (by norm_num)) (by simp)
  · exact natDegree_mul_le.trans (by norm_num)

theorem mixedOneTwoEven_leading :
    Function.Injective (Matrix.mulVec (fun x j => (mixedOneTwoEvenKernel (K := K) j x).coeff (4+0*j.val))) := by
  dsimp only [mixedOneTwoEvenSelector,mixedOneTwoEvenRightInverse,mixedOneTwoEvenKernel]
  intro u v h
  have h2 := congrFun h (2 : Fin 4)
  have h3 := congrFun h (3 : Fin 4)
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, coeff_add,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
    coeff_mul_X_pow', coeff_sub] at h2 h3
  funext j
  fin_cases j
  · exact h2
  · exact h3

theorem mixedOneTwoEven_rg :
    mixedOneTwoEvenRightInverse (K := K)*mixedOneTwoEvenBase=(1 : Matrix (Fin 2) (Fin 2) K[X]) := by
  dsimp only [mixedOneTwoEvenSelector,mixedOneTwoEvenRightInverse,mixedOneTwoEvenKernel]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [mixedOneTwoEvenBase, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;> ring

theorem mixedOneTwoEven_rs :
    mixedOneTwoEvenRightInverse (K := K)*mixedOneTwoEvenSelector=(0 : Matrix (Fin 2) (Fin 2) K[X]) := by
  dsimp only [mixedOneTwoEvenSelector,mixedOneTwoEvenRightInverse,mixedOneTwoEvenKernel]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem mixedOneTwoEven_vg :
    mixedOneTwoEvenKernel (K := K)*mixedOneTwoEvenBase=(0 : Matrix (Fin 2) (Fin 2) K[X]) := by
  dsimp only [mixedOneTwoEvenSelector,mixedOneTwoEvenRightInverse,mixedOneTwoEvenKernel]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [mixedOneTwoEvenBase, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem mixedOneTwoEven_wa :
    mixedOneTwoEvenCoordinates (K := K)*(mixedOneTwoEvenKernel*mixedOneTwoEvenSelector)=1 := by
  dsimp only [mixedOneTwoEvenSelector,mixedOneTwoEvenRightInverse,mixedOneTwoEvenKernel]
  apply polynomial_matrix_smul_cancel 4 (by norm_num)
  rw [← Matrix.smul_mul, mixedOneTwoEvenCoordinates_scaled]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [mixedOneTwoEvenAdjugate, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.smul_apply, Matrix.one_apply] <;> ring

theorem mixedOneTwoEven_completion :
    mixedOneTwoEvenBase (K := K)*mixedOneTwoEvenRightInverse+mixedOneTwoEvenSelector*mixedOneTwoEvenCoordinates*mixedOneTwoEvenKernel=(1 : Matrix (Fin 4) (Fin 4) K[X]) := by
  dsimp only [mixedOneTwoEvenSelector,mixedOneTwoEvenRightInverse,mixedOneTwoEvenKernel]
  apply polynomial_matrix_smul_cancel 4 (by norm_num)
  rw [smul_add, scale_triple_middle,
    mixedOneTwoEvenCoordinates_scaled]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [mixedOneTwoEvenBase, mixedOneTwoEvenAdjugate, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.smul_apply, Matrix.one_apply] <;> ring

theorem mixedOneTwoEven_aDegree :
    DegreeBound (mixedOneTwoEvenKernel (K := K)*mixedOneTwoEvenSelector) 2 := by
  dsimp only [mixedOneTwoEvenSelector,mixedOneTwoEvenRightInverse,mixedOneTwoEvenKernel]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.head_cons, Matrix.head_fin_const,
      mul_one, mul_zero, add_zero, zero_add, sub_eq_add_neg]
  all_goals first
    | exact natDegree_add_le_of_degree_le (by simp) (by simp)
    | simp

def mixedOneTwoEvenCompletion :
    CubicTwoCompletion (m := Fin 4) (fun _ : Fin 2 => 2) 4 0
      (mixedOneTwoEvenCoordinates (K := K)) where
  G := mixedOneTwoEvenBase
  S := mixedOneTwoEvenSelector
  R := mixedOneTwoEvenRightInverse
  V := mixedOneTwoEvenKernel
  gDegree := mixedOneTwoEven_gDegree
  sDegree := mixedOneTwoEven_sDegree
  vDegree := mixedOneTwoEven_vDegree
  leading := mixedOneTwoEven_leading
  rg := mixedOneTwoEven_rg
  rs := mixedOneTwoEven_rs
  vg := mixedOneTwoEven_vg
  wa := mixedOneTwoEven_wa
  completion := mixedOneTwoEven_completion
  aDegree := mixedOneTwoEven_aDegree

def mixedOneTwoOddSelector : Matrix (Fin 5) (Fin 2) K[X] :=
  ![![1,0], ![0,1], ![0,0], ![0,0], ![0,0]]

def mixedOneTwoOddRightInverse : Matrix (Fin 3) (Fin 5) K[X] :=
  ![![0,0,-1,-X^2,-2*X^4], ![0,0,0,-1,-X^2], ![0,0,0,0,-1]]

def mixedOneTwoOddKernel : Matrix (Fin 2) (Fin 5) K[X] :=
  ![![9,4-6*X,4*X-2*X^2+3*X^3,4*X^3+2*X^4-3*X^5,8*X^5],
    ![-2-3*X,2*X^2,-X^4,X^6,0]]

theorem mixedOneTwoOdd_gDegree :
    ∀ x j, (mixedOneTwoOddBase (K := K) x j).natDegree≤(fun j : Fin 3 => if j=0 then 1 else 2) j+2 := by
  dsimp only [mixedOneTwoOddSelector,mixedOneTwoOddRightInverse,mixedOneTwoOddKernel]
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [mixedOneTwoOddBase,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.head_cons,
    Matrix.head_fin_const, Fin.reduceEq, if_true, if_false, Nat.reduceAdd]
  all_goals first | exact natDegree_add_le_of_degree_le (by simp) (by simp) | simp

theorem mixedOneTwoOdd_sDegree :
    DegreeBound (mixedOneTwoOddSelector (K := K)) 0 := by
  dsimp only [mixedOneTwoOddSelector,mixedOneTwoOddRightInverse,mixedOneTwoOddKernel]
  intro i j; fin_cases i <;> fin_cases j <;> norm_num

theorem mixedOneTwoOdd_vDegree :
    ∀ j x, (mixedOneTwoOddKernel (K := K) j x).natDegree≤5+1*j.val := by
  dsimp only [mixedOneTwoOddSelector,mixedOneTwoOddRightInverse,mixedOneTwoOddKernel]
  intro j i
  fin_cases j <;> fin_cases i <;> simp only [Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.head_cons, Matrix.head_fin_const,
    Fin.val_zero, Fin.val_one, Nat.one_mul, Nat.reduceAdd, sub_eq_add_neg]
  · simp
  · apply natDegree_add_le_of_degree_le (by simp)
    rw [natDegree_neg]
    exact natDegree_mul_le.trans (by norm_num)
  · apply natDegree_add_le_of_degree_le
    · apply natDegree_add_le_of_degree_le
      · exact natDegree_mul_le.trans (by norm_num)
      · rw [natDegree_neg]
        exact natDegree_mul_le.trans (by norm_num)
    · exact natDegree_mul_le.trans (by norm_num)
  · apply natDegree_add_le_of_degree_le
    · exact natDegree_add_le_of_degree_le
        (natDegree_mul_le.trans (by norm_num)) (natDegree_mul_le.trans (by norm_num))
    · rw [natDegree_neg]
      exact natDegree_mul_le.trans (by norm_num)
  · exact natDegree_mul_le.trans (by norm_num)
  · apply natDegree_add_le_of_degree_le (by simp)
    rw [natDegree_neg]
    exact natDegree_mul_le.trans (by norm_num)
  · exact natDegree_mul_le.trans (by norm_num)
  · simp
  · simp
  · simp

theorem mixedOneTwoOdd_leading :
    Function.Injective (Matrix.mulVec (fun x j => (mixedOneTwoOddKernel (K := K) j x).coeff (5+1*j.val))) := by
  dsimp only [mixedOneTwoOddSelector,mixedOneTwoOddRightInverse,mixedOneTwoOddKernel]
  intro u v h
  have h3 := congrFun h (3 : Fin 5)
  have h4 := congrFun h (4 : Fin 5)
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, coeff_add,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
    coeff_mul_X_pow', coeff_sub] at h3 h4
  funext j
  fin_cases j
  · exact h4
  · change u 1=v 1
    rw [h4] at h3
    exact add_left_cancel h3

theorem mixedOneTwoOdd_rg :
    mixedOneTwoOddRightInverse (K := K)*mixedOneTwoOddBase=(1 : Matrix (Fin 3) (Fin 3) K[X]) := by
  dsimp only [mixedOneTwoOddSelector,mixedOneTwoOddRightInverse,mixedOneTwoOddKernel]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [mixedOneTwoOddBase, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;> ring

theorem mixedOneTwoOdd_rs :
    mixedOneTwoOddRightInverse (K := K)*mixedOneTwoOddSelector=(0 : Matrix (Fin 3) (Fin 2) K[X]) := by
  dsimp only [mixedOneTwoOddSelector,mixedOneTwoOddRightInverse,mixedOneTwoOddKernel]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem mixedOneTwoOdd_vg :
    mixedOneTwoOddKernel (K := K)*mixedOneTwoOddBase=(0 : Matrix (Fin 2) (Fin 3) K[X]) := by
  dsimp only [mixedOneTwoOddSelector,mixedOneTwoOddRightInverse,mixedOneTwoOddKernel]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [mixedOneTwoOddBase, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem mixedOneTwoOdd_wa :
    mixedOneTwoOddCoordinates (K := K)*(mixedOneTwoOddKernel*mixedOneTwoOddSelector)=1 := by
  dsimp only [mixedOneTwoOddSelector,mixedOneTwoOddRightInverse,mixedOneTwoOddKernel]
  apply polynomial_matrix_smul_cancel 8 (by norm_num)
  rw [← Matrix.smul_mul, mixedOneTwoOddCoordinates_scaled]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [mixedOneTwoOddAdjugate, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.smul_apply, Matrix.one_apply] <;> ring

theorem mixedOneTwoOdd_completion :
    mixedOneTwoOddBase (K := K)*mixedOneTwoOddRightInverse+mixedOneTwoOddSelector*mixedOneTwoOddCoordinates*mixedOneTwoOddKernel=(1 : Matrix (Fin 5) (Fin 5) K[X]) := by
  dsimp only [mixedOneTwoOddSelector,mixedOneTwoOddRightInverse,mixedOneTwoOddKernel]
  apply polynomial_matrix_smul_cancel 8 (by norm_num)
  rw [smul_add, scale_triple_middle,
    mixedOneTwoOddCoordinates_scaled]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [mixedOneTwoOddBase, mixedOneTwoOddAdjugate, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.smul_apply, Matrix.one_apply] <;> ring

theorem mixedOneTwoOdd_aDegree :
    DegreeBound (mixedOneTwoOddKernel (K := K)*mixedOneTwoOddSelector) 2 := by
  dsimp only [mixedOneTwoOddSelector,mixedOneTwoOddRightInverse,mixedOneTwoOddKernel]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.head_cons, Matrix.head_fin_const,
      mul_one, mul_zero, add_zero, zero_add, sub_eq_add_neg]
  all_goals first
    | exact natDegree_add_le_of_degree_le (by simp)
        (by rw [natDegree_neg]; exact natDegree_mul_le.trans (by norm_num))
    | exact natDegree_mul_le.trans (by norm_num)
    | simp

def mixedOneTwoOddCompletion :
    CubicTwoCompletion (m := Fin 5) (fun j : Fin 3 => if j=0 then 1 else 2) 5 1
      (mixedOneTwoOddCoordinates (K := K)) where
  G := mixedOneTwoOddBase
  S := mixedOneTwoOddSelector
  R := mixedOneTwoOddRightInverse
  V := mixedOneTwoOddKernel
  gDegree := mixedOneTwoOdd_gDegree
  sDegree := mixedOneTwoOdd_sDegree
  vDegree := mixedOneTwoOdd_vDegree
  leading := mixedOneTwoOdd_leading
  rg := mixedOneTwoOdd_rg
  rs := mixedOneTwoOdd_rs
  vg := mixedOneTwoOdd_vg
  wa := mixedOneTwoOdd_wa
  completion := mixedOneTwoOdd_completion
  aDegree := mixedOneTwoOdd_aDegree

end FD56
