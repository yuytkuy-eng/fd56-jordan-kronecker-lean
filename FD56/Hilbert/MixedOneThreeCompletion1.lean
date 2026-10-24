/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedOneThreeBase1
import FD56.Hilbert.UniformCubicCompletion
import FD56.Hilbert.FiniteMatrixEvaluation

/-! A polynomial completion for the three-high-column base with 1 low columns. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

variable {K : Type*} [Field K] [CharZero K]

def mixedOneThreeBase1Selector : Matrix (Fin 7) (Fin 3) K[X] :=
  ![![1,0,0],
    ![0,1,0],
    ![0,0,1],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0]]

def mixedOneThreeBase1Right : Matrix (Fin 4) (Fin 7) K[X] :=
  ![![0,0,0,-1,-1,-X-X^3,-2*X^3-X^4-X^5],
    ![0,0,0,0,-1,-X-X^3,-2*X^3-X^5],
    ![0,0,0,0,0,-1,-X^2],
    ![0,0,0,0,0,0,-1]]

def mixedOneThreeBase1Kernel : Matrix (Fin 3) (Fin 7) K[X] :=
  ![![-X,2+X+X^2,-X^2-X^4,-X^4,X^5,0,0],
    ![-1,0,X,-X^3,0,X^5,0],
    ![1,-3-X,4-3*X+2*X^2+X^3,X^3,4*X^2-2*X^3-X^4,4*X^3+2*X^4,8*X^5]]

def mixedOneThreeBase1CoordinateNumerator : Matrix (Fin 3) (Fin 3) K[X] :=
  ![![3*X+X^2,-8+2*X-2*X^2,2*X+X^2+X^3],
    ![4-2*X+2*X^2+X^3,-4*X+4*X^2-2*X^3,2*X^2+X^4],
    ![3+X,2-2*X,2+X+X^2]]

def mixedOneThreeBase1Coordinates : Matrix (Fin 3) (Fin 3) K[X] :=
  C (1/8 : K) • mixedOneThreeBase1CoordinateNumerator

theorem mixedOneThreeBase1Coordinates_scaled :
    (8 : K[X]) • mixedOneThreeBase1Coordinates (K := K)=mixedOneThreeBase1CoordinateNumerator := by
  have h : (8 : K[X])*C (1/8 : K)=1 := by
    have hh := congrArg (Polynomial.C : K → K[X])
      (show (8 : K)*(1/8)=1 by norm_num)
    simpa only [map_mul,map_ofNat,map_one] using hh
  simp only [mixedOneThreeBase1Coordinates,smul_smul,h,one_smul]

omit [CharZero K] in
private theorem polynomial_matrix_smul_cancel {a b : Type*} (s : K[X]) (hs : s≠0)
    {A B : Matrix a b K[X]} (h : s • A=s • B) : A=B := by
  apply Matrix.ext
  intro i j
  exact mul_left_cancel₀ hs (congrArg (fun M : Matrix a b K[X] => M i j) h)

theorem mixedOneThreeBase1_gDegree :
    ∀ i j, (mixedOneThreeBase1 (K := K) i j).natDegree≤(if j.val<1 then 1 else 2)+2 := by
  intro i j
  fin_cases i <;> fin_cases j
  · change (X^3 : K[X]).natDegree≤3
    exact (by norm_num)
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (X^4 : K[X]).natDegree≤4
    exact (by norm_num)
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (X^2 : K[X]).natDegree≤4
    exact (by norm_num)
  · change (X^4 : K[X]).natDegree≤4
    exact (by norm_num)
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (-1 : K[X]).natDegree≤3
    exact (by rw [natDegree_neg]; exact (by norm_num))
  · change (1 : K[X]).natDegree≤4
    exact (by norm_num)
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (X^4 : K[X]).natDegree≤4
    exact (by norm_num)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (-1 : K[X]).natDegree≤4
    exact (by rw [natDegree_neg]; exact (by norm_num))
  · change (X+X^3 : K[X]).natDegree≤4
    exact (natDegree_add_le_of_degree_le (by norm_num) (by norm_num))
  · change (X^3 : K[X]).natDegree≤4
    exact (by norm_num)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (-1 : K[X]).natDegree≤4
    exact (by rw [natDegree_neg]; exact (by norm_num))
  · change (X^2 : K[X]).natDegree≤4
    exact (by norm_num)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (-1 : K[X]).natDegree≤4
    exact (by rw [natDegree_neg]; exact (by norm_num))

theorem mixedOneThreeBase1_sDegree : DegreeBound (mixedOneThreeBase1Selector (K := K)) 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [mixedOneThreeBase1Selector,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine]

theorem mixedOneThreeBase1_vDegree : DegreeBound (mixedOneThreeBase1Kernel (K := K)) 5 := by
  intro i j
  fin_cases i <;> fin_cases j
  · change (-X : K[X]).natDegree≤5
    exact (by rw [natDegree_neg]; exact (by norm_num))
  · change (2+X+X^2 : K[X]).natDegree≤5
    exact (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (by norm_num) (by norm_num)) (by norm_num))
  · change (-X^2-X^4 : K[X]).natDegree≤5
    exact ((natDegree_sub_le _ _).trans (max_le (by rw [natDegree_neg]; exact (by norm_num)) (by norm_num)))
  · change (-X^4 : K[X]).natDegree≤5
    exact (by rw [natDegree_neg]; exact (by norm_num))
  · change (X^5 : K[X]).natDegree≤5
    exact (by norm_num)
  · change (0 : K[X]).natDegree≤5
    exact (by simp)
  · change (0 : K[X]).natDegree≤5
    exact (by simp)
  · change (-1 : K[X]).natDegree≤5
    exact (by rw [natDegree_neg]; exact (by norm_num))
  · change (0 : K[X]).natDegree≤5
    exact (by simp)
  · change (X : K[X]).natDegree≤5
    exact (by norm_num)
  · change (-X^3 : K[X]).natDegree≤5
    exact (by rw [natDegree_neg]; exact (by norm_num))
  · change (0 : K[X]).natDegree≤5
    exact (by simp)
  · change (X^5 : K[X]).natDegree≤5
    exact (by norm_num)
  · change (0 : K[X]).natDegree≤5
    exact (by simp)
  · change (1 : K[X]).natDegree≤5
    exact (by norm_num)
  · change (-3-X : K[X]).natDegree≤5
    exact ((natDegree_sub_le _ _).trans (max_le (by rw [natDegree_neg]; exact (by norm_num)) (by norm_num)))
  · change (4-3*X+2*X^2+X^3 : K[X]).natDegree≤5
    exact (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ((natDegree_sub_le _ _).trans (max_le (by norm_num) (natDegree_mul_le.trans (by norm_num)))) (natDegree_mul_le.trans (by norm_num))) (by norm_num))
  · change (X^3 : K[X]).natDegree≤5
    exact (by norm_num)
  · change (4*X^2-2*X^3-X^4 : K[X]).natDegree≤5
    exact ((natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le (natDegree_mul_le.trans (by norm_num)) (natDegree_mul_le.trans (by norm_num)))) (by norm_num)))
  · change (4*X^3+2*X^4 : K[X]).natDegree≤5
    exact (natDegree_add_le_of_degree_le (natDegree_mul_le.trans (by norm_num)) (natDegree_mul_le.trans (by norm_num)))
  · change (8*X^5 : K[X]).natDegree≤5
    exact (natDegree_mul_le.trans (by norm_num))

theorem mixedOneThreeBase1_leading : Function.Injective (Matrix.mulVec
    (fun x j => (mixedOneThreeBase1Kernel (K := K) j x).coeff 5)) := by
  intro a b h
  have h4 : a 0=b 0 := by
    have hh := congrFun h (4 : Fin 7)
    norm_num [mixedOneThreeBase1Kernel,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  have h5 : a 1=b 1 := by
    have hh := congrFun h (5 : Fin 7)
    norm_num [mixedOneThreeBase1Kernel,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  have h6 : (8)*a 2=(8)*b 2 := by
    have hh := congrFun h (6 : Fin 7)
    norm_num [mixedOneThreeBase1Kernel,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  funext j
  fin_cases j
  · linear_combination (norm := ring1!) h4
  · linear_combination (norm := ring1!) h5
  · linear_combination (norm := ring1!) (1/8 : K)*h6

theorem mixedOneThreeBase1_jet : Function.Injective (Matrix.mulVec
    (fun (ij : Fin 3 × Fin 3) (k : Fin 3) =>
      (mixedOneThreeBase1Coordinates (K := K) ij.1 ij.2).coeff (2-k.val))) := by
  intro a b h
  have h0 : (1/8 : K)*a 0 + (3/8 : K)*a 1=(1/8 : K)*b 0 + (3/8 : K)*b 1 := by
    have hh := congrFun h ((0,0) : Fin 3 × Fin 3)
    norm_num [mixedOneThreeBase1Coordinates,mixedOneThreeBase1CoordinateNumerator,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,Matrix.smul_apply,smul_eq_mul,coeff_C_mul,coeff_add,coeff_sub,
      coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  have h1 : (-1/4 : K)*a 0 + (1/4 : K)*a 1 + -a 2=(-1/4 : K)*b 0 + (1/4 : K)*b 1 + -b 2 := by
    have hh := congrFun h ((0,1) : Fin 3 × Fin 3)
    norm_num [mixedOneThreeBase1Coordinates,mixedOneThreeBase1CoordinateNumerator,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,Matrix.smul_apply,smul_eq_mul,coeff_C_mul,coeff_add,coeff_sub,
      coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  have h2 : (1/8 : K)*a 0 + (1/4 : K)*a 1=(1/8 : K)*b 0 + (1/4 : K)*b 1 := by
    have hh := congrFun h ((0,2) : Fin 3 × Fin 3)
    norm_num [mixedOneThreeBase1Coordinates,mixedOneThreeBase1CoordinateNumerator,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,Matrix.smul_apply,smul_eq_mul,coeff_C_mul,coeff_add,coeff_sub,
      coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  funext j
  fin_cases j
  · linear_combination (norm := ring1!) (-16)*h0 + (24)*h2
  · linear_combination (norm := ring1!) (8)*h0 + (-8)*h2
  · linear_combination (norm := ring1!) (6)*h0 + -h1 + (-8)*h2

private theorem mixedOneThreeBase1_rg_row0 (j : Fin 4) :
    (mixedOneThreeBase1Right (K := K)*mixedOneThreeBase1 : Matrix (Fin 4) (Fin 4) K[X]) 0 j=
      ((1 : Matrix (Fin 4) (Fin 4) K[X]) : Matrix (Fin 4) (Fin 4) K[X]) 0 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase1,mixedOneThreeBase1Right,mixedOneThreeBase1Selector,mixedOneThreeBase1Kernel,mixedOneThreeBase1CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase1_rg_row1 (j : Fin 4) :
    (mixedOneThreeBase1Right (K := K)*mixedOneThreeBase1 : Matrix (Fin 4) (Fin 4) K[X]) 1 j=
      ((1 : Matrix (Fin 4) (Fin 4) K[X]) : Matrix (Fin 4) (Fin 4) K[X]) 1 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase1,mixedOneThreeBase1Right,mixedOneThreeBase1Selector,mixedOneThreeBase1Kernel,mixedOneThreeBase1CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase1_rg_row2 (j : Fin 4) :
    (mixedOneThreeBase1Right (K := K)*mixedOneThreeBase1 : Matrix (Fin 4) (Fin 4) K[X]) 2 j=
      ((1 : Matrix (Fin 4) (Fin 4) K[X]) : Matrix (Fin 4) (Fin 4) K[X]) 2 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase1,mixedOneThreeBase1Right,mixedOneThreeBase1Selector,mixedOneThreeBase1Kernel,mixedOneThreeBase1CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase1_rg_row3 (j : Fin 4) :
    (mixedOneThreeBase1Right (K := K)*mixedOneThreeBase1 : Matrix (Fin 4) (Fin 4) K[X]) 3 j=
      ((1 : Matrix (Fin 4) (Fin 4) K[X]) : Matrix (Fin 4) (Fin 4) K[X]) 3 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase1,mixedOneThreeBase1Right,mixedOneThreeBase1Selector,mixedOneThreeBase1Kernel,mixedOneThreeBase1CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

theorem mixedOneThreeBase1_rg :
    mixedOneThreeBase1Right (K := K)*mixedOneThreeBase1=(1 : Matrix (Fin 4) (Fin 4) K[X]) := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact mixedOneThreeBase1_rg_row0 j
  · exact mixedOneThreeBase1_rg_row1 j
  · exact mixedOneThreeBase1_rg_row2 j
  · exact mixedOneThreeBase1_rg_row3 j

private theorem mixedOneThreeBase1_rs_row0 (j : Fin 3) :
    (mixedOneThreeBase1Right (K := K)*mixedOneThreeBase1Selector : Matrix (Fin 4) (Fin 3) K[X]) 0 j=
      ((0 : Matrix (Fin 4) (Fin 3) K[X]) : Matrix (Fin 4) (Fin 3) K[X]) 0 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase1,mixedOneThreeBase1Right,mixedOneThreeBase1Selector,mixedOneThreeBase1Kernel,mixedOneThreeBase1CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase1_rs_row1 (j : Fin 3) :
    (mixedOneThreeBase1Right (K := K)*mixedOneThreeBase1Selector : Matrix (Fin 4) (Fin 3) K[X]) 1 j=
      ((0 : Matrix (Fin 4) (Fin 3) K[X]) : Matrix (Fin 4) (Fin 3) K[X]) 1 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase1,mixedOneThreeBase1Right,mixedOneThreeBase1Selector,mixedOneThreeBase1Kernel,mixedOneThreeBase1CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase1_rs_row2 (j : Fin 3) :
    (mixedOneThreeBase1Right (K := K)*mixedOneThreeBase1Selector : Matrix (Fin 4) (Fin 3) K[X]) 2 j=
      ((0 : Matrix (Fin 4) (Fin 3) K[X]) : Matrix (Fin 4) (Fin 3) K[X]) 2 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase1,mixedOneThreeBase1Right,mixedOneThreeBase1Selector,mixedOneThreeBase1Kernel,mixedOneThreeBase1CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase1_rs_row3 (j : Fin 3) :
    (mixedOneThreeBase1Right (K := K)*mixedOneThreeBase1Selector : Matrix (Fin 4) (Fin 3) K[X]) 3 j=
      ((0 : Matrix (Fin 4) (Fin 3) K[X]) : Matrix (Fin 4) (Fin 3) K[X]) 3 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase1,mixedOneThreeBase1Right,mixedOneThreeBase1Selector,mixedOneThreeBase1Kernel,mixedOneThreeBase1CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

theorem mixedOneThreeBase1_rs :
    mixedOneThreeBase1Right (K := K)*mixedOneThreeBase1Selector=(0 : Matrix (Fin 4) (Fin 3) K[X]) := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact mixedOneThreeBase1_rs_row0 j
  · exact mixedOneThreeBase1_rs_row1 j
  · exact mixedOneThreeBase1_rs_row2 j
  · exact mixedOneThreeBase1_rs_row3 j

private theorem mixedOneThreeBase1_vg_row0 (j : Fin 4) :
    (mixedOneThreeBase1Kernel (K := K)*mixedOneThreeBase1 : Matrix (Fin 3) (Fin 4) K[X]) 0 j=
      ((0 : Matrix (Fin 3) (Fin 4) K[X]) : Matrix (Fin 3) (Fin 4) K[X]) 0 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase1,mixedOneThreeBase1Right,mixedOneThreeBase1Selector,mixedOneThreeBase1Kernel,mixedOneThreeBase1CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase1_vg_row1 (j : Fin 4) :
    (mixedOneThreeBase1Kernel (K := K)*mixedOneThreeBase1 : Matrix (Fin 3) (Fin 4) K[X]) 1 j=
      ((0 : Matrix (Fin 3) (Fin 4) K[X]) : Matrix (Fin 3) (Fin 4) K[X]) 1 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase1,mixedOneThreeBase1Right,mixedOneThreeBase1Selector,mixedOneThreeBase1Kernel,mixedOneThreeBase1CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase1_vg_row2 (j : Fin 4) :
    (mixedOneThreeBase1Kernel (K := K)*mixedOneThreeBase1 : Matrix (Fin 3) (Fin 4) K[X]) 2 j=
      ((0 : Matrix (Fin 3) (Fin 4) K[X]) : Matrix (Fin 3) (Fin 4) K[X]) 2 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase1,mixedOneThreeBase1Right,mixedOneThreeBase1Selector,mixedOneThreeBase1Kernel,mixedOneThreeBase1CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

theorem mixedOneThreeBase1_vg :
    mixedOneThreeBase1Kernel (K := K)*mixedOneThreeBase1=(0 : Matrix (Fin 3) (Fin 4) K[X]) := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact mixedOneThreeBase1_vg_row0 j
  · exact mixedOneThreeBase1_vg_row1 j
  · exact mixedOneThreeBase1_vg_row2 j

private theorem mixedOneThreeBase1_wa_row0 (j : Fin 3) :
    (mixedOneThreeBase1CoordinateNumerator (K := K)*(mixedOneThreeBase1Kernel*mixedOneThreeBase1Selector) : Matrix (Fin 3) (Fin 3) K[X]) 0 j=
      ((8 : K[X]) • (1 : Matrix (Fin 3) (Fin 3) K[X]) : Matrix (Fin 3) (Fin 3) K[X]) 0 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase1,mixedOneThreeBase1Right,mixedOneThreeBase1Selector,mixedOneThreeBase1Kernel,mixedOneThreeBase1CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase1_wa_row1 (j : Fin 3) :
    (mixedOneThreeBase1CoordinateNumerator (K := K)*(mixedOneThreeBase1Kernel*mixedOneThreeBase1Selector) : Matrix (Fin 3) (Fin 3) K[X]) 1 j=
      ((8 : K[X]) • (1 : Matrix (Fin 3) (Fin 3) K[X]) : Matrix (Fin 3) (Fin 3) K[X]) 1 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase1,mixedOneThreeBase1Right,mixedOneThreeBase1Selector,mixedOneThreeBase1Kernel,mixedOneThreeBase1CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase1_wa_row2 (j : Fin 3) :
    (mixedOneThreeBase1CoordinateNumerator (K := K)*(mixedOneThreeBase1Kernel*mixedOneThreeBase1Selector) : Matrix (Fin 3) (Fin 3) K[X]) 2 j=
      ((8 : K[X]) • (1 : Matrix (Fin 3) (Fin 3) K[X]) : Matrix (Fin 3) (Fin 3) K[X]) 2 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase1,mixedOneThreeBase1Right,mixedOneThreeBase1Selector,mixedOneThreeBase1Kernel,mixedOneThreeBase1CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

theorem mixedOneThreeBase1_wa :
    mixedOneThreeBase1Coordinates (K := K)*(mixedOneThreeBase1Kernel*mixedOneThreeBase1Selector)=(1 : Matrix (Fin 3) (Fin 3) K[X]) := by
  apply polynomial_matrix_smul_cancel 8 (by norm_num)
  rw [← Matrix.smul_mul,mixedOneThreeBase1Coordinates_scaled]
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact mixedOneThreeBase1_wa_row0 j
  · exact mixedOneThreeBase1_wa_row1 j
  · exact mixedOneThreeBase1_wa_row2 j

theorem mixedOneThreeBase1_completion :
    mixedOneThreeBase1 (K := K)*mixedOneThreeBase1Right+mixedOneThreeBase1Selector*mixedOneThreeBase1Coordinates*mixedOneThreeBase1Kernel=(1 : Matrix (Fin 7) (Fin 7) K[X]) := by
  exact polynomial_completion_of_left_inverse mixedOneThreeBase1 mixedOneThreeBase1Selector mixedOneThreeBase1Right
    mixedOneThreeBase1Kernel mixedOneThreeBase1Coordinates (by decide) mixedOneThreeBase1_rg mixedOneThreeBase1_rs
    mixedOneThreeBase1_vg mixedOneThreeBase1_wa

def mixedOneThreeBase1Completion :
    UniformCubicCompletion (m := Fin 7) (fun j : Fin 4 => if j.val<1 then 1 else 2)
      5 (mixedOneThreeBase1Coordinates (K := K)) where
  G := mixedOneThreeBase1
  S := mixedOneThreeBase1Selector
  R := mixedOneThreeBase1Right
  V := mixedOneThreeBase1Kernel
  gDegree := mixedOneThreeBase1_gDegree
  sDegree := mixedOneThreeBase1_sDegree
  vDegree := mixedOneThreeBase1_vDegree
  leading := mixedOneThreeBase1_leading
  rg := mixedOneThreeBase1_rg
  rs := mixedOneThreeBase1_rs
  vg := mixedOneThreeBase1_vg
  wa := mixedOneThreeBase1_wa
  completion := mixedOneThreeBase1_completion

end FD56
