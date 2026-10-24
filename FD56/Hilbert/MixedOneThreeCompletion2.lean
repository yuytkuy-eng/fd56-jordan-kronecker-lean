/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedOneThreeBase2
import FD56.Hilbert.UniformCubicCompletion
import FD56.Hilbert.FiniteMatrixEvaluation

/-! A polynomial completion for the three-high-column base with 2 low columns. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

variable {K : Type*} [Field K] [CharZero K]

def mixedOneThreeBase2Selector : Matrix (Fin 8) (Fin 3) K[X] :=
  ![![1,0,0],
    ![0,1,0],
    ![0,0,1],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0]]

def mixedOneThreeBase2Right : Matrix (Fin 5) (Fin 8) K[X] :=
  ![![0,0,0,-1,0,-1,-X^3-X^4,X^3-X^5-2*X^6-X^7],
    ![0,0,0,0,-1,0,-1-X,-X^2-2*X^3-2*X^4],
    ![0,0,0,0,0,-1,-X^3,X^3-X^5-X^6],
    ![0,0,0,0,0,0,-1,-X^2-X^3],
    ![0,0,0,0,0,0,0,-1]]

def mixedOneThreeBase2Kernel : Matrix (Fin 3) (Fin 8) K[X] :=
  ![![-1-3*X-5*X^2,-X+3*X^2,4+8*X+5*X^2,-X^3-3*X^4-5*X^5,-X^4+3*X^5,-X^3+X^4+3*X^5+5*X^6,-X^4+2*X^5+2*X^6,0],
    ![1+3*X+X^2,1-X-X^2,-4-4*X-X^2,X^3+3*X^4+X^5,X^3-X^4-X^5,X^3-X^4-3*X^5-X^6,X^3-2*X^5,X^5],
    ![-1-X-X^2,X^2,2+2*X+X^2,-X^3-X^4-X^5,X^5,-X^3+X^4+X^5+X^6,X^5,X^6]]

def mixedOneThreeBase2CoordinateNumerator : Matrix (Fin 3) (Fin 3) K[X] :=
  ![![2+X^2+X^3,2*X+3*X^3+2*X^4,-4-X^2+2*X^3+2*X^4],
    ![2,2+4*X,4*X],
    ![1+X^3,X-X^2+X^3+2*X^4,-1-X-X^2+2*X^4]]

def mixedOneThreeBase2Coordinates : Matrix (Fin 3) (Fin 3) K[X] :=
  C (1/2 : K) • mixedOneThreeBase2CoordinateNumerator

theorem mixedOneThreeBase2Coordinates_scaled :
    (2 : K[X]) • mixedOneThreeBase2Coordinates (K := K)=mixedOneThreeBase2CoordinateNumerator := by
  have h : (2 : K[X])*C (1/2 : K)=1 := by
    have hh := congrArg (Polynomial.C : K → K[X])
      (show (2 : K)*(1/2)=1 by norm_num)
    simpa only [map_mul,map_ofNat,map_one] using hh
  simp only [mixedOneThreeBase2Coordinates,smul_smul,h,one_smul]

omit [CharZero K] in
private theorem polynomial_matrix_smul_cancel {a b : Type*} (s : K[X]) (hs : s≠0)
    {A B : Matrix a b K[X]} (h : s • A=s • B) : A=B := by
  apply Matrix.ext
  intro i j
  exact mul_left_cancel₀ hs (congrArg (fun M : Matrix a b K[X] => M i j) h)

theorem mixedOneThreeBase2_gDegree :
    ∀ i j, (mixedOneThreeBase2 (K := K) i j).natDegree≤(if j.val<2 then 1 else 2)+2 := by
  intro i j
  fin_cases i <;> fin_cases j
  · change (X^3 : K[X]).natDegree≤3
    exact (by norm_num)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
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
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (X^4 : K[X]).natDegree≤4
    exact (by norm_num)
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (-1 : K[X]).natDegree≤3
    exact (by rw [natDegree_neg]; exact (by norm_num))
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (1 : K[X]).natDegree≤4
    exact (by norm_num)
  · change (X^4 : K[X]).natDegree≤4
    exact (by norm_num)
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (-1 : K[X]).natDegree≤3
    exact (by rw [natDegree_neg]; exact (by norm_num))
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (1+X : K[X]).natDegree≤4
    exact (natDegree_add_le_of_degree_le (by norm_num) (by norm_num))
  · change (X^4 : K[X]).natDegree≤4
    exact (by norm_num)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (-1 : K[X]).natDegree≤4
    exact (by rw [natDegree_neg]; exact (by norm_num))
  · change (X^3 : K[X]).natDegree≤4
    exact (by norm_num)
  · change (-X^3 : K[X]).natDegree≤4
    exact (by rw [natDegree_neg]; exact (by norm_num))
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (-1 : K[X]).natDegree≤4
    exact (by rw [natDegree_neg]; exact (by norm_num))
  · change (X^2+X^3 : K[X]).natDegree≤4
    exact (natDegree_add_le_of_degree_le (by norm_num) (by norm_num))
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (-1 : K[X]).natDegree≤4
    exact (by rw [natDegree_neg]; exact (by norm_num))

theorem mixedOneThreeBase2_sDegree : DegreeBound (mixedOneThreeBase2Selector (K := K)) 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [mixedOneThreeBase2Selector,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine]

theorem mixedOneThreeBase2_vDegree : DegreeBound (mixedOneThreeBase2Kernel (K := K)) 6 := by
  intro i j
  fin_cases i <;> fin_cases j
  · change (-1-3*X-5*X^2 : K[X]).natDegree≤6
    exact ((natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le (by rw [natDegree_neg]; exact (by norm_num)) (natDegree_mul_le.trans (by norm_num)))) (natDegree_mul_le.trans (by norm_num))))
  · change (-X+3*X^2 : K[X]).natDegree≤6
    exact (natDegree_add_le_of_degree_le (by rw [natDegree_neg]; exact (by norm_num)) (natDegree_mul_le.trans (by norm_num)))
  · change (4+8*X+5*X^2 : K[X]).natDegree≤6
    exact (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (by norm_num) (natDegree_mul_le.trans (by norm_num))) (natDegree_mul_le.trans (by norm_num)))
  · change (-X^3-3*X^4-5*X^5 : K[X]).natDegree≤6
    exact ((natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le (by rw [natDegree_neg]; exact (by norm_num)) (natDegree_mul_le.trans (by norm_num)))) (natDegree_mul_le.trans (by norm_num))))
  · change (-X^4+3*X^5 : K[X]).natDegree≤6
    exact (natDegree_add_le_of_degree_le (by rw [natDegree_neg]; exact (by norm_num)) (natDegree_mul_le.trans (by norm_num)))
  · change (-X^3+X^4+3*X^5+5*X^6 : K[X]).natDegree≤6
    exact (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (by rw [natDegree_neg]; exact (by norm_num)) (by norm_num)) (natDegree_mul_le.trans (by norm_num))) (natDegree_mul_le.trans (by norm_num)))
  · change (-X^4+2*X^5+2*X^6 : K[X]).natDegree≤6
    exact (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (by rw [natDegree_neg]; exact (by norm_num)) (natDegree_mul_le.trans (by norm_num))) (natDegree_mul_le.trans (by norm_num)))
  · change (0 : K[X]).natDegree≤6
    exact (by simp)
  · change (1+3*X+X^2 : K[X]).natDegree≤6
    exact (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (by norm_num) (natDegree_mul_le.trans (by norm_num))) (by norm_num))
  · change (1-X-X^2 : K[X]).natDegree≤6
    exact ((natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le (by norm_num) (by norm_num))) (by norm_num)))
  · change (-4-4*X-X^2 : K[X]).natDegree≤6
    exact ((natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le (by rw [natDegree_neg]; exact (by norm_num)) (natDegree_mul_le.trans (by norm_num)))) (by norm_num)))
  · change (X^3+3*X^4+X^5 : K[X]).natDegree≤6
    exact (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (by norm_num) (natDegree_mul_le.trans (by norm_num))) (by norm_num))
  · change (X^3-X^4-X^5 : K[X]).natDegree≤6
    exact ((natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le (by norm_num) (by norm_num))) (by norm_num)))
  · change (X^3-X^4-3*X^5-X^6 : K[X]).natDegree≤6
    exact ((natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le (by norm_num) (by norm_num))) (natDegree_mul_le.trans (by norm_num)))) (by norm_num)))
  · change (X^3-2*X^5 : K[X]).natDegree≤6
    exact ((natDegree_sub_le _ _).trans (max_le (by norm_num) (natDegree_mul_le.trans (by norm_num))))
  · change (X^5 : K[X]).natDegree≤6
    exact (by norm_num)
  · change (-1-X-X^2 : K[X]).natDegree≤6
    exact ((natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le (by rw [natDegree_neg]; exact (by norm_num)) (by norm_num))) (by norm_num)))
  · change (X^2 : K[X]).natDegree≤6
    exact (by norm_num)
  · change (2+2*X+X^2 : K[X]).natDegree≤6
    exact (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (by norm_num) (natDegree_mul_le.trans (by norm_num))) (by norm_num))
  · change (-X^3-X^4-X^5 : K[X]).natDegree≤6
    exact ((natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le (by rw [natDegree_neg]; exact (by norm_num)) (by norm_num))) (by norm_num)))
  · change (X^5 : K[X]).natDegree≤6
    exact (by norm_num)
  · change (-X^3+X^4+X^5+X^6 : K[X]).natDegree≤6
    exact (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (by rw [natDegree_neg]; exact (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  · change (X^5 : K[X]).natDegree≤6
    exact (by norm_num)
  · change (X^6 : K[X]).natDegree≤6
    exact (by norm_num)

theorem mixedOneThreeBase2_leading : Function.Injective (Matrix.mulVec
    (fun x j => (mixedOneThreeBase2Kernel (K := K) j x).coeff 6)) := by
  intro a b h
  have h5 : (5)*a 0 + -a 1 + a 2=(5)*b 0 + -b 1 + b 2 := by
    have hh := congrFun h (5 : Fin 8)
    norm_num [mixedOneThreeBase2Kernel,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  have h6 : (2)*a 0=(2)*b 0 := by
    have hh := congrFun h (6 : Fin 8)
    norm_num [mixedOneThreeBase2Kernel,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  have h7 : a 2=b 2 := by
    have hh := congrFun h (7 : Fin 8)
    norm_num [mixedOneThreeBase2Kernel,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  funext j
  fin_cases j
  · linear_combination (norm := ring1!) (1/2 : K)*h6
  · linear_combination (norm := ring1!) -h5 + (5/2 : K)*h6 + h7
  · linear_combination (norm := ring1!) h7

theorem mixedOneThreeBase2_jet : Function.Injective (Matrix.mulVec
    (fun (ij : Fin 3 × Fin 3) (k : Fin 3) =>
      (mixedOneThreeBase2Coordinates (K := K) ij.1 ij.2).coeff (2-k.val))) := by
  intro a b h
  have h0 : (1/2 : K)*a 0 + a 2=(1/2 : K)*b 0 + b 2 := by
    have hh := congrFun h ((0,0) : Fin 3 × Fin 3)
    norm_num [mixedOneThreeBase2Coordinates,mixedOneThreeBase2CoordinateNumerator,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,Matrix.smul_apply,smul_eq_mul,coeff_C_mul,coeff_add,coeff_sub,
      coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  have h1 : a 1=b 1 := by
    have hh := congrFun h ((0,1) : Fin 3 × Fin 3)
    norm_num [mixedOneThreeBase2Coordinates,mixedOneThreeBase2CoordinateNumerator,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,Matrix.smul_apply,smul_eq_mul,coeff_C_mul,coeff_add,coeff_sub,
      coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  have h2 : (-1/2 : K)*a 0 + (-2)*a 2=(-1/2 : K)*b 0 + (-2)*b 2 := by
    have hh := congrFun h ((0,2) : Fin 3 × Fin 3)
    norm_num [mixedOneThreeBase2Coordinates,mixedOneThreeBase2CoordinateNumerator,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,Matrix.smul_apply,smul_eq_mul,coeff_C_mul,coeff_add,coeff_sub,
      coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  funext j
  fin_cases j
  · linear_combination (norm := ring1!) (4)*h0 + (2)*h2
  · linear_combination (norm := ring1!) h1
  · linear_combination (norm := ring1!) -h0 + -h2

private theorem mixedOneThreeBase2_rg_row0 (j : Fin 5) :
    (mixedOneThreeBase2Right (K := K)*mixedOneThreeBase2 : Matrix (Fin 5) (Fin 5) K[X]) 0 j=
      ((1 : Matrix (Fin 5) (Fin 5) K[X]) : Matrix (Fin 5) (Fin 5) K[X]) 0 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase2,mixedOneThreeBase2Right,mixedOneThreeBase2Selector,mixedOneThreeBase2Kernel,mixedOneThreeBase2CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase2_rg_row1 (j : Fin 5) :
    (mixedOneThreeBase2Right (K := K)*mixedOneThreeBase2 : Matrix (Fin 5) (Fin 5) K[X]) 1 j=
      ((1 : Matrix (Fin 5) (Fin 5) K[X]) : Matrix (Fin 5) (Fin 5) K[X]) 1 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase2,mixedOneThreeBase2Right,mixedOneThreeBase2Selector,mixedOneThreeBase2Kernel,mixedOneThreeBase2CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase2_rg_row2 (j : Fin 5) :
    (mixedOneThreeBase2Right (K := K)*mixedOneThreeBase2 : Matrix (Fin 5) (Fin 5) K[X]) 2 j=
      ((1 : Matrix (Fin 5) (Fin 5) K[X]) : Matrix (Fin 5) (Fin 5) K[X]) 2 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase2,mixedOneThreeBase2Right,mixedOneThreeBase2Selector,mixedOneThreeBase2Kernel,mixedOneThreeBase2CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase2_rg_row3 (j : Fin 5) :
    (mixedOneThreeBase2Right (K := K)*mixedOneThreeBase2 : Matrix (Fin 5) (Fin 5) K[X]) 3 j=
      ((1 : Matrix (Fin 5) (Fin 5) K[X]) : Matrix (Fin 5) (Fin 5) K[X]) 3 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase2,mixedOneThreeBase2Right,mixedOneThreeBase2Selector,mixedOneThreeBase2Kernel,mixedOneThreeBase2CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase2_rg_row4 (j : Fin 5) :
    (mixedOneThreeBase2Right (K := K)*mixedOneThreeBase2 : Matrix (Fin 5) (Fin 5) K[X]) 4 j=
      ((1 : Matrix (Fin 5) (Fin 5) K[X]) : Matrix (Fin 5) (Fin 5) K[X]) 4 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase2,mixedOneThreeBase2Right,mixedOneThreeBase2Selector,mixedOneThreeBase2Kernel,mixedOneThreeBase2CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

theorem mixedOneThreeBase2_rg :
    mixedOneThreeBase2Right (K := K)*mixedOneThreeBase2=(1 : Matrix (Fin 5) (Fin 5) K[X]) := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact mixedOneThreeBase2_rg_row0 j
  · exact mixedOneThreeBase2_rg_row1 j
  · exact mixedOneThreeBase2_rg_row2 j
  · exact mixedOneThreeBase2_rg_row3 j
  · exact mixedOneThreeBase2_rg_row4 j

private theorem mixedOneThreeBase2_rs_row0 (j : Fin 3) :
    (mixedOneThreeBase2Right (K := K)*mixedOneThreeBase2Selector : Matrix (Fin 5) (Fin 3) K[X]) 0 j=
      ((0 : Matrix (Fin 5) (Fin 3) K[X]) : Matrix (Fin 5) (Fin 3) K[X]) 0 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase2,mixedOneThreeBase2Right,mixedOneThreeBase2Selector,mixedOneThreeBase2Kernel,mixedOneThreeBase2CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase2_rs_row1 (j : Fin 3) :
    (mixedOneThreeBase2Right (K := K)*mixedOneThreeBase2Selector : Matrix (Fin 5) (Fin 3) K[X]) 1 j=
      ((0 : Matrix (Fin 5) (Fin 3) K[X]) : Matrix (Fin 5) (Fin 3) K[X]) 1 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase2,mixedOneThreeBase2Right,mixedOneThreeBase2Selector,mixedOneThreeBase2Kernel,mixedOneThreeBase2CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase2_rs_row2 (j : Fin 3) :
    (mixedOneThreeBase2Right (K := K)*mixedOneThreeBase2Selector : Matrix (Fin 5) (Fin 3) K[X]) 2 j=
      ((0 : Matrix (Fin 5) (Fin 3) K[X]) : Matrix (Fin 5) (Fin 3) K[X]) 2 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase2,mixedOneThreeBase2Right,mixedOneThreeBase2Selector,mixedOneThreeBase2Kernel,mixedOneThreeBase2CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase2_rs_row3 (j : Fin 3) :
    (mixedOneThreeBase2Right (K := K)*mixedOneThreeBase2Selector : Matrix (Fin 5) (Fin 3) K[X]) 3 j=
      ((0 : Matrix (Fin 5) (Fin 3) K[X]) : Matrix (Fin 5) (Fin 3) K[X]) 3 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase2,mixedOneThreeBase2Right,mixedOneThreeBase2Selector,mixedOneThreeBase2Kernel,mixedOneThreeBase2CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase2_rs_row4 (j : Fin 3) :
    (mixedOneThreeBase2Right (K := K)*mixedOneThreeBase2Selector : Matrix (Fin 5) (Fin 3) K[X]) 4 j=
      ((0 : Matrix (Fin 5) (Fin 3) K[X]) : Matrix (Fin 5) (Fin 3) K[X]) 4 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase2,mixedOneThreeBase2Right,mixedOneThreeBase2Selector,mixedOneThreeBase2Kernel,mixedOneThreeBase2CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

theorem mixedOneThreeBase2_rs :
    mixedOneThreeBase2Right (K := K)*mixedOneThreeBase2Selector=(0 : Matrix (Fin 5) (Fin 3) K[X]) := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact mixedOneThreeBase2_rs_row0 j
  · exact mixedOneThreeBase2_rs_row1 j
  · exact mixedOneThreeBase2_rs_row2 j
  · exact mixedOneThreeBase2_rs_row3 j
  · exact mixedOneThreeBase2_rs_row4 j

private theorem mixedOneThreeBase2_vg_row0 (j : Fin 5) :
    (mixedOneThreeBase2Kernel (K := K)*mixedOneThreeBase2 : Matrix (Fin 3) (Fin 5) K[X]) 0 j=
      ((0 : Matrix (Fin 3) (Fin 5) K[X]) : Matrix (Fin 3) (Fin 5) K[X]) 0 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase2,mixedOneThreeBase2Right,mixedOneThreeBase2Selector,mixedOneThreeBase2Kernel,mixedOneThreeBase2CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase2_vg_row1 (j : Fin 5) :
    (mixedOneThreeBase2Kernel (K := K)*mixedOneThreeBase2 : Matrix (Fin 3) (Fin 5) K[X]) 1 j=
      ((0 : Matrix (Fin 3) (Fin 5) K[X]) : Matrix (Fin 3) (Fin 5) K[X]) 1 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase2,mixedOneThreeBase2Right,mixedOneThreeBase2Selector,mixedOneThreeBase2Kernel,mixedOneThreeBase2CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase2_vg_row2 (j : Fin 5) :
    (mixedOneThreeBase2Kernel (K := K)*mixedOneThreeBase2 : Matrix (Fin 3) (Fin 5) K[X]) 2 j=
      ((0 : Matrix (Fin 3) (Fin 5) K[X]) : Matrix (Fin 3) (Fin 5) K[X]) 2 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase2,mixedOneThreeBase2Right,mixedOneThreeBase2Selector,mixedOneThreeBase2Kernel,mixedOneThreeBase2CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

theorem mixedOneThreeBase2_vg :
    mixedOneThreeBase2Kernel (K := K)*mixedOneThreeBase2=(0 : Matrix (Fin 3) (Fin 5) K[X]) := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact mixedOneThreeBase2_vg_row0 j
  · exact mixedOneThreeBase2_vg_row1 j
  · exact mixedOneThreeBase2_vg_row2 j

private theorem mixedOneThreeBase2_wa_row0 (j : Fin 3) :
    (mixedOneThreeBase2CoordinateNumerator (K := K)*(mixedOneThreeBase2Kernel*mixedOneThreeBase2Selector) : Matrix (Fin 3) (Fin 3) K[X]) 0 j=
      ((2 : K[X]) • (1 : Matrix (Fin 3) (Fin 3) K[X]) : Matrix (Fin 3) (Fin 3) K[X]) 0 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase2,mixedOneThreeBase2Right,mixedOneThreeBase2Selector,mixedOneThreeBase2Kernel,mixedOneThreeBase2CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase2_wa_row1 (j : Fin 3) :
    (mixedOneThreeBase2CoordinateNumerator (K := K)*(mixedOneThreeBase2Kernel*mixedOneThreeBase2Selector) : Matrix (Fin 3) (Fin 3) K[X]) 1 j=
      ((2 : K[X]) • (1 : Matrix (Fin 3) (Fin 3) K[X]) : Matrix (Fin 3) (Fin 3) K[X]) 1 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase2,mixedOneThreeBase2Right,mixedOneThreeBase2Selector,mixedOneThreeBase2Kernel,mixedOneThreeBase2CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase2_wa_row2 (j : Fin 3) :
    (mixedOneThreeBase2CoordinateNumerator (K := K)*(mixedOneThreeBase2Kernel*mixedOneThreeBase2Selector) : Matrix (Fin 3) (Fin 3) K[X]) 2 j=
      ((2 : K[X]) • (1 : Matrix (Fin 3) (Fin 3) K[X]) : Matrix (Fin 3) (Fin 3) K[X]) 2 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase2,mixedOneThreeBase2Right,mixedOneThreeBase2Selector,mixedOneThreeBase2Kernel,mixedOneThreeBase2CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

theorem mixedOneThreeBase2_wa :
    mixedOneThreeBase2Coordinates (K := K)*(mixedOneThreeBase2Kernel*mixedOneThreeBase2Selector)=(1 : Matrix (Fin 3) (Fin 3) K[X]) := by
  apply polynomial_matrix_smul_cancel 2 (by norm_num)
  rw [← Matrix.smul_mul,mixedOneThreeBase2Coordinates_scaled]
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact mixedOneThreeBase2_wa_row0 j
  · exact mixedOneThreeBase2_wa_row1 j
  · exact mixedOneThreeBase2_wa_row2 j

theorem mixedOneThreeBase2_completion :
    mixedOneThreeBase2 (K := K)*mixedOneThreeBase2Right+mixedOneThreeBase2Selector*mixedOneThreeBase2Coordinates*mixedOneThreeBase2Kernel=(1 : Matrix (Fin 8) (Fin 8) K[X]) := by
  exact polynomial_completion_of_left_inverse mixedOneThreeBase2 mixedOneThreeBase2Selector mixedOneThreeBase2Right
    mixedOneThreeBase2Kernel mixedOneThreeBase2Coordinates (by decide) mixedOneThreeBase2_rg mixedOneThreeBase2_rs
    mixedOneThreeBase2_vg mixedOneThreeBase2_wa

def mixedOneThreeBase2Completion :
    UniformCubicCompletion (m := Fin 8) (fun j : Fin 5 => if j.val<2 then 1 else 2)
      6 (mixedOneThreeBase2Coordinates (K := K)) where
  G := mixedOneThreeBase2
  S := mixedOneThreeBase2Selector
  R := mixedOneThreeBase2Right
  V := mixedOneThreeBase2Kernel
  gDegree := mixedOneThreeBase2_gDegree
  sDegree := mixedOneThreeBase2_sDegree
  vDegree := mixedOneThreeBase2_vDegree
  leading := mixedOneThreeBase2_leading
  rg := mixedOneThreeBase2_rg
  rs := mixedOneThreeBase2_rs
  vg := mixedOneThreeBase2_vg
  wa := mixedOneThreeBase2_wa
  completion := mixedOneThreeBase2_completion

end FD56
