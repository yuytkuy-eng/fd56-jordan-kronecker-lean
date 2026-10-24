/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedOneThreeBase4
import FD56.Hilbert.UniformCubicCompletion
import FD56.Hilbert.FiniteMatrixEvaluation

/-! A polynomial completion for the three-high-column base with 4 low columns. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

variable {K : Type*} [Field K] [CharZero K]

def mixedOneThreeBase4Selector : Matrix (Fin 10) (Fin 3) K[X] :=
  ![![1,0,0],
    ![0,1,0],
    ![0,0,1],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0]]

def mixedOneThreeBase4Right : Matrix (Fin 7) (Fin 10) K[X] :=
  ![![0,0,0,-1,0,0,-X^3,0,-X^6,-X^9],
    ![0,0,0,0,-1,0,0,-X^4,-2*X^6,2*X^7-2*X^9],
    ![0,0,0,0,0,-1,0,-X,-2*X^3-X^4,2*X^4+X^5-2*X^6-X^7],
    ![0,0,0,0,0,0,-1,0,-X^3,-X^6],
    ![0,0,0,0,0,0,0,-1,-2*X^2,2*X^3-2*X^5],
    ![0,0,0,0,0,0,0,0,-1,X-X^3],
    ![0,0,0,0,0,0,0,0,0,-1]]

def mixedOneThreeBase4Kernel : Matrix (Fin 3) (Fin 10) K[X] :=
  ![![0,2+X,-2*X^3,0,2*X^3+X^4,-2*X^6,0,X^8,0,0],
    ![16*X,21,-8+4*X-10*X^2-16*X^3,16*X^4,21*X^3,-8*X^3+4*X^4-10*X^5-16*X^6,16*X^7,-8*X^4+4*X^5-10*X^6+5*X^7,-16*X^6-16*X^8,16*X^7],
    ![8,-5,-4*X+2*X^2,8*X^3,-5*X^3,-4*X^4+2*X^5,8*X^6,-4*X^5+2*X^6-5*X^7,-8*X^7,8*X^8]]

def mixedOneThreeBase4CoordinateNumerator : Matrix (Fin 3) (Fin 3) K[X] :=
  ![![5+8*X+X^2+10*X^3,-X-X^3,2+2*X^2+2*X^4],
    ![8-4*X+2*X^2+20*X^3,-2*X^3,4*X^4],
    ![21+10*X,-2-X,4*X+2*X^2]]

def mixedOneThreeBase4Coordinates : Matrix (Fin 3) (Fin 3) K[X] :=
  C (1/16 : K) • mixedOneThreeBase4CoordinateNumerator

theorem mixedOneThreeBase4Coordinates_scaled :
    (16 : K[X]) • mixedOneThreeBase4Coordinates (K := K)=mixedOneThreeBase4CoordinateNumerator := by
  have h : (16 : K[X])*C (1/16 : K)=1 := by
    have hh := congrArg (Polynomial.C : K → K[X])
      (show (16 : K)*(1/16)=1 by norm_num)
    simpa only [map_mul,map_ofNat,map_one] using hh
  simp only [mixedOneThreeBase4Coordinates,smul_smul,h,one_smul]

omit [CharZero K] in
private theorem polynomial_matrix_smul_cancel {a b : Type*} (s : K[X]) (hs : s≠0)
    {A B : Matrix a b K[X]} (h : s • A=s • B) : A=B := by
  apply Matrix.ext
  intro i j
  exact mul_left_cancel₀ hs (congrArg (fun M : Matrix a b K[X] => M i j) h)

theorem mixedOneThreeBase4_gDegree :
    ∀ i j, (mixedOneThreeBase4 (K := K) i j).natDegree≤(if j.val<4 then 1 else 2)+2 := by
  intro i j
  fin_cases i <;> fin_cases j
  · change (X^3 : K[X]).natDegree≤3
    exact (by norm_num)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
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
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
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
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
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
  · change (-1 : K[X]).natDegree≤3
    exact (by rw [natDegree_neg]; exact (by norm_num))
  · change (0 : K[X]).natDegree≤3
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
  · change (-1 : K[X]).natDegree≤3
    exact (by rw [natDegree_neg]; exact (by norm_num))
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
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (-1 : K[X]).natDegree≤3
    exact (by rw [natDegree_neg]; exact (by norm_num))
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (X : K[X]).natDegree≤4
    exact (by norm_num)
  · change (X^4 : K[X]).natDegree≤4
    exact (by norm_num)
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (-1 : K[X]).natDegree≤3
    exact (by rw [natDegree_neg]; exact (by norm_num))
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (X^3 : K[X]).natDegree≤4
    exact (by norm_num)
  · change (X^4 : K[X]).natDegree≤4
    exact (by norm_num)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (-1 : K[X]).natDegree≤4
    exact (by rw [natDegree_neg]; exact (by norm_num))
  · change (X^2+X^2 : K[X]).natDegree≤4
    exact (natDegree_add_le_of_degree_le (by norm_num) (by norm_num))
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (-1 : K[X]).natDegree≤4
    exact (by rw [natDegree_neg]; exact (by norm_num))
  · change (-X+X^3 : K[X]).natDegree≤4
    exact (natDegree_add_le_of_degree_le (by rw [natDegree_neg]; exact (by norm_num)) (by norm_num))
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
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

theorem mixedOneThreeBase4_sDegree : DegreeBound (mixedOneThreeBase4Selector (K := K)) 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [mixedOneThreeBase4Selector,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine]

theorem mixedOneThreeBase4_vDegree : DegreeBound (mixedOneThreeBase4Kernel (K := K)) 8 := by
  intro i j
  fin_cases i <;> fin_cases j
  · change (0 : K[X]).natDegree≤8
    exact (by simp)
  · change (2+X : K[X]).natDegree≤8
    exact (natDegree_add_le_of_degree_le (by norm_num) (by norm_num))
  · change (-2*X^3 : K[X]).natDegree≤8
    exact (natDegree_mul_le.trans (by norm_num))
  · change (0 : K[X]).natDegree≤8
    exact (by simp)
  · change (2*X^3+X^4 : K[X]).natDegree≤8
    exact (natDegree_add_le_of_degree_le (natDegree_mul_le.trans (by norm_num)) (by norm_num))
  · change (-2*X^6 : K[X]).natDegree≤8
    exact (natDegree_mul_le.trans (by norm_num))
  · change (0 : K[X]).natDegree≤8
    exact (by simp)
  · change (X^8 : K[X]).natDegree≤8
    exact (by norm_num)
  · change (0 : K[X]).natDegree≤8
    exact (by simp)
  · change (0 : K[X]).natDegree≤8
    exact (by simp)
  · change (16*X : K[X]).natDegree≤8
    exact (natDegree_mul_le.trans (by norm_num))
  · change (21 : K[X]).natDegree≤8
    exact (by norm_num)
  · change (-8+4*X-10*X^2-16*X^3 : K[X]).natDegree≤8
    exact ((natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le (natDegree_add_le_of_degree_le (by rw [natDegree_neg]; exact (by norm_num)) (natDegree_mul_le.trans (by norm_num))) (natDegree_mul_le.trans (by norm_num)))) (natDegree_mul_le.trans (by norm_num))))
  · change (16*X^4 : K[X]).natDegree≤8
    exact (natDegree_mul_le.trans (by norm_num))
  · change (21*X^3 : K[X]).natDegree≤8
    exact (natDegree_mul_le.trans (by norm_num))
  · change (-8*X^3+4*X^4-10*X^5-16*X^6 : K[X]).natDegree≤8
    exact ((natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le (natDegree_add_le_of_degree_le (natDegree_mul_le.trans (by norm_num)) (natDegree_mul_le.trans (by norm_num))) (natDegree_mul_le.trans (by norm_num)))) (natDegree_mul_le.trans (by norm_num))))
  · change (16*X^7 : K[X]).natDegree≤8
    exact (natDegree_mul_le.trans (by norm_num))
  · change (-8*X^4+4*X^5-10*X^6+5*X^7 : K[X]).natDegree≤8
    exact (natDegree_add_le_of_degree_le ((natDegree_sub_le _ _).trans (max_le (natDegree_add_le_of_degree_le (natDegree_mul_le.trans (by norm_num)) (natDegree_mul_le.trans (by norm_num))) (natDegree_mul_le.trans (by norm_num)))) (natDegree_mul_le.trans (by norm_num)))
  · change (-16*X^6-16*X^8 : K[X]).natDegree≤8
    exact ((natDegree_sub_le _ _).trans (max_le (natDegree_mul_le.trans (by norm_num)) (natDegree_mul_le.trans (by norm_num))))
  · change (16*X^7 : K[X]).natDegree≤8
    exact (natDegree_mul_le.trans (by norm_num))
  · change (8 : K[X]).natDegree≤8
    exact (by norm_num)
  · change (-5 : K[X]).natDegree≤8
    exact (by rw [natDegree_neg]; exact (by norm_num))
  · change (-4*X+2*X^2 : K[X]).natDegree≤8
    exact (natDegree_add_le_of_degree_le (natDegree_mul_le.trans (by norm_num)) (natDegree_mul_le.trans (by norm_num)))
  · change (8*X^3 : K[X]).natDegree≤8
    exact (natDegree_mul_le.trans (by norm_num))
  · change (-5*X^3 : K[X]).natDegree≤8
    exact (natDegree_mul_le.trans (by norm_num))
  · change (-4*X^4+2*X^5 : K[X]).natDegree≤8
    exact (natDegree_add_le_of_degree_le (natDegree_mul_le.trans (by norm_num)) (natDegree_mul_le.trans (by norm_num)))
  · change (8*X^6 : K[X]).natDegree≤8
    exact (natDegree_mul_le.trans (by norm_num))
  · change (-4*X^5+2*X^6-5*X^7 : K[X]).natDegree≤8
    exact ((natDegree_sub_le _ _).trans (max_le (natDegree_add_le_of_degree_le (natDegree_mul_le.trans (by norm_num)) (natDegree_mul_le.trans (by norm_num))) (natDegree_mul_le.trans (by norm_num))))
  · change (-8*X^7 : K[X]).natDegree≤8
    exact (natDegree_mul_le.trans (by norm_num))
  · change (8*X^8 : K[X]).natDegree≤8
    exact (natDegree_mul_le.trans (by norm_num))

theorem mixedOneThreeBase4_leading : Function.Injective (Matrix.mulVec
    (fun x j => (mixedOneThreeBase4Kernel (K := K) j x).coeff 8)) := by
  intro a b h
  have h7 : a 0=b 0 := by
    have hh := congrFun h (7 : Fin 10)
    norm_num [mixedOneThreeBase4Kernel,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  have h8 : (-16)*a 1=(-16)*b 1 := by
    have hh := congrFun h (8 : Fin 10)
    norm_num [mixedOneThreeBase4Kernel,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  have h9 : (8)*a 2=(8)*b 2 := by
    have hh := congrFun h (9 : Fin 10)
    norm_num [mixedOneThreeBase4Kernel,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  funext j
  fin_cases j
  · linear_combination (norm := ring1!) h7
  · linear_combination (norm := ring1!) (-1/16 : K)*h8
  · linear_combination (norm := ring1!) (1/8 : K)*h9

theorem mixedOneThreeBase4_jet : Function.Injective (Matrix.mulVec
    (fun (ij : Fin 3 × Fin 3) (k : Fin 3) =>
      (mixedOneThreeBase4Coordinates (K := K) ij.1 ij.2).coeff (2-k.val))) := by
  intro a b h
  have h0 : (1/16 : K)*a 0 + (1/2 : K)*a 1 + (5/16 : K)*a 2=(1/16 : K)*b 0 + (1/2 : K)*b 1 + (5/16 : K)*b 2 := by
    have hh := congrFun h ((0,0) : Fin 3 × Fin 3)
    norm_num [mixedOneThreeBase4Coordinates,mixedOneThreeBase4CoordinateNumerator,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,Matrix.smul_apply,smul_eq_mul,coeff_C_mul,coeff_add,coeff_sub,
      coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  have h1 : (-1/16 : K)*a 1=(-1/16 : K)*b 1 := by
    have hh := congrFun h ((0,1) : Fin 3 × Fin 3)
    norm_num [mixedOneThreeBase4Coordinates,mixedOneThreeBase4CoordinateNumerator,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,Matrix.smul_apply,smul_eq_mul,coeff_C_mul,coeff_add,coeff_sub,
      coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  have h2 : (1/8 : K)*a 0 + (1/8 : K)*a 2=(1/8 : K)*b 0 + (1/8 : K)*b 2 := by
    have hh := congrFun h ((0,2) : Fin 3 × Fin 3)
    norm_num [mixedOneThreeBase4Coordinates,mixedOneThreeBase4CoordinateNumerator,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,Matrix.smul_apply,smul_eq_mul,coeff_C_mul,coeff_add,coeff_sub,
      coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  funext j
  fin_cases j
  · linear_combination (norm := ring1!) (-4)*h0 + (-32)*h1 + (10)*h2
  · linear_combination (norm := ring1!) (-16)*h1
  · linear_combination (norm := ring1!) (4)*h0 + (32)*h1 + (-2)*h2

private theorem mixedOneThreeBase4_rg_row0 (j : Fin 7) :
    (mixedOneThreeBase4Right (K := K)*mixedOneThreeBase4 : Matrix (Fin 7) (Fin 7) K[X]) 0 j=
      ((1 : Matrix (Fin 7) (Fin 7) K[X]) : Matrix (Fin 7) (Fin 7) K[X]) 0 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase4,mixedOneThreeBase4Right,mixedOneThreeBase4Selector,mixedOneThreeBase4Kernel,mixedOneThreeBase4CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase4_rg_row1 (j : Fin 7) :
    (mixedOneThreeBase4Right (K := K)*mixedOneThreeBase4 : Matrix (Fin 7) (Fin 7) K[X]) 1 j=
      ((1 : Matrix (Fin 7) (Fin 7) K[X]) : Matrix (Fin 7) (Fin 7) K[X]) 1 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase4,mixedOneThreeBase4Right,mixedOneThreeBase4Selector,mixedOneThreeBase4Kernel,mixedOneThreeBase4CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase4_rg_row2 (j : Fin 7) :
    (mixedOneThreeBase4Right (K := K)*mixedOneThreeBase4 : Matrix (Fin 7) (Fin 7) K[X]) 2 j=
      ((1 : Matrix (Fin 7) (Fin 7) K[X]) : Matrix (Fin 7) (Fin 7) K[X]) 2 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase4,mixedOneThreeBase4Right,mixedOneThreeBase4Selector,mixedOneThreeBase4Kernel,mixedOneThreeBase4CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase4_rg_row3 (j : Fin 7) :
    (mixedOneThreeBase4Right (K := K)*mixedOneThreeBase4 : Matrix (Fin 7) (Fin 7) K[X]) 3 j=
      ((1 : Matrix (Fin 7) (Fin 7) K[X]) : Matrix (Fin 7) (Fin 7) K[X]) 3 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase4,mixedOneThreeBase4Right,mixedOneThreeBase4Selector,mixedOneThreeBase4Kernel,mixedOneThreeBase4CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase4_rg_row4 (j : Fin 7) :
    (mixedOneThreeBase4Right (K := K)*mixedOneThreeBase4 : Matrix (Fin 7) (Fin 7) K[X]) 4 j=
      ((1 : Matrix (Fin 7) (Fin 7) K[X]) : Matrix (Fin 7) (Fin 7) K[X]) 4 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase4,mixedOneThreeBase4Right,mixedOneThreeBase4Selector,mixedOneThreeBase4Kernel,mixedOneThreeBase4CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase4_rg_row5 (j : Fin 7) :
    (mixedOneThreeBase4Right (K := K)*mixedOneThreeBase4 : Matrix (Fin 7) (Fin 7) K[X]) 5 j=
      ((1 : Matrix (Fin 7) (Fin 7) K[X]) : Matrix (Fin 7) (Fin 7) K[X]) 5 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase4,mixedOneThreeBase4Right,mixedOneThreeBase4Selector,mixedOneThreeBase4Kernel,mixedOneThreeBase4CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase4_rg_row6 (j : Fin 7) :
    (mixedOneThreeBase4Right (K := K)*mixedOneThreeBase4 : Matrix (Fin 7) (Fin 7) K[X]) 6 j=
      ((1 : Matrix (Fin 7) (Fin 7) K[X]) : Matrix (Fin 7) (Fin 7) K[X]) 6 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase4,mixedOneThreeBase4Right,mixedOneThreeBase4Selector,mixedOneThreeBase4Kernel,mixedOneThreeBase4CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

theorem mixedOneThreeBase4_rg :
    mixedOneThreeBase4Right (K := K)*mixedOneThreeBase4=(1 : Matrix (Fin 7) (Fin 7) K[X]) := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact mixedOneThreeBase4_rg_row0 j
  · exact mixedOneThreeBase4_rg_row1 j
  · exact mixedOneThreeBase4_rg_row2 j
  · exact mixedOneThreeBase4_rg_row3 j
  · exact mixedOneThreeBase4_rg_row4 j
  · exact mixedOneThreeBase4_rg_row5 j
  · exact mixedOneThreeBase4_rg_row6 j

private theorem mixedOneThreeBase4_rs_row0 (j : Fin 3) :
    (mixedOneThreeBase4Right (K := K)*mixedOneThreeBase4Selector : Matrix (Fin 7) (Fin 3) K[X]) 0 j=
      ((0 : Matrix (Fin 7) (Fin 3) K[X]) : Matrix (Fin 7) (Fin 3) K[X]) 0 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase4,mixedOneThreeBase4Right,mixedOneThreeBase4Selector,mixedOneThreeBase4Kernel,mixedOneThreeBase4CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase4_rs_row1 (j : Fin 3) :
    (mixedOneThreeBase4Right (K := K)*mixedOneThreeBase4Selector : Matrix (Fin 7) (Fin 3) K[X]) 1 j=
      ((0 : Matrix (Fin 7) (Fin 3) K[X]) : Matrix (Fin 7) (Fin 3) K[X]) 1 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase4,mixedOneThreeBase4Right,mixedOneThreeBase4Selector,mixedOneThreeBase4Kernel,mixedOneThreeBase4CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase4_rs_row2 (j : Fin 3) :
    (mixedOneThreeBase4Right (K := K)*mixedOneThreeBase4Selector : Matrix (Fin 7) (Fin 3) K[X]) 2 j=
      ((0 : Matrix (Fin 7) (Fin 3) K[X]) : Matrix (Fin 7) (Fin 3) K[X]) 2 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase4,mixedOneThreeBase4Right,mixedOneThreeBase4Selector,mixedOneThreeBase4Kernel,mixedOneThreeBase4CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase4_rs_row3 (j : Fin 3) :
    (mixedOneThreeBase4Right (K := K)*mixedOneThreeBase4Selector : Matrix (Fin 7) (Fin 3) K[X]) 3 j=
      ((0 : Matrix (Fin 7) (Fin 3) K[X]) : Matrix (Fin 7) (Fin 3) K[X]) 3 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase4,mixedOneThreeBase4Right,mixedOneThreeBase4Selector,mixedOneThreeBase4Kernel,mixedOneThreeBase4CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase4_rs_row4 (j : Fin 3) :
    (mixedOneThreeBase4Right (K := K)*mixedOneThreeBase4Selector : Matrix (Fin 7) (Fin 3) K[X]) 4 j=
      ((0 : Matrix (Fin 7) (Fin 3) K[X]) : Matrix (Fin 7) (Fin 3) K[X]) 4 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase4,mixedOneThreeBase4Right,mixedOneThreeBase4Selector,mixedOneThreeBase4Kernel,mixedOneThreeBase4CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase4_rs_row5 (j : Fin 3) :
    (mixedOneThreeBase4Right (K := K)*mixedOneThreeBase4Selector : Matrix (Fin 7) (Fin 3) K[X]) 5 j=
      ((0 : Matrix (Fin 7) (Fin 3) K[X]) : Matrix (Fin 7) (Fin 3) K[X]) 5 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase4,mixedOneThreeBase4Right,mixedOneThreeBase4Selector,mixedOneThreeBase4Kernel,mixedOneThreeBase4CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase4_rs_row6 (j : Fin 3) :
    (mixedOneThreeBase4Right (K := K)*mixedOneThreeBase4Selector : Matrix (Fin 7) (Fin 3) K[X]) 6 j=
      ((0 : Matrix (Fin 7) (Fin 3) K[X]) : Matrix (Fin 7) (Fin 3) K[X]) 6 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase4,mixedOneThreeBase4Right,mixedOneThreeBase4Selector,mixedOneThreeBase4Kernel,mixedOneThreeBase4CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

theorem mixedOneThreeBase4_rs :
    mixedOneThreeBase4Right (K := K)*mixedOneThreeBase4Selector=(0 : Matrix (Fin 7) (Fin 3) K[X]) := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact mixedOneThreeBase4_rs_row0 j
  · exact mixedOneThreeBase4_rs_row1 j
  · exact mixedOneThreeBase4_rs_row2 j
  · exact mixedOneThreeBase4_rs_row3 j
  · exact mixedOneThreeBase4_rs_row4 j
  · exact mixedOneThreeBase4_rs_row5 j
  · exact mixedOneThreeBase4_rs_row6 j

private theorem mixedOneThreeBase4_vg_row0 (j : Fin 7) :
    (mixedOneThreeBase4Kernel (K := K)*mixedOneThreeBase4 : Matrix (Fin 3) (Fin 7) K[X]) 0 j=
      ((0 : Matrix (Fin 3) (Fin 7) K[X]) : Matrix (Fin 3) (Fin 7) K[X]) 0 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase4,mixedOneThreeBase4Right,mixedOneThreeBase4Selector,mixedOneThreeBase4Kernel,mixedOneThreeBase4CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase4_vg_row1 (j : Fin 7) :
    (mixedOneThreeBase4Kernel (K := K)*mixedOneThreeBase4 : Matrix (Fin 3) (Fin 7) K[X]) 1 j=
      ((0 : Matrix (Fin 3) (Fin 7) K[X]) : Matrix (Fin 3) (Fin 7) K[X]) 1 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase4,mixedOneThreeBase4Right,mixedOneThreeBase4Selector,mixedOneThreeBase4Kernel,mixedOneThreeBase4CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase4_vg_row2 (j : Fin 7) :
    (mixedOneThreeBase4Kernel (K := K)*mixedOneThreeBase4 : Matrix (Fin 3) (Fin 7) K[X]) 2 j=
      ((0 : Matrix (Fin 3) (Fin 7) K[X]) : Matrix (Fin 3) (Fin 7) K[X]) 2 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase4,mixedOneThreeBase4Right,mixedOneThreeBase4Selector,mixedOneThreeBase4Kernel,mixedOneThreeBase4CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

theorem mixedOneThreeBase4_vg :
    mixedOneThreeBase4Kernel (K := K)*mixedOneThreeBase4=(0 : Matrix (Fin 3) (Fin 7) K[X]) := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact mixedOneThreeBase4_vg_row0 j
  · exact mixedOneThreeBase4_vg_row1 j
  · exact mixedOneThreeBase4_vg_row2 j

private theorem mixedOneThreeBase4_wa_row0 (j : Fin 3) :
    (mixedOneThreeBase4CoordinateNumerator (K := K)*(mixedOneThreeBase4Kernel*mixedOneThreeBase4Selector) : Matrix (Fin 3) (Fin 3) K[X]) 0 j=
      ((16 : K[X]) • (1 : Matrix (Fin 3) (Fin 3) K[X]) : Matrix (Fin 3) (Fin 3) K[X]) 0 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase4,mixedOneThreeBase4Right,mixedOneThreeBase4Selector,mixedOneThreeBase4Kernel,mixedOneThreeBase4CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase4_wa_row1 (j : Fin 3) :
    (mixedOneThreeBase4CoordinateNumerator (K := K)*(mixedOneThreeBase4Kernel*mixedOneThreeBase4Selector) : Matrix (Fin 3) (Fin 3) K[X]) 1 j=
      ((16 : K[X]) • (1 : Matrix (Fin 3) (Fin 3) K[X]) : Matrix (Fin 3) (Fin 3) K[X]) 1 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase4,mixedOneThreeBase4Right,mixedOneThreeBase4Selector,mixedOneThreeBase4Kernel,mixedOneThreeBase4CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase4_wa_row2 (j : Fin 3) :
    (mixedOneThreeBase4CoordinateNumerator (K := K)*(mixedOneThreeBase4Kernel*mixedOneThreeBase4Selector) : Matrix (Fin 3) (Fin 3) K[X]) 2 j=
      ((16 : K[X]) • (1 : Matrix (Fin 3) (Fin 3) K[X]) : Matrix (Fin 3) (Fin 3) K[X]) 2 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase4,mixedOneThreeBase4Right,mixedOneThreeBase4Selector,mixedOneThreeBase4Kernel,mixedOneThreeBase4CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

theorem mixedOneThreeBase4_wa :
    mixedOneThreeBase4Coordinates (K := K)*(mixedOneThreeBase4Kernel*mixedOneThreeBase4Selector)=(1 : Matrix (Fin 3) (Fin 3) K[X]) := by
  apply polynomial_matrix_smul_cancel 16 (by norm_num)
  rw [← Matrix.smul_mul,mixedOneThreeBase4Coordinates_scaled]
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact mixedOneThreeBase4_wa_row0 j
  · exact mixedOneThreeBase4_wa_row1 j
  · exact mixedOneThreeBase4_wa_row2 j

theorem mixedOneThreeBase4_completion :
    mixedOneThreeBase4 (K := K)*mixedOneThreeBase4Right+mixedOneThreeBase4Selector*mixedOneThreeBase4Coordinates*mixedOneThreeBase4Kernel=(1 : Matrix (Fin 10) (Fin 10) K[X]) := by
  exact polynomial_completion_of_left_inverse mixedOneThreeBase4 mixedOneThreeBase4Selector mixedOneThreeBase4Right
    mixedOneThreeBase4Kernel mixedOneThreeBase4Coordinates (by decide) mixedOneThreeBase4_rg mixedOneThreeBase4_rs
    mixedOneThreeBase4_vg mixedOneThreeBase4_wa

def mixedOneThreeBase4Completion :
    UniformCubicCompletion (m := Fin 10) (fun j : Fin 7 => if j.val<4 then 1 else 2)
      8 (mixedOneThreeBase4Coordinates (K := K)) where
  G := mixedOneThreeBase4
  S := mixedOneThreeBase4Selector
  R := mixedOneThreeBase4Right
  V := mixedOneThreeBase4Kernel
  gDegree := mixedOneThreeBase4_gDegree
  sDegree := mixedOneThreeBase4_sDegree
  vDegree := mixedOneThreeBase4_vDegree
  leading := mixedOneThreeBase4_leading
  rg := mixedOneThreeBase4_rg
  rs := mixedOneThreeBase4_rs
  vg := mixedOneThreeBase4_vg
  wa := mixedOneThreeBase4_wa
  completion := mixedOneThreeBase4_completion

end FD56
