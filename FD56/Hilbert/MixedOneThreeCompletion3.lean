/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedOneThreeBase3
import FD56.Hilbert.UniformCubicCompletion
import FD56.Hilbert.FiniteMatrixEvaluation

/-! A polynomial completion for the three-high-column base with 3 low columns. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

variable {K : Type*} [Field K] [CharZero K]

def mixedOneThreeBase3Selector : Matrix (Fin 9) (Fin 3) K[X] :=
  ![![1,0,0],
    ![0,1,0],
    ![0,0,1],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0]]

def mixedOneThreeBase3Right : Matrix (Fin 6) (Fin 9) K[X] :=
  ![![0,0,0,-1,0,0,-X^4,X^5-X^6,-2*X^6+X^8-X^9],
    ![0,0,0,0,-1,0,-2*X^2,2*X^3-3*X^4,-4*X^4+2*X^6-3*X^7],
    ![0,0,0,0,0,-1,-X^3,-X^2+X^4-X^5,-X^4-3*X^5+X^7-X^8],
    ![0,0,0,0,0,0,-1,X-X^2,-2*X^2+X^4-X^5],
    ![0,0,0,0,0,0,0,-1,-X^3],
    ![0,0,0,0,0,0,0,0,-1]]

def mixedOneThreeBase3Kernel : Matrix (Fin 3) (Fin 9) K[X] :=
  ![![-31+18*X,4+5*X+X^2,-16+28*X-18*X^2,-31*X^3+18*X^4,4*X^3+5*X^4+X^5,-16*X^3+28*X^4-18*X^5,8*X^5-6*X^6-X^7,-16*X^5+20*X^6,0],
    ![-13-6*X+10*X^2,2+5*X+3*X^2,-8+4*X+6*X^2-10*X^3,-13*X^3-6*X^4+10*X^5,2*X^3+5*X^4+3*X^5,-8*X^3+4*X^4+6*X^5-10*X^6,4*X^5+2*X^6-3*X^7,-8*X^5+10*X^7,0],
    ![27+34*X,12+15*X-17*X^2,-28+24*X-34*X^2,27*X^3+34*X^4,12*X^3+15*X^4-17*X^5,-28*X^3+24*X^4-34*X^5,24*X^5+2*X^6+17*X^7,-28*X^5,20*X^7]]

def mixedOneThreeBase3CoordinateNumerator : Matrix (Fin 3) (Fin 3) K[X] :=
  ![![-4+2*X+30*X^2-15*X^4+17*X^5,8-14*X-52*X^2+60*X^3-34*X^4,2*X^2-X^4+X^5],
    ![58+2*X-28*X^2+51*X^3,-130+146*X-102*X^2,4-2*X^2+3*X^3],
    ![21+47*X-15*X^3+17*X^4,-48-52*X+60*X^2-34*X^3,1+3*X-X^3+X^4]]

def mixedOneThreeBase3Coordinates : Matrix (Fin 3) (Fin 3) K[X] :=
  C (1/20 : K) • mixedOneThreeBase3CoordinateNumerator

theorem mixedOneThreeBase3Coordinates_scaled :
    (20 : K[X]) • mixedOneThreeBase3Coordinates (K := K)=mixedOneThreeBase3CoordinateNumerator := by
  have h : (20 : K[X])*C (1/20 : K)=1 := by
    have hh := congrArg (Polynomial.C : K → K[X])
      (show (20 : K)*(1/20)=1 by norm_num)
    simpa only [map_mul,map_ofNat,map_one] using hh
  simp only [mixedOneThreeBase3Coordinates,smul_smul,h,one_smul]

omit [CharZero K] in
private theorem polynomial_matrix_smul_cancel {a b : Type*} (s : K[X]) (hs : s≠0)
    {A B : Matrix a b K[X]} (h : s • A=s • B) : A=B := by
  apply Matrix.ext
  intro i j
  exact mul_left_cancel₀ hs (congrArg (fun M : Matrix a b K[X] => M i j) h)

theorem mixedOneThreeBase3_gDegree :
    ∀ i j, (mixedOneThreeBase3 (K := K) i j).natDegree≤(if j.val<3 then 1 else 2)+2 := by
  intro i j
  fin_cases i <;> fin_cases j
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
  · change (-1 : K[X]).natDegree≤3
    exact (by rw [natDegree_neg]; exact (by norm_num))
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (X^2+X^2 : K[X]).natDegree≤4
    exact (natDegree_add_le_of_degree_le (by norm_num) (by norm_num))
  · change (X^4 : K[X]).natDegree≤4
    exact (by norm_num)
  · change (0 : K[X]).natDegree≤4
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (-1 : K[X]).natDegree≤3
    exact (by rw [natDegree_neg]; exact (by norm_num))
  · change (X^3 : K[X]).natDegree≤4
    exact (by norm_num)
  · change (X^2 : K[X]).natDegree≤4
    exact (by norm_num)
  · change (X^4 : K[X]).natDegree≤4
    exact (by norm_num)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (0 : K[X]).natDegree≤3
    exact (by simp)
  · change (-1 : K[X]).natDegree≤4
    exact (by rw [natDegree_neg]; exact (by norm_num))
  · change (-X+X^2 : K[X]).natDegree≤4
    exact (natDegree_add_le_of_degree_le (by rw [natDegree_neg]; exact (by norm_num)) (by norm_num))
  · change (X^2+X^2 : K[X]).natDegree≤4
    exact (natDegree_add_le_of_degree_le (by norm_num) (by norm_num))
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
  · change (X^3 : K[X]).natDegree≤4
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
  · change (-1 : K[X]).natDegree≤4
    exact (by rw [natDegree_neg]; exact (by norm_num))

theorem mixedOneThreeBase3_sDegree : DegreeBound (mixedOneThreeBase3Selector (K := K)) 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [mixedOneThreeBase3Selector,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine]

theorem mixedOneThreeBase3_vDegree : DegreeBound (mixedOneThreeBase3Kernel (K := K)) 7 := by
  intro i j
  fin_cases i <;> fin_cases j
  · change (-31+18*X : K[X]).natDegree≤7
    exact (natDegree_add_le_of_degree_le (by rw [natDegree_neg]; exact (by norm_num)) (natDegree_mul_le.trans (by norm_num)))
  · change (4+5*X+X^2 : K[X]).natDegree≤7
    exact (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (by norm_num) (natDegree_mul_le.trans (by norm_num))) (by norm_num))
  · change (-16+28*X-18*X^2 : K[X]).natDegree≤7
    exact ((natDegree_sub_le _ _).trans (max_le (natDegree_add_le_of_degree_le (by rw [natDegree_neg]; exact (by norm_num)) (natDegree_mul_le.trans (by norm_num))) (natDegree_mul_le.trans (by norm_num))))
  · change (-31*X^3+18*X^4 : K[X]).natDegree≤7
    exact (natDegree_add_le_of_degree_le (natDegree_mul_le.trans (by norm_num)) (natDegree_mul_le.trans (by norm_num)))
  · change (4*X^3+5*X^4+X^5 : K[X]).natDegree≤7
    exact (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (natDegree_mul_le.trans (by norm_num)) (natDegree_mul_le.trans (by norm_num))) (by norm_num))
  · change (-16*X^3+28*X^4-18*X^5 : K[X]).natDegree≤7
    exact ((natDegree_sub_le _ _).trans (max_le (natDegree_add_le_of_degree_le (natDegree_mul_le.trans (by norm_num)) (natDegree_mul_le.trans (by norm_num))) (natDegree_mul_le.trans (by norm_num))))
  · change (8*X^5-6*X^6-X^7 : K[X]).natDegree≤7
    exact ((natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le (natDegree_mul_le.trans (by norm_num)) (natDegree_mul_le.trans (by norm_num)))) (by norm_num)))
  · change (-16*X^5+20*X^6 : K[X]).natDegree≤7
    exact (natDegree_add_le_of_degree_le (natDegree_mul_le.trans (by norm_num)) (natDegree_mul_le.trans (by norm_num)))
  · change (0 : K[X]).natDegree≤7
    exact (by simp)
  · change (-13-6*X+10*X^2 : K[X]).natDegree≤7
    exact (natDegree_add_le_of_degree_le ((natDegree_sub_le _ _).trans (max_le (by rw [natDegree_neg]; exact (by norm_num)) (natDegree_mul_le.trans (by norm_num)))) (natDegree_mul_le.trans (by norm_num)))
  · change (2+5*X+3*X^2 : K[X]).natDegree≤7
    exact (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (by norm_num) (natDegree_mul_le.trans (by norm_num))) (natDegree_mul_le.trans (by norm_num)))
  · change (-8+4*X+6*X^2-10*X^3 : K[X]).natDegree≤7
    exact ((natDegree_sub_le _ _).trans (max_le (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (by rw [natDegree_neg]; exact (by norm_num)) (natDegree_mul_le.trans (by norm_num))) (natDegree_mul_le.trans (by norm_num))) (natDegree_mul_le.trans (by norm_num))))
  · change (-13*X^3-6*X^4+10*X^5 : K[X]).natDegree≤7
    exact (natDegree_add_le_of_degree_le ((natDegree_sub_le _ _).trans (max_le (natDegree_mul_le.trans (by norm_num)) (natDegree_mul_le.trans (by norm_num)))) (natDegree_mul_le.trans (by norm_num)))
  · change (2*X^3+5*X^4+3*X^5 : K[X]).natDegree≤7
    exact (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (natDegree_mul_le.trans (by norm_num)) (natDegree_mul_le.trans (by norm_num))) (natDegree_mul_le.trans (by norm_num)))
  · change (-8*X^3+4*X^4+6*X^5-10*X^6 : K[X]).natDegree≤7
    exact ((natDegree_sub_le _ _).trans (max_le (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (natDegree_mul_le.trans (by norm_num)) (natDegree_mul_le.trans (by norm_num))) (natDegree_mul_le.trans (by norm_num))) (natDegree_mul_le.trans (by norm_num))))
  · change (4*X^5+2*X^6-3*X^7 : K[X]).natDegree≤7
    exact ((natDegree_sub_le _ _).trans (max_le (natDegree_add_le_of_degree_le (natDegree_mul_le.trans (by norm_num)) (natDegree_mul_le.trans (by norm_num))) (natDegree_mul_le.trans (by norm_num))))
  · change (-8*X^5+10*X^7 : K[X]).natDegree≤7
    exact (natDegree_add_le_of_degree_le (natDegree_mul_le.trans (by norm_num)) (natDegree_mul_le.trans (by norm_num)))
  · change (0 : K[X]).natDegree≤7
    exact (by simp)
  · change (27+34*X : K[X]).natDegree≤7
    exact (natDegree_add_le_of_degree_le (by norm_num) (natDegree_mul_le.trans (by norm_num)))
  · change (12+15*X-17*X^2 : K[X]).natDegree≤7
    exact ((natDegree_sub_le _ _).trans (max_le (natDegree_add_le_of_degree_le (by norm_num) (natDegree_mul_le.trans (by norm_num))) (natDegree_mul_le.trans (by norm_num))))
  · change (-28+24*X-34*X^2 : K[X]).natDegree≤7
    exact ((natDegree_sub_le _ _).trans (max_le (natDegree_add_le_of_degree_le (by rw [natDegree_neg]; exact (by norm_num)) (natDegree_mul_le.trans (by norm_num))) (natDegree_mul_le.trans (by norm_num))))
  · change (27*X^3+34*X^4 : K[X]).natDegree≤7
    exact (natDegree_add_le_of_degree_le (natDegree_mul_le.trans (by norm_num)) (natDegree_mul_le.trans (by norm_num)))
  · change (12*X^3+15*X^4-17*X^5 : K[X]).natDegree≤7
    exact ((natDegree_sub_le _ _).trans (max_le (natDegree_add_le_of_degree_le (natDegree_mul_le.trans (by norm_num)) (natDegree_mul_le.trans (by norm_num))) (natDegree_mul_le.trans (by norm_num))))
  · change (-28*X^3+24*X^4-34*X^5 : K[X]).natDegree≤7
    exact ((natDegree_sub_le _ _).trans (max_le (natDegree_add_le_of_degree_le (natDegree_mul_le.trans (by norm_num)) (natDegree_mul_le.trans (by norm_num))) (natDegree_mul_le.trans (by norm_num))))
  · change (24*X^5+2*X^6+17*X^7 : K[X]).natDegree≤7
    exact (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (natDegree_mul_le.trans (by norm_num)) (natDegree_mul_le.trans (by norm_num))) (natDegree_mul_le.trans (by norm_num)))
  · change (-28*X^5 : K[X]).natDegree≤7
    exact (natDegree_mul_le.trans (by norm_num))
  · change (20*X^7 : K[X]).natDegree≤7
    exact (natDegree_mul_le.trans (by norm_num))

theorem mixedOneThreeBase3_leading : Function.Injective (Matrix.mulVec
    (fun x j => (mixedOneThreeBase3Kernel (K := K) j x).coeff 7)) := by
  intro a b h
  have h6 : -a 0 + (-3)*a 1 + (17)*a 2=-b 0 + (-3)*b 1 + (17)*b 2 := by
    have hh := congrFun h (6 : Fin 9)
    norm_num [mixedOneThreeBase3Kernel,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  have h7 : (10)*a 1=(10)*b 1 := by
    have hh := congrFun h (7 : Fin 9)
    norm_num [mixedOneThreeBase3Kernel,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  have h8 : (20)*a 2=(20)*b 2 := by
    have hh := congrFun h (8 : Fin 9)
    norm_num [mixedOneThreeBase3Kernel,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  funext j
  fin_cases j
  · linear_combination (norm := ring1!) -h6 + (-3/10 : K)*h7 + (17/20 : K)*h8
  · linear_combination (norm := ring1!) (1/10 : K)*h7
  · linear_combination (norm := ring1!) (1/20 : K)*h8

theorem mixedOneThreeBase3_jet : Function.Injective (Matrix.mulVec
    (fun (ij : Fin 3 × Fin 3) (k : Fin 3) =>
      (mixedOneThreeBase3Coordinates (K := K) ij.1 ij.2).coeff (2-k.val))) := by
  intro a b h
  have h0 : (3/2 : K)*a 0 + (1/10 : K)*a 1 + (-1/5 : K)*a 2=(3/2 : K)*b 0 + (1/10 : K)*b 1 + (-1/5 : K)*b 2 := by
    have hh := congrFun h ((0,0) : Fin 3 × Fin 3)
    norm_num [mixedOneThreeBase3Coordinates,mixedOneThreeBase3CoordinateNumerator,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,Matrix.smul_apply,smul_eq_mul,coeff_C_mul,coeff_add,coeff_sub,
      coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  have h1 : (-13/5 : K)*a 0 + (-7/10 : K)*a 1 + (2/5 : K)*a 2=(-13/5 : K)*b 0 + (-7/10 : K)*b 1 + (2/5 : K)*b 2 := by
    have hh := congrFun h ((0,1) : Fin 3 × Fin 3)
    norm_num [mixedOneThreeBase3Coordinates,mixedOneThreeBase3CoordinateNumerator,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,Matrix.smul_apply,smul_eq_mul,coeff_C_mul,coeff_add,coeff_sub,
      coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  have h2 : (1/10 : K)*a 0=(1/10 : K)*b 0 := by
    have hh := congrFun h ((0,2) : Fin 3 × Fin 3)
    norm_num [mixedOneThreeBase3Coordinates,mixedOneThreeBase3CoordinateNumerator,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,Matrix.smul_apply,smul_eq_mul,coeff_C_mul,coeff_add,coeff_sub,
      coeff_neg,coeff_X,coeff_mul_X_pow',coeff_mul_X,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] at hh ⊢
    first | exact hh | linear_combination (norm := ring1!) hh
  funext j
  fin_cases j
  · linear_combination (norm := ring1!) (10)*h2
  · linear_combination (norm := ring1!) (-4)*h0 + (-2)*h1 + (8)*h2
  · linear_combination (norm := ring1!) (-7)*h0 + -h1 + (79)*h2

private theorem mixedOneThreeBase3_rg_row0 (j : Fin 6) :
    (mixedOneThreeBase3Right (K := K)*mixedOneThreeBase3 : Matrix (Fin 6) (Fin 6) K[X]) 0 j=
      ((1 : Matrix (Fin 6) (Fin 6) K[X]) : Matrix (Fin 6) (Fin 6) K[X]) 0 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase3,mixedOneThreeBase3Right,mixedOneThreeBase3Selector,mixedOneThreeBase3Kernel,mixedOneThreeBase3CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase3_rg_row1 (j : Fin 6) :
    (mixedOneThreeBase3Right (K := K)*mixedOneThreeBase3 : Matrix (Fin 6) (Fin 6) K[X]) 1 j=
      ((1 : Matrix (Fin 6) (Fin 6) K[X]) : Matrix (Fin 6) (Fin 6) K[X]) 1 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase3,mixedOneThreeBase3Right,mixedOneThreeBase3Selector,mixedOneThreeBase3Kernel,mixedOneThreeBase3CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase3_rg_row2 (j : Fin 6) :
    (mixedOneThreeBase3Right (K := K)*mixedOneThreeBase3 : Matrix (Fin 6) (Fin 6) K[X]) 2 j=
      ((1 : Matrix (Fin 6) (Fin 6) K[X]) : Matrix (Fin 6) (Fin 6) K[X]) 2 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase3,mixedOneThreeBase3Right,mixedOneThreeBase3Selector,mixedOneThreeBase3Kernel,mixedOneThreeBase3CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase3_rg_row3 (j : Fin 6) :
    (mixedOneThreeBase3Right (K := K)*mixedOneThreeBase3 : Matrix (Fin 6) (Fin 6) K[X]) 3 j=
      ((1 : Matrix (Fin 6) (Fin 6) K[X]) : Matrix (Fin 6) (Fin 6) K[X]) 3 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase3,mixedOneThreeBase3Right,mixedOneThreeBase3Selector,mixedOneThreeBase3Kernel,mixedOneThreeBase3CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase3_rg_row4 (j : Fin 6) :
    (mixedOneThreeBase3Right (K := K)*mixedOneThreeBase3 : Matrix (Fin 6) (Fin 6) K[X]) 4 j=
      ((1 : Matrix (Fin 6) (Fin 6) K[X]) : Matrix (Fin 6) (Fin 6) K[X]) 4 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase3,mixedOneThreeBase3Right,mixedOneThreeBase3Selector,mixedOneThreeBase3Kernel,mixedOneThreeBase3CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase3_rg_row5 (j : Fin 6) :
    (mixedOneThreeBase3Right (K := K)*mixedOneThreeBase3 : Matrix (Fin 6) (Fin 6) K[X]) 5 j=
      ((1 : Matrix (Fin 6) (Fin 6) K[X]) : Matrix (Fin 6) (Fin 6) K[X]) 5 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase3,mixedOneThreeBase3Right,mixedOneThreeBase3Selector,mixedOneThreeBase3Kernel,mixedOneThreeBase3CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

theorem mixedOneThreeBase3_rg :
    mixedOneThreeBase3Right (K := K)*mixedOneThreeBase3=(1 : Matrix (Fin 6) (Fin 6) K[X]) := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact mixedOneThreeBase3_rg_row0 j
  · exact mixedOneThreeBase3_rg_row1 j
  · exact mixedOneThreeBase3_rg_row2 j
  · exact mixedOneThreeBase3_rg_row3 j
  · exact mixedOneThreeBase3_rg_row4 j
  · exact mixedOneThreeBase3_rg_row5 j

private theorem mixedOneThreeBase3_rs_row0 (j : Fin 3) :
    (mixedOneThreeBase3Right (K := K)*mixedOneThreeBase3Selector : Matrix (Fin 6) (Fin 3) K[X]) 0 j=
      ((0 : Matrix (Fin 6) (Fin 3) K[X]) : Matrix (Fin 6) (Fin 3) K[X]) 0 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase3,mixedOneThreeBase3Right,mixedOneThreeBase3Selector,mixedOneThreeBase3Kernel,mixedOneThreeBase3CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase3_rs_row1 (j : Fin 3) :
    (mixedOneThreeBase3Right (K := K)*mixedOneThreeBase3Selector : Matrix (Fin 6) (Fin 3) K[X]) 1 j=
      ((0 : Matrix (Fin 6) (Fin 3) K[X]) : Matrix (Fin 6) (Fin 3) K[X]) 1 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase3,mixedOneThreeBase3Right,mixedOneThreeBase3Selector,mixedOneThreeBase3Kernel,mixedOneThreeBase3CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase3_rs_row2 (j : Fin 3) :
    (mixedOneThreeBase3Right (K := K)*mixedOneThreeBase3Selector : Matrix (Fin 6) (Fin 3) K[X]) 2 j=
      ((0 : Matrix (Fin 6) (Fin 3) K[X]) : Matrix (Fin 6) (Fin 3) K[X]) 2 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase3,mixedOneThreeBase3Right,mixedOneThreeBase3Selector,mixedOneThreeBase3Kernel,mixedOneThreeBase3CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase3_rs_row3 (j : Fin 3) :
    (mixedOneThreeBase3Right (K := K)*mixedOneThreeBase3Selector : Matrix (Fin 6) (Fin 3) K[X]) 3 j=
      ((0 : Matrix (Fin 6) (Fin 3) K[X]) : Matrix (Fin 6) (Fin 3) K[X]) 3 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase3,mixedOneThreeBase3Right,mixedOneThreeBase3Selector,mixedOneThreeBase3Kernel,mixedOneThreeBase3CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase3_rs_row4 (j : Fin 3) :
    (mixedOneThreeBase3Right (K := K)*mixedOneThreeBase3Selector : Matrix (Fin 6) (Fin 3) K[X]) 4 j=
      ((0 : Matrix (Fin 6) (Fin 3) K[X]) : Matrix (Fin 6) (Fin 3) K[X]) 4 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase3,mixedOneThreeBase3Right,mixedOneThreeBase3Selector,mixedOneThreeBase3Kernel,mixedOneThreeBase3CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase3_rs_row5 (j : Fin 3) :
    (mixedOneThreeBase3Right (K := K)*mixedOneThreeBase3Selector : Matrix (Fin 6) (Fin 3) K[X]) 5 j=
      ((0 : Matrix (Fin 6) (Fin 3) K[X]) : Matrix (Fin 6) (Fin 3) K[X]) 5 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase3,mixedOneThreeBase3Right,mixedOneThreeBase3Selector,mixedOneThreeBase3Kernel,mixedOneThreeBase3CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

theorem mixedOneThreeBase3_rs :
    mixedOneThreeBase3Right (K := K)*mixedOneThreeBase3Selector=(0 : Matrix (Fin 6) (Fin 3) K[X]) := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact mixedOneThreeBase3_rs_row0 j
  · exact mixedOneThreeBase3_rs_row1 j
  · exact mixedOneThreeBase3_rs_row2 j
  · exact mixedOneThreeBase3_rs_row3 j
  · exact mixedOneThreeBase3_rs_row4 j
  · exact mixedOneThreeBase3_rs_row5 j

private theorem mixedOneThreeBase3_vg_row0 (j : Fin 6) :
    (mixedOneThreeBase3Kernel (K := K)*mixedOneThreeBase3 : Matrix (Fin 3) (Fin 6) K[X]) 0 j=
      ((0 : Matrix (Fin 3) (Fin 6) K[X]) : Matrix (Fin 3) (Fin 6) K[X]) 0 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase3,mixedOneThreeBase3Right,mixedOneThreeBase3Selector,mixedOneThreeBase3Kernel,mixedOneThreeBase3CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase3_vg_row1 (j : Fin 6) :
    (mixedOneThreeBase3Kernel (K := K)*mixedOneThreeBase3 : Matrix (Fin 3) (Fin 6) K[X]) 1 j=
      ((0 : Matrix (Fin 3) (Fin 6) K[X]) : Matrix (Fin 3) (Fin 6) K[X]) 1 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase3,mixedOneThreeBase3Right,mixedOneThreeBase3Selector,mixedOneThreeBase3Kernel,mixedOneThreeBase3CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase3_vg_row2 (j : Fin 6) :
    (mixedOneThreeBase3Kernel (K := K)*mixedOneThreeBase3 : Matrix (Fin 3) (Fin 6) K[X]) 2 j=
      ((0 : Matrix (Fin 3) (Fin 6) K[X]) : Matrix (Fin 3) (Fin 6) K[X]) 2 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase3,mixedOneThreeBase3Right,mixedOneThreeBase3Selector,mixedOneThreeBase3Kernel,mixedOneThreeBase3CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

theorem mixedOneThreeBase3_vg :
    mixedOneThreeBase3Kernel (K := K)*mixedOneThreeBase3=(0 : Matrix (Fin 3) (Fin 6) K[X]) := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact mixedOneThreeBase3_vg_row0 j
  · exact mixedOneThreeBase3_vg_row1 j
  · exact mixedOneThreeBase3_vg_row2 j

private theorem mixedOneThreeBase3_wa_row0 (j : Fin 3) :
    (mixedOneThreeBase3CoordinateNumerator (K := K)*(mixedOneThreeBase3Kernel*mixedOneThreeBase3Selector) : Matrix (Fin 3) (Fin 3) K[X]) 0 j=
      ((20 : K[X]) • (1 : Matrix (Fin 3) (Fin 3) K[X]) : Matrix (Fin 3) (Fin 3) K[X]) 0 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase3,mixedOneThreeBase3Right,mixedOneThreeBase3Selector,mixedOneThreeBase3Kernel,mixedOneThreeBase3CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase3_wa_row1 (j : Fin 3) :
    (mixedOneThreeBase3CoordinateNumerator (K := K)*(mixedOneThreeBase3Kernel*mixedOneThreeBase3Selector) : Matrix (Fin 3) (Fin 3) K[X]) 1 j=
      ((20 : K[X]) • (1 : Matrix (Fin 3) (Fin 3) K[X]) : Matrix (Fin 3) (Fin 3) K[X]) 1 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase3,mixedOneThreeBase3Right,mixedOneThreeBase3Selector,mixedOneThreeBase3Kernel,mixedOneThreeBase3CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

private theorem mixedOneThreeBase3_wa_row2 (j : Fin 3) :
    (mixedOneThreeBase3CoordinateNumerator (K := K)*(mixedOneThreeBase3Kernel*mixedOneThreeBase3Selector) : Matrix (Fin 3) (Fin 3) K[X]) 2 j=
      ((20 : K[X]) • (1 : Matrix (Fin 3) (Fin 3) K[X]) : Matrix (Fin 3) (Fin 3) K[X]) 2 j := by
  fin_cases j <;>
    simp [mixedOneThreeBase3,mixedOneThreeBase3Right,mixedOneThreeBase3Selector,mixedOneThreeBase3Kernel,mixedOneThreeBase3CoordinateNumerator,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,matrix_cons_five,matrix_cons_six,
      matrix_cons_seven,matrix_cons_eight,matrix_cons_nine] <;> ring

theorem mixedOneThreeBase3_wa :
    mixedOneThreeBase3Coordinates (K := K)*(mixedOneThreeBase3Kernel*mixedOneThreeBase3Selector)=(1 : Matrix (Fin 3) (Fin 3) K[X]) := by
  apply polynomial_matrix_smul_cancel 20 (by norm_num)
  rw [← Matrix.smul_mul,mixedOneThreeBase3Coordinates_scaled]
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact mixedOneThreeBase3_wa_row0 j
  · exact mixedOneThreeBase3_wa_row1 j
  · exact mixedOneThreeBase3_wa_row2 j

theorem mixedOneThreeBase3_completion :
    mixedOneThreeBase3 (K := K)*mixedOneThreeBase3Right+mixedOneThreeBase3Selector*mixedOneThreeBase3Coordinates*mixedOneThreeBase3Kernel=(1 : Matrix (Fin 9) (Fin 9) K[X]) := by
  exact polynomial_completion_of_left_inverse mixedOneThreeBase3 mixedOneThreeBase3Selector mixedOneThreeBase3Right
    mixedOneThreeBase3Kernel mixedOneThreeBase3Coordinates (by decide) mixedOneThreeBase3_rg mixedOneThreeBase3_rs
    mixedOneThreeBase3_vg mixedOneThreeBase3_wa

def mixedOneThreeBase3Completion :
    UniformCubicCompletion (m := Fin 9) (fun j : Fin 6 => if j.val<3 then 1 else 2)
      7 (mixedOneThreeBase3Coordinates (K := K)) where
  G := mixedOneThreeBase3
  S := mixedOneThreeBase3Selector
  R := mixedOneThreeBase3Right
  V := mixedOneThreeBase3Kernel
  gDegree := mixedOneThreeBase3_gDegree
  sDegree := mixedOneThreeBase3_sDegree
  vDegree := mixedOneThreeBase3_vDegree
  leading := mixedOneThreeBase3_leading
  rg := mixedOneThreeBase3_rg
  rs := mixedOneThreeBase3_rs
  vg := mixedOneThreeBase3_vg
  wa := mixedOneThreeBase3_wa
  completion := mixedOneThreeBase3_completion

end FD56
