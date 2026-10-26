/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.IntegerPolynomial
import FD56.LinearAlgebra.PolynomialMatrix

/-! Exact polynomial chains for a thirteen-state, four-row affine witness. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def thirteenFourM : Matrix (Fin 13) (Fin 13) K[X] :=
  ![![0, X, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, X, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, X, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, X, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, X, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, X, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, X, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, X, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, X, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, X, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, X, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, X], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def thirteenFourP : Matrix (Fin 4) (Fin 13) K[X] :=
  ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, X, 0, 0], ![0, 0, 0, 0, X, 0, 0, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, X, 0, 0, 0, 0, 0], ![X, 0, 0, 0, 0, 0, 0, 1, 0, 0, X, 0, 0]]

def thirteenFourV0 : Fin 13 → K[X] := fun i =>
  integerPolynomial (([
  [0, 0, 0, -1, 0, 2, 0, 1, 0, -2, 0, -1, 2, 0, 0, 0, 0, -2, 0, 2, 0, -1],
  [0, 0, 1, 0, -3, 0, 1, 0, 3, 0, -1, -2, -1, 2, 0, 0, 2, 0, -4, 0, 3, 0, -1],
  [0, 0, 0, -1, 0, 1, -2, 3, 2, -6, 2, 1, 3, 3, -2, 1, -1, -2, 0, 5, 0, -4, 0, 1],
  [0, 0, 0, 0, 3, 2, -7, -2, 4, -2, 3, -1, -3, -2, -2, 3, 0, 0, 1, 0, -3, 0, 3, 0, -1],
  [0, 0, 0, 0, 0, -5, -4, 9, 4, -3, 4, -3, 2, 3, -3, -1, 4, 0, -4, 0, 1],
  [0, 0, 0, 0, 0, 0, 11, 8, -23, -10, 13, -6, 2, 3, -3, -4, 1, 2, 1, 2, 0, -1],
  [1, 0, -3, 0, -1, -2, 7, -4, -8, 14, 5, -7, 4, 1, -2, -1, 3, 0, -2, -1],
  [0, 0, 1, 0, -2, 0, -1, 0, 2, 0, 1, -2, 0, 0, 0, 0, 2, 0, -2, 0, 1],
  [0, 0, 0, 0, 0, 0, 5, 4, -9, -4, 3, -4, 3, -2, -3, 3, 1, -4, 0, 4, 0, -1],
  [0, 0, 0, 0, 2, 2, -4, -7, -1, 7, 4, -4, 2, -3, 1, 4, -3, -1, 3, 0, -3, 0, 1],
  [0, -1, 0, 3, 0, -1, 0, -3, 0, 1, 2, 1, -2, 0, 0, -2, 0, 4, 0, -3, 0, 1],
  [0, 0, 2, 0, -6, 0, 4, 0, 2, 5, 2, -13, -4, 12, 0, -5, 2, 1, -5, 0, 4, 0, -1],
  [0, 0, 0, -4, -2, 12, 4, -11, 0, 1, -6, 0, 12, 3, -13, -1, 6, -1, -1, 3, 0, -3, 0, 1]]).getD i.val [])

def thirteenFourV1 : Fin 13 → K[X] := fun i =>
  integerPolynomial (([
  [0, 0, 0, 0, 0, -2, -2, 4, 2, -3, 2, 0, 1, 2, 0, 1, -1, 0, 0, 1, 0, -1],
  [0, 0, 0, 0, 2, 2, -6, -4, 7, 0, -3, 1, -2, 1, 1, 1, 1, -1, -1, 0, 2, 0, -1],
  [0, 0, 0, 0, 0, -2, -2, 2, 2, 1, 2, 0, 1, 0, -5, -3, 7, 0, -4, 1, 1, -3, 0, 3, 0, -1],
  [0, 0, 0, 0, 0, 0, 6, 4, -14, -6, 10, -2, -1, 5, 0, -7, 0, 6, 1, -2],
  [1, 0, -3, 0, -1, -2, 7, 7, 0, -9, -5, 6, -2, 3, 1, -4, -1, 1, 0, 0, 2, 0, -1],
  [0, 1, 1, -3, -2, -1, -3, 7, -2, -8, 15, 3, -7, 4, 1, -2, 1, 3, -2, -2],
  [0, 0, 0, 1, 0, -2, 5, 3, -9, -2, 3, -3, 1, -2, -3, 3, 1, -2, 0, 2],
  [0, 0, 0, 0, 2, 2, -4, -2, 3, -2, 0, -1, -2, 0, -1, 1, 0, 0, -1, 0, 1],
  [0, -1, 0, 3, 0, 1, 2, -7, -7, 0, 9, 5, -6, 2, -3, -1, 4, 1, -1, 0, 0, -2, 0, 1],
  [0, 0, 1, 0, -3, 0, 3, 0, -1, 5, 3, -11, -3, 10, 0, -5, 0, 1, -1, 0, 1],
  [0, 0, 0, -2, -2, 6, 4, -7, 0, 3, -1, 2, -1, -1, -1, -1, 1, 1, 0, -2, 0, 1],
  [0, 0, 0, 0, -4, -2, 12, 4, -11, 0, 1, -6, 0, 12, 3, -13, -1, 6, -1, -1, 3, 0, -3, 0, 1],
  [0]]).getD i.val [])

def thirteenFourV2 : Fin 13 → K[X] := fun i =>
  integerPolynomial (([
  [0, 0, 0, 0, 0, 0, 0, -4, -2, 8, 2, -3, 2, -2, -4, -2, 8, 1, -5, 0, 1, -1, 0, 2, 0, -1],
  [0, 0, 0, 0, 0, 0, 4, 2, -12, -4, 11, 0, -1, 6, 0, -12, -3, 13, 1, -6, 1, 1, -3, 0, 3, 0, -1],
  [1, 0, -3, 0, -1, -2, 7, 13, 4, -23, -11, 16, -4, 2, 6, -4, -8, 1, 6, 1, 0, 0, -1],
  [0, 2, 1, -6, -2, -2, -5, 14, 5, -8, 6, -2, -1, 2, 4, -1, -3, 2, -1, -2, 0, 2, 0, -1],
  [0, 0, 1, 2, -3, -4, 4, 0, -2, -4, -5, 12, 4, -9, 1, 4, -1, -1, 3, 0, -2],
  [0, 0, 0, 0, 3, 2, -6, 3, 6, -11, -2, 2, -5, 1, -3, -2, 3, 1, -3, 0, 3],
  [0, -1, 0, 3, 0, 3, 4, -11, -9, 3, 7, 5, -7, 0, -3, -2, 5, 1, -1, -1, 0, -1, 0, 1],
  [0, 0, 0, 0, 0, 0, 4, 2, -8, -2, 3, -2, 2, 4, 2, -8, -1, 5, 0, -1, 1, 0, -2, 0, 1],
  [0, 0, 0, -1, -2, 3, 4, -4, 0, 2, 4, 5, -12, -4, 9, -1, -4, 1, 1, -3, 0, 2],
  [0, 0, 0, 0, -6, -4, 18, 8, -18, 0, 4, -7, 2, 11, 2, -14, -2, 7, 0, -1, 1, 0, -2, 0, 1],
  [0, 0, 0, 0, 0, -4, -2, 12, 4, -11, 0, 1, -6, 0, 12, 3, -13, -1, 6, -1, -1, 3, 0, -3, 0, 1],
  [0],
  [0]]).getD i.val [])

def thirteenFourV3 : Fin 13 → K[X] := fun i =>
  integerPolynomial (([
  [1, 0, -3, 0, -1, -2, 7, 17, 6, -35, -15, 27, -4, 1, 12, -4, -20, -2, 19, 2, -6, 1, 0, -3, 0, 3, 0, -1],
  [0, 3, 1, -9, -2, -3, -7, 21, 18, -4, -17, -13, 15, -2, 6, 5, -7, -6, 0, 4, 1, 2, 0, -2],
  [0, 0, 3, 3, -9, -6, 2, -5, 12, 1, -13, 18, 2, -10, 3, 8, -2, -4, 5, -1, -4, 0, 2, 0, -1],
  [0, 0, 0, 1, 5, -1, -10, 7, 6, -13, -6, -3, 7, 5, -12, -1, 7, 0, -4, 3, 3, -2],
  [0, -1, 0, 3, 0, 6, 6, -17, -6, 9, -4, 3, -5, -5, -2, -5, 3, 4, 0, -4, 0, 2, 0, 1],
  [0, 0, -1, 0, 3, 0, 7, 6, -19, -11, 6, 5, 7, -3, 2, -11, -3, 10, 1, -2, 0, 0, -3, 0, 2],
  [0, 0, 0, -1, -2, 3, 4, 0, 2, -6, 2, 8, -14, -2, 13, 1, -12, 0, 6, -3, -1, 3, 0, -2, 0, 1],
  [0, 0, 0, 0, -7, -6, 21, 12, -22, 0, 6, -3, 7, -1, -2, -5, -3, 3, 1, 0, -2, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, -10, -6, 30, 12, -29, 0, 5, -13, 2, 23, 5, -27, -3, 13, -1, -2, 4, 0, -5, 0, 2],
  [0, 0, 0, 0, 0, 0, -4, -2, 12, 4, -11, 0, 1, -6, 0, 12, 3, -13, -1, 6, -1, -1, 3, 0, -3, 0, 1],
  [0],
  [0],
  [0]]).getD i.val [])

def thirteenFourTerminalCoefficients : List (List ℤ) :=
  [
  [0, 3, 1, -9, -2, -3, -7, 21, 18, -4, -17, -13, 15, -2, 6, 5, -7, -6, 0, 4, 1, 2, 0, -2],
  [0, 0, -1, 0, 3, -10, 0, 36, -5, -35, 9, 1, -10, -3, 18, 3, -32, 0, 17, -1, -6, 4, 2, -5, 1, 2],
  [1, 0, -3, 0, -1, -9, 1, 38, 18, -57, -15, 33, -7, 8, 11, -6, -25, -5, 22, 3, -6, -1, 0, -3, 0, 4, 0, -1],
  [0, 1, 0, -3, -7, -7, 19, 19, -5, 6, -29, -18, 34, -5, -1, 7, -7, -17, -1, 19, 0, -6, 1, 0, -2, 0, 3, 0, -1]]

def thirteenFourF : Fin 4 → K[X] := fun i =>
  integerPolynomial (thirteenFourTerminalCoefficients.getD i.val [])

theorem thirteenFour_step0 : thirteenFourM (K := K) *ᵥ thirteenFourV0 = thirteenFourV1 := by
  funext i
  fin_cases i <;>
    norm_num [thirteenFourM,thirteenFourV0,thirteenFourV1,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    (try change _ = integerPolynomial (K := K) []) <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem thirteenFour_step1 : thirteenFourM (K := K) *ᵥ thirteenFourV1 = thirteenFourV2 := by
  funext i
  fin_cases i <;>
    norm_num [thirteenFourM,thirteenFourV1,thirteenFourV2,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    (try change _ = integerPolynomial (K := K) []) <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem thirteenFour_step2 : thirteenFourM (K := K) *ᵥ thirteenFourV2 = thirteenFourV3 := by
  funext i
  fin_cases i <;>
    norm_num [thirteenFourM,thirteenFourV2,thirteenFourV3,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    (try change _ = integerPolynomial (K := K) []) <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem thirteenFour_output0 : thirteenFourP (K := K) *ᵥ thirteenFourV0 = 0 := by
  funext i
  fin_cases i <;>
    norm_num [thirteenFourP,thirteenFourV0,thirteenFourF,thirteenFourTerminalCoefficients,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    change _ = integerPolynomial (K := K) [] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem thirteenFour_output1 : thirteenFourP (K := K) *ᵥ thirteenFourV1 = 0 := by
  funext i
  fin_cases i <;>
    norm_num [thirteenFourP,thirteenFourV1,thirteenFourF,thirteenFourTerminalCoefficients,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    change _ = integerPolynomial (K := K) [] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem thirteenFour_output2 : thirteenFourP (K := K) *ᵥ thirteenFourV2 = 0 := by
  funext i
  fin_cases i <;>
    norm_num [thirteenFourP,thirteenFourV2,thirteenFourF,thirteenFourTerminalCoefficients,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    change _ = integerPolynomial (K := K) [] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem thirteenFour_output3 : thirteenFourP (K := K) *ᵥ thirteenFourV3 = thirteenFourF := by
  funext i
  fin_cases i <;>
    norm_num [thirteenFourP,thirteenFourV3,thirteenFourF,thirteenFourTerminalCoefficients,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem thirteenFour_M_degree : DegreeBound (thirteenFourM (K := K)) 1 := by
  intro i j
  fin_cases i <;> (fin_cases j <;> norm_num [thirteenFourM,Polynomial.natDegree_X])

theorem thirteenFour_P_degree : DegreeBound (thirteenFourP (K := K)) 1 := by
  intro i j
  fin_cases i <;> (fin_cases j <;> norm_num [thirteenFourP,Polynomial.natDegree_X])

end FD56
