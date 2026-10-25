/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.IntegerPolynomial
import FD56.LinearAlgebra.PolynomialMatrix

/-! Integer identities for a ten-state, three-row affine witness. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def tenThreeM : Matrix (Fin 10) (Fin 10) K[X] :=
  ![![0, X, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, X, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, X, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, X, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, X, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, X, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, X, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, X, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, X], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def tenThreeP : Matrix (Fin 3) (Fin 10) K[X] :=
  ![![0, 0, 0, 0, X, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, X, 0, 0], ![X, 1, 0, 0, 1, 0, 0, 0, 0, 0]]

def tenThreeV0 : Fin 10 → K[X] := fun i =>
  integerPolynomial (([
  [0, 0, 2, 0, 0, 0, 0, 16, 0, 0, -4, 0, 0, 0, 0, -5],
  [0, -2, 0, -2, 0, 0, -16, 0, -16, 0, 0, 13, 0, 0, 0, 0, 5],
  [0, 0, 2, 0, 1, 0, 0, 17, 0, 6, 0, 0, -9, 0, 0, 0, 0, -3],
  [-1, 0, 0, -1, 0, -8, 0, 0, -8, 0, 4, 0, 0, 3, 0, 0, 0, 0, 1],
  [0, 2, 0, 0, 0, 0, 16, 0, 0, 0, 0, -9],
  [0, 0, -2, 0, 0, 0, 0, -16, 0, 0, 0, 0, 9],
  [1, 0, 0, 1, 0, 8, 0, 0, 6, 0, 0, 0, 0, -7],
  [0, -2, 0, 0, 0, 0, -16, 0, 0, 4, 0, 0, 0, 0, 5],
  [0, 0, 2, 0, 0, 0, 0, 15, 0, 0, -7, 0, 0, 0, 0, -3],
  [0, 0, 0, -1, 0, 0, -1, 0, -5, 0, 0, 3, 0, 0, 0, 0, 1]]).getD i.val [])

def tenThreeV1 : Fin 10 → K[X] := fun i =>
  integerPolynomial (([
  [0, 0, 0, 0, -1, 0, 0, 1, 0, -10, 0, 0, 4, 0, 0, 0, 0, 2],
  [-1, 0, 0, 1, 0, -7, 0, 0, 9, 0, 10, 0, 0, -6, 0, 0, 0, 0, -2],
  [0, 1, 0, 0, -1, 0, 8, 0, 0, -8, 0, -5, 0, 0, 3, 0, 0, 0, 0, 1],
  [0],
  [1, 0, 0, -1, 0, 8, 0, 0, -10, 0, 0, 0, 0, 2],
  [0, -1, 0, 0, 1, 0, -8, 0, 0, 10, 0, 0, 0, 0, -2],
  [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -3, 0, 0, 0, 0, 2],
  [0, 0, 0, 1, 0, 0, -1, 0, 10, 0, 0, -4, 0, 0, 0, 0, -2],
  [0, 0, 0, 0, -1, 0, 0, -1, 0, -5, 0, 0, 3, 0, 0, 0, 0, 1],
  [0]]).getD i.val [])

def tenThreeV2 : Fin 10 → K[X] := fun i =>
  integerPolynomial (([
  [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 5, 0, 0, -3, 0, 0, 0, 0, -1],
  [0, 0, 1, 0, 0, -1, 0, 8, 0, 0, -8, 0, -5, 0, 0, 3, 0, 0, 0, 0, 1],
  [1, 0, 0, -1, 0, 8, 0, 0, -10, 0, 0, 0, 0, 2],
  [0],
  [0, 0, -1, 0, 0, 1, 0, -9, 0, 0, 7],
  [0, 0, 0, 1, 0, 0, -1, 0, 9, 0, 0, -7],
  [0, 0, 0, 0, 0, 0, 0, -2, 0, 5, 0, 0, -1, 0, 0, 0, 0, -1],
  [0, 0, 0, 0, 0, -1, 0, 0, -1, 0, -5, 0, 0, 3, 0, 0, 0, 0, 1],
  [0],
  [0]]).getD i.val [])

def tenThreeV3 : Fin 10 → K[X] := fun i =>
  integerPolynomial (([
  [1, 0, 0, 0, 0, 8, -1, 0, -2, 0, 0, -8, 0, -3, 0, 0, 3, 0, 0, 0, 0, 1],
  [0, 1, 0, 0, -1, 0, 8, 0, 0, -10, 0, 0, 0, 0, 2],
  [0, 0, -1, 0, 0, 1, 0, -9, 0, 0, 7],
  [0],
  [0, 0, 0, 0, 1, 0, 0, -3, 0, 14, 0, 0, -8, 0, 0, 0, 0, -1],
  [0, 0, 0, 0, 0, -1, 0, 0, -3, 0, 0, 0, 0, 2],
  [0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, -5, 0, 0, 3, 0, 0, 0, 0, 1],
  [0],
  [0],
  [0]]).getD i.val [])

def tenThreeTerminalCoefficients : List (List ℤ) :=
  [
  [0, 0, 0, 0, 0, 0, 0, 0, -6, 0, 14, 0, 0, -6, 0, 0, 0, 0, -1],
  [1, 0, 0, 0, 0, 8, -1, 0, -2, 0, 0, -8, 0, -3, 0, 0, 3, 0, 0, 0, 0, 1],
  [0, 2, 0, 0, 0, 0, 16, -4, 0, 2, 0, 0, -16, 0, -1, 0, 0, 2, 0, 0, 0, 0, 1]]

def tenThreeF : Fin 3 → K[X] := fun i =>
  integerPolynomial (tenThreeTerminalCoefficients.getD i.val [])

theorem tenThree_step0 : tenThreeM (K := K) *ᵥ tenThreeV0 = tenThreeV1 := by
  funext i
  fin_cases i <;>
    norm_num [tenThreeM,tenThreeV0,tenThreeV1,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    (try change _ = integerPolynomial (K := K) []) <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem tenThree_step1 : tenThreeM (K := K) *ᵥ tenThreeV1 = tenThreeV2 := by
  funext i
  fin_cases i <;>
    norm_num [tenThreeM,tenThreeV1,tenThreeV2,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    (try change _ = integerPolynomial (K := K) []) <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem tenThree_step2 : tenThreeM (K := K) *ᵥ tenThreeV2 = tenThreeV3 := by
  funext i
  fin_cases i <;>
    norm_num [tenThreeM,tenThreeV2,tenThreeV3,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    (try change _ = integerPolynomial (K := K) []) <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem tenThree_output0 : tenThreeP (K := K) *ᵥ tenThreeV0 = 0 := by
  funext i
  fin_cases i <;>
    norm_num [tenThreeP,tenThreeV0,tenThreeF,tenThreeTerminalCoefficients,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    change _ = integerPolynomial (K := K) [] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem tenThree_output1 : tenThreeP (K := K) *ᵥ tenThreeV1 = 0 := by
  funext i
  fin_cases i <;>
    norm_num [tenThreeP,tenThreeV1,tenThreeF,tenThreeTerminalCoefficients,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    change _ = integerPolynomial (K := K) [] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem tenThree_output2 : tenThreeP (K := K) *ᵥ tenThreeV2 = 0 := by
  funext i
  fin_cases i <;>
    norm_num [tenThreeP,tenThreeV2,tenThreeF,tenThreeTerminalCoefficients,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    change _ = integerPolynomial (K := K) [] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem tenThree_output3 : tenThreeP (K := K) *ᵥ tenThreeV3 = tenThreeF := by
  funext i
  fin_cases i <;>
    norm_num [tenThreeP,tenThreeV3,tenThreeF,tenThreeTerminalCoefficients,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem tenThree_M_degree : DegreeBound (tenThreeM (K := K)) 1 := by
  intro i j
  fin_cases i <;> (fin_cases j <;> norm_num [tenThreeM,Polynomial.natDegree_X])

theorem tenThree_P_degree : DegreeBound (tenThreeP (K := K)) 1 := by
  intro i j
  fin_cases i <;> (fin_cases j <;> norm_num [tenThreeP,Polynomial.natDegree_X])

end FD56
