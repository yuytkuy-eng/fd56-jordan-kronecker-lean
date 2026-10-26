/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.IntegerPolynomial
import FD56.LinearAlgebra.PolynomialMatrix

/-! Exact polynomial chains for a sixteen-state, five-row affine witness. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def sixteenFiveM : Matrix (Fin 16) (Fin 16) K[X] :=
  ![![0, 1, X, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, X, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, X, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, X, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, X, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, X, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, X, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, X, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, X, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, X, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, X, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, X, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, X, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, X], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def sixteenFiveP : Matrix (Fin 5) (Fin 16) K[X] :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, X, 0, 0, 0, 0], ![X, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, X, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, X, 0, 0, 0, X, 0, 0, 0, 1, 0, 0, X, 0, 0, 0], ![0, 0, 0, 0, X, 0, 0, 0, 0, 0, X, 0, 1, 0, 0, 0]]

def sixteenFiveV0 : Fin 16 → K[X] := fun i =>
  integerPolynomial (([
  [0, 0, 0, 0, 0, 2, -2, 2, 2, -2, 0, -4, 3, -3, 0, -28, 16, -2, 13, 4, -17, -3, -5, 1, 3, 4, -1, 0, -1],
  [0, 0, 0, 0, -3, 0, -1, -8, -6, -1, -9, -8, 2, 9, 13, 6, 15, 1, 40, -11, 17, -5, -16, -13, -12, 3, 6, 2, -1, 0, -1],
  [0, 0, 0, 1, 0, 0, 2, 3, -2, 2, 2, -10, -10, -12, -17, -18, -16, -50, 14, -23, 5, 11, 0, 6, -3, -8, -1, 3, 0, 1],
  [0, 0, 0, 0, 0, 0, -2, 2, -2, -2, 2, 0, 4, -3, 3, 0, 28, -16, 2, -13, -4, 17, 3, 5, -1, -3, -4, 1, 0, 1],
  [0, 0, 0, 0, 0, 3, 0, 1, 8, 6, 8, 9, 15, 11, 19, 4, 4, 33, 10, -3, -19, -14, -1, 7, -2, 0, 0, -2, -2],
  [0, 0, 0, 0, -1, 0, 0, -2, -3, -5, -2, -9, -3, -18, -5, 7, -30, 5, 13, 16, 20, 1, -2, 15, 6, 0, 4, 1, -2],
  [0, 0, 0, 0, 0, 0, 0, 2, -2, 2, 2, -2, 0, -4, 3, -3, 0, -28, 16, -2, 13, 4, -17, -3, -5, 1, 3, 4, -1, 0, -1],
  [0, 0, 0, 0, 0, 0, -3, 7, -1, -1, 7, 20, 8, -5, 37, -8, 33, -34, -30, -16, -6, 4, 2, 4, -3, 2, -1, 0, 1, 2],
  [0, 0, 0, 0, 0, 1, -7, 0, -5, -10, -23, -15, -1, -45, 7, -32, 23, 27, 1, -4, -1, -8, -4, -2, -15, -5, 0, -3, -1, 2],
  [0, 0, 0, 0, 0, 4, -1, 6, 5, 12, 15, 1, 30, -5, 25, -10, -5, 1, -2, -2, -4, -10, -2, 10, 7, 2, -3, -4, -3],
  [0, 0, 0, 0, -1, 2, -5, 2, 1, -16, 5, -15, 1, -13, -11, -18, 0, 18, -9, 30, 13, 6, 10, -11, 2, 6, 0, -1, 2, -1],
  [0, 0, 0, 0, -2, 2, -2, -2, 2, 0, 4, -3, 3, 0, 28, -16, 2, -13, -4, 17, 3, 5, -1, -3, -4, 1, 0, 1],
  [0, 0, 0, 0, 0, 1, -5, 5, -3, -9, 10, -13, 6, -16, 2, -8, 14, -4, -51, -1, -27, 6, 8, -9, 4, 0, -6, 0, 3, 0, 1],
  [0, 0, 2, 0, 0, 11, -2, 6, 16, -4, 21, -5, 15, 9, 11, 1, 14, 48, 7, 27, -1, 5, 15, -4, 2, 5, -2, -3, 0, -1],
  [0, -2, 0, 0, -8, 0, -5, -7, -2, -11, 10, -15, 6, 1, -4, -10, -9, -13, -4, 3, -25, -7, -3, -5, 5, 2, -2, 1, -1, -2],
  [1, 0, 0, 3, 0, 2, -1, 2, 1, -13, 10, -13, -12, 4, -4, -16, 5, -8, -5, 30, 1, 4, 11, -6, 3, 5, -1, 3, 4]]).getD i.val [])

def sixteenFiveV1 : Fin 16 → K[X] := fun i =>
  integerPolynomial (([
  [0, 0, 0, 0, -2, 0, -1, -6, -3, -3, -7, -6, -8, -1, 1, -11, -3, -15, -10, 3, -6, 0, -5, -13, -6, 0, -2, 1, 2],
  [0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0, -8, -10, -8, -20, -15, -16, -22, -2, -21, -8, 7, 17, 9, 2, -9, -4, -1, 1, 1, 1],
  [0, 0, 0, 0, 0, 0, 1, 2, -1, 6, 8, 8, 13, 12, 14, 19, 32, -12, 35, -3, -7, -2, -11, 4, 6, -5, -4, 1, -2, -1],
  [0, 0, 0, 0, 0, 2, 0, 1, 6, 3, 3, 7, 6, 8, 1, -1, 11, 3, 15, 10, -3, 6, 0, 5, 13, 6, 0, 2, -1, -2],
  [0, 0, 0, 0, -1, 0, 0, -2, -1, -7, 0, -7, -5, -18, -9, 10, -33, 5, -15, 32, 18, 14, 2, -2, 3, -5, 5, 4, 2, -1, 0, -1],
  [0, 0, 0, 0, 0, 0, 0, -1, 5, 1, 1, 5, 20, 4, -2, 34, -8, 5, -18, -32, -3, -2, -13, -1, -1, -2, 5, 3, -1, 1, 1],
  [0, 0, 0, 0, 0, 0, -2, 0, -1, -6, -3, -3, -7, -6, -8, -1, 1, -11, -3, -15, -10, 3, -6, 0, -5, -13, -6, 0, -2, 1, 2],
  [0, 0, 0, 0, 0, 1, -3, -1, 1, -5, -11, 0, 0, -15, 2, -7, 13, 22, 2, -6, -3, -12, -14, -4, -5, 2, 2, -6, -5, -1],
  [0, 0, 0, 0, 0, 3, 1, 1, 7, 13, -1, 6, 15, -4, 12, -21, -23, 1, 16, -11, 26, 3, 4, 20, -4, 4, 3, -4, -4, 2, -1],
  [0, 0, 0, 0, -1, 0, -3, 0, -1, -14, 5, -11, -2, -10, -11, 10, -16, 20, -22, 26, 30, 9, 15, -12, -1, 2, 1, -1, 3, -1],
  [0, 0, 0, 0, -2, 2, -1, -7, 7, -3, -5, 7, -10, 6, 12, -14, -6, 1, -8, -34, 2, -22, 5, 5, -13, 5, 0, -5, 0, 3, 0, 1],
  [0, 0, 0, 2, 0, 1, 6, 3, 3, 7, 6, 8, 1, -1, 11, 3, 15, 10, -3, 6, 0, 5, 13, 6, 0, 2, -1, -2],
  [0, 0, 0, 0, 0, 3, -2, 1, 9, -6, 10, 5, 0, 15, 12, -3, 4, 39, -6, 23, 2, -20, 8, -7, -3, 10, 0, -5, 1, -2, -2],
  [0, -1, 0, 0, -5, 0, -3, -8, 0, -10, -3, -5, -7, -11, 0, -14, -25, -8, -12, -2, 5, -6, 1, 6, -1, 5, 3, 0, 2, 2],
  [1, 0, 0, 3, 0, 2, -1, 2, 1, -13, 10, -13, -12, 4, -4, -16, 5, -8, -5, 30, 1, 4, 11, -6, 3, 5, -1, 3, 4],
  [0]]).getD i.val [])

def sixteenFiveV2 : Fin 16 → K[X] := fun i =>
  integerPolynomial (([
  [0, 0, 0, 1, 0, 0, 2, 2, 2, -1, 6, 0, -2, 5, -8, -1, 3, 10, -14, 14, -11, 0, 15, -2, 6, -3, -9, -5, 2, -1],
  [0, 0, 0, 0, 0, 0, 3, 2, 0, 12, 11, 11, 20, 18, 22, 20, 31, -1, 38, 12, 3, -5, -5, 4, 11, 8, 2, 1, 0, -2, -2],
  [0, 0, 0, 0, 0, 1, 0, 1, 4, 2, -4, 7, -1, 3, -17, -10, 21, -30, 20, -5, 29, 24, 14, 7, 11, 9, -5, 7, 3, 0, -1, 0, -1],
  [0, 0, 0, 0, -1, 0, 0, -2, -2, -2, 1, -6, 0, 2, -5, 8, 1, -3, -10, 14, -14, 11, 0, -15, 2, -6, 3, 9, 5, -2, 1],
  [0, 0, 0, 0, 0, 0, 0, -3, 5, 0, -5, 2, 17, -3, -8, 26, -9, 6, -29, -35, -18, -12, -10, -7, -1, -7, -8, -3, -1, -1, 2, 2],
  [0, 0, 0, 0, 0, 0, -1, -3, -2, -5, -8, -14, -7, -6, -23, 1, -6, 2, 19, -13, -16, 0, -18, -14, -9, -18, -4, 2, -8, -4, 1],
  [0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 2, -1, 6, 0, -2, 5, -8, -1, 3, 10, -14, 14, -11, 0, 15, -2, 6, -3, -9, -5, 2, -1],
  [0, 0, 0, 0, 0, 2, 1, -2, 7, 12, -15, 11, 4, -6, 2, -32, -13, -15, 36, -33, 52, 33, 13, 35, -16, 3, 5, -3, -5, 5, -2],
  [0, 0, 0, 0, -1, -2, -1, -1, -8, -7, 2, -16, 5, -20, -5, 22, -30, 14, -21, 18, -4, 11, -7, -7, 4, -11, 6, -1, -2, -1, 3, 0, 1],
  [0, 0, 0, 0, 0, 2, 0, -1, 10, 0, 2, 13, -2, 7, 11, -3, -3, 16, 2, -37, 8, -22, 10, 18, -7, 5, 2, -6, -2, 3, 0, 1],
  [0, 0, 0, 2, 0, 1, 9, 1, 4, 16, 0, 18, 6, -1, 26, 15, 12, 14, 36, 0, 23, 7, -7, 14, -7, -1, 9, -2, -5, 1, -2, -2],
  [0, 0, -1, 0, 0, -2, -2, -2, 1, -6, 0, 2, -5, 8, 1, -3, -10, 14, -14, 11, 0, -15, 2, -6, 3, 9, 5, -2, 1],
  [0, 0, 0, 0, -2, 0, -1, -9, 2, -9, -16, 5, -20, -23, 4, -18, -41, -3, -20, -7, 35, -5, 5, 17, -7, 8, 8, -1, 5, 6],
  [1, 0, 0, 3, 0, 2, -1, 2, 1, -13, 10, -13, -12, 4, -4, -16, 5, -8, -5, 30, 1, 4, 11, -6, 3, 5, -1, 3, 4],
  [0],
  [0]]).getD i.val [])

def sixteenFiveV3 : Fin 16 → K[X] := fun i =>
  integerPolynomial (([
  [0, 0, 0, 0, 0, 0, 4, 2, 1, 16, 13, 7, 27, 17, 25, 3, 21, 20, 8, 32, -2, 24, 19, 18, 18, 19, 11, -4, 7, 1, -2, -1, 0, -1],
  [0, 0, 0, 0, 0, 0, 0, 1, 2, 0, -6, 8, -7, 3, -15, -15, 29, -29, 17, -15, 43, 10, 25, 7, -4, 11, -11, 10, 12, 5, -3, 1, -1],
  [0, 0, 0, 0, -1, 0, 0, -2, -5, 3, 1, -11, 2, 19, -8, 0, 27, -12, -4, -15, -49, -7, -12, -25, -5, -7, -4, 1, 2, -3, 0, 2, 2],
  [0, 0, 0, 0, 0, 0, 0, -4, 2, -2, -10, -6, 3, -10, -14, 3, -8, 0, -27, -16, -31, -28, -10, -25, -15, -16, -26, -7, 1, -9, -2, 3],
  [0, 0, 0, 0, 0, 0, 0, -3, -2, -3, -6, -12, -8, 0, -23, -1, -1, -6, 18, -10, -6, -14, -4, -25, -9, -3, -6, 8, -11, -13, -4, 2, -1],
  [0, 0, 0, 0, 0, 1, 2, 1, 0, 9, 14, -16, 17, 4, -8, 7, -40, -14, -12, 46, -47, 66, 22, 13, 50, -18, 9, 2, -12, -10, 7, -3],
  [0, 0, 0, 0, 0, 1, -1, -3, 6, 4, -22, 13, -12, -1, -18, -37, 9, -45, 50, -54, 70, 29, 24, 28, -23, 7, -6, 3, -6, 3, -3, 3, 0, 1],
  [0, 0, 0, 0, -1, -2, 1, -1, -9, 3, 2, -14, 18, -22, 2, 33, -33, 11, -5, 20, -41, 19, -29, 3, 22, -18, 11, 1, -8, -3, 6, 0, 2],
  [0, 0, 0, 0, 2, 2, 1, 8, 11, 4, 18, 13, 16, 13, 10, 23, 12, 28, 16, -1, 8, 1, 17, 11, 7, -2, 1, 3, -4, -2, 1, -1, -2],
  [0, 0, 0, 1, 0, 1, 7, -1, 2, 17, -6, 18, 8, -6, 34, 16, 9, 4, 50, -14, 34, 7, -22, 16, -13, 2, 18, 3, -7, 2, -2, -2],
  [0, 0, -1, 0, 0, -4, -2, -3, -8, -4, -9, -14, 0, -12, -22, 1, -28, -27, -17, -9, -7, 20, -3, -1, 20, 2, 13, 6, 0, 5, 6],
  [0, 1, 0, 0, 1, 0, 1, -10, 4, -8, -29, 15, -33, -35, 8, -22, -57, 2, -28, -12, 65, -4, 9, 28, -13, 11, 13, -2, 8, 10],
  [1, 0, 0, 3, 0, 2, -1, 2, 1, -13, 10, -13, -12, 4, -4, -16, 5, -8, -5, 30, 1, 4, 11, -6, 3, 5, -1, 3, 4],
  [0],
  [0],
  [0]]).getD i.val [])

def sixteenFiveTerminalCoefficients : List (List ℤ) :=
  [
  [0, 0, 1, 0, 0, 1, 4, 3, -9, 20, 5, -22, 42, -16, -10, 11, -1, -37, 10, 4, -14, 89, 15, 27, 46, 6, 22, 9, 5, 9, 8, -1, 0, -1],
  [0, 0, 0, 0, 0, 0, 0, 0, 4, -1, 6, 7, 10, 17, 3, 28, -5, 21, -7, -8, 1, -30, 14, -6, 3, 2, -7, 4, -3, -2, -1, 1, -1, 0, -1],
  [0, 0, 0, 0, 0, 1, -1, -3, 2, 6, -24, 3, -18, 2, -28, -51, 12, -53, 50, -81, 54, -2, -4, 18, -48, -8, -22, -23, -13, 4, -12, 1, 3, 1],
  [0, 1, 0, 1, 3, 1, 10, 0, 6, 20, -10, 36, -13, -8, 45, -11, -15, -2, -1, -14, 95, 4, 58, 74, 1, 51, 16, 0, 8, 6, -7, 2, -2, -1],
  [1, 0, 0, 2, 0, 2, -5, 0, -5, -23, 3, -28, -38, -4, -16, -61, 5, -37, -38, 31, -18, -9, 17, -13, -23, 16, -2, 10, 18, -11, -8, 2, 2, -1]]

def sixteenFiveF : Fin 5 → K[X] := fun i =>
  integerPolynomial (sixteenFiveTerminalCoefficients.getD i.val [])

theorem sixteenFive_step0 : sixteenFiveM (K := K) *ᵥ sixteenFiveV0 = sixteenFiveV1 := by
  funext i
  fin_cases i <;>
    norm_num [sixteenFiveM,sixteenFiveV0,sixteenFiveV1,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    (try change _ = integerPolynomial (K := K) []) <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem sixteenFive_step1 : sixteenFiveM (K := K) *ᵥ sixteenFiveV1 = sixteenFiveV2 := by
  funext i
  fin_cases i <;>
    norm_num [sixteenFiveM,sixteenFiveV1,sixteenFiveV2,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    (try change _ = integerPolynomial (K := K) []) <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem sixteenFive_step2 : sixteenFiveM (K := K) *ᵥ sixteenFiveV2 = sixteenFiveV3 := by
  funext i
  fin_cases i <;>
    norm_num [sixteenFiveM,sixteenFiveV2,sixteenFiveV3,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    (try change _ = integerPolynomial (K := K) []) <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem sixteenFive_output0 : sixteenFiveP (K := K) *ᵥ sixteenFiveV0 = 0 := by
  funext i
  fin_cases i <;>
    norm_num [sixteenFiveP,sixteenFiveV0,sixteenFiveF,sixteenFiveTerminalCoefficients,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    change _ = integerPolynomial (K := K) [] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem sixteenFive_output1 : sixteenFiveP (K := K) *ᵥ sixteenFiveV1 = 0 := by
  funext i
  fin_cases i <;>
    norm_num [sixteenFiveP,sixteenFiveV1,sixteenFiveF,sixteenFiveTerminalCoefficients,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    change _ = integerPolynomial (K := K) [] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem sixteenFive_output2 : sixteenFiveP (K := K) *ᵥ sixteenFiveV2 = 0 := by
  funext i
  fin_cases i <;>
    norm_num [sixteenFiveP,sixteenFiveV2,sixteenFiveF,sixteenFiveTerminalCoefficients,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    change _ = integerPolynomial (K := K) [] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem sixteenFive_output3 : sixteenFiveP (K := K) *ᵥ sixteenFiveV3 = sixteenFiveF := by
  funext i
  fin_cases i <;>
    norm_num [sixteenFiveP,sixteenFiveV3,sixteenFiveF,sixteenFiveTerminalCoefficients,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem sixteenFive_M_degree : DegreeBound (sixteenFiveM (K := K)) 1 := by
  intro i j
  fin_cases i <;> (fin_cases j <;> norm_num [sixteenFiveM,Polynomial.natDegree_X])

theorem sixteenFive_P_degree : DegreeBound (sixteenFiveP (K := K)) 1 := by
  intro i j
  fin_cases i <;> (fin_cases j <;> norm_num [sixteenFiveP,Polynomial.natDegree_X])

end FD56
