/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.IntegerPolynomial
import FD56.LinearAlgebra.PolynomialMatrix

/-! Exact integer polynomial identities for a depth-four thirteen-state witness. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option Elab.async false

def thirteenThreeQ4M : Matrix (Fin 13) (Fin 13) K[X] :=
  ![![0, X, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, X, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, X, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, X, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, X, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, X, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, X, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, X, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, X, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, X, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, X, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, X], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def thirteenThreeQ4P : Matrix (Fin 3) (Fin 13) K[X] :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, X, 0, 0, 0], ![0, 1 + X, 0, 0, 0, 0, 0, 0, 0, X, 0, 0, 0], ![X, 0, 1, 0, X, 0, 0, 0, 0, 0, 0, 0, 0]]

def thirteenThreeQ4V0 : Fin 13 → K[X] := fun i =>
  integerPolynomial (([
  [0, 0, 0, 0, 0, 3, 12, 21, 24, 6, -33, -33, -17, -60, -98, -122, -134, -125, -102, 178, 486, 293, -62, -144, -88, -29, 9, 12, 3],
  [0, 0, 0, 0, 0, 3, 9, 12, 12, -6, -27, -6, -11, -49, -49, -73, -61, -64, -38, 216, 270, 23, -85, -59, -29, 0, 9, 3],
  [0, 0, -1, -3, -4, -4, -1, -4, -24, -43, -33, 10, 33, 46, 143, 186, 175, 196, 243, 324, 129, -160, -177, -80, -15, 18, 15, 3],
  [0, 1, 4, 6, 4, -5, -21, -19, 5, 6, -11, -26, -46, -58, -43, 97, 287, 242, 95, -52, -282, -259, -28, 49, 31, 18, 5],
  [0, 1, 3, 4, 4, -2, -8, 3, 19, 27, 23, 0, -29, -83, -88, -53, -62, -118, -222, -307, -326, -116, 142, 159, 70, 14, -12, -12, -3],
  [0, 0, -2, -8, -13, -12, 3, 31, 27, -11, -13, 32, 94, 124, 163, 190, -64, -408, -414, -225, 34, 294, 246, 19, -52, -23, -9, -3],
  [0, 0, -2, -6, -7, -5, 8, 20, -6, -38, -43, -35, 6, 75, 188, 177, 41, 16, 63, 162, 231, 236, 113, -72, -104, -50, -13, 7, 8, 2],
  [0, 0, 0, 3, 12, 20, 20, -1, -42, -38, 7, -2, -58, -130, -179, -244, -283, 55, 507, 522, 279, -32, -280, -207, 1, 54, 16],
  [0, 0, 0, 3, 9, 9, 3, -18, -36, 12, 72, 79, 80, 28, -117, -294, -246, 5, 79, 25, -66, -156, -163, -74, 38, 56, 25, 7, -3, -4, -1],
  [0, 0, 0, 0, -3, -12, -21, -24, -6, 33, 33, 17, 60, 98, 122, 134, 125, 102, -178, -486, -293, 62, 144, 88, 29, -9, -12, -3],
  [0, 0, 0, 0, -3, -9, -7, 3, 26, 41, -25, -107, -128, -156, -116, 92, 288, 188, -86, -124, 28, 79, 35, 2, -9, -9, -3],
  [0, 0, 0, 0, 0, 1, 4, 13, 32, 27, -27, -55, -47, -78, -78, -2, 86, 140, 92, -10, -52, -37, -10, 0, -1, 1, 1],
  [-1, -4, -6, -4, 5, 21, 19, -10, -21, -9, 12, 77, 176, 220, 108, -98, -273, -319, -98, 152, 113, -23, -43, -7, 9, 4]]).getD i.val [])

def thirteenThreeQ4V1 : Fin 13 → K[X] := fun i =>
  integerPolynomial (([
  [0, 1, 4, 6, 4, -5, -18, -10, 17, 18, -17, -53, -52, -69, -92, 48, 214, 181, 31, -90, -66, 11, -5, -36, -28, -11, 5, 9, 3],
  [0, 1, 3, 3, 1, -6, -12, 2, 15, 3, -20, -33, -19, -50, -42, 90, 124, 57, -26, -64, -2, 13, -18, -18, -10, -1, 6, 3],
  [0, 0, -1, -4, -7, -8, -2, 10, 8, -6, -7, 21, 68, 78, 105, 147, 33, -121, -172, -130, -18, 12, -13, -9, -3, 8, 9, 2],
  [0, 0, -1, -3, -3, -1, 6, 12, -3, -19, -16, -12, 6, 46, 105, 89, -12, -46, -55, -60, -76, -90, -3, 70, 55, 20, 1, -5, -4, -1],
  [0, 0, 0, 1, 4, 7, 8, 2, -11, -11, -4, -15, -26, -36, -55, -81, -93, -9, 99, 108, 54, 2, 14, 39, 20, 2, -7, -9, -3],
  [0, 0, 0, 1, 3, 2, -2, -10, -16, 6, 34, 36, 45, 34, -42, -106, -69, 46, 95, 88, 96, 75, 73, 39, -34, -48, -25, -6, 4, 4, 1],
  [0, 0, 0, 0, 0, 0, -1, -4, -7, -9, -5, 24, 58, 40, -8, -45, -119, -181, -123, 21, 229, 341, 112, -192, -178, -8, 42, 13],
  [0, 0, 0, 0, 0, 0, 2, 6, 8, 5, -13, -35, -49, -76, -88, -25, -6, -58, -81, -45, 53, 13, -121, -161, -83, 29, 53, 25, 7, -3, -4, -1],
  [0, 0, 0, 0, 0, -2, -8, -8, 8, 21, 6, -22, -30, -18, 20, 120, 220, 265, 194, -188, -538, -330, 52, 144, 87, 30, -8, -12, -3],
  [-1, -4, -6, -4, 5, 18, 10, -17, -18, 17, 53, 52, 69, 92, -48, -214, -181, -31, 90, 66, -11, 5, 36, 28, 11, -5, -9, -3],
  [0, 0, 0, 0, 0, 0, 1, 4, 13, 32, 27, -27, -55, -47, -78, -78, -2, 86, 140, 92, -10, -52, -37, -10, 0, -1, 1, 1],
  [0, -1, -4, -6, -4, 5, 21, 19, -10, -21, -9, 12, 77, 176, 220, 108, -98, -273, -319, -98, 152, 113, -23, -43, -7, 9, 4],
  []]).getD i.val [])

def thirteenThreeQ4V2 : Fin 13 → K[X] := fun i =>
  integerPolynomial (([
  [0, 0, 0, 0, 0, 0, 0, 0, -1, -4, -13, -32, -27, 27, 55, 47, 78, 78, 2, -86, -140, -92, 10, 52, 37, 10, 0, 1, -1, -1],
  [0, 0, 0, 0, 0, 0, 0, 0, -1, -3, -10, -22, -5, 32, 23, 24, 54, 24, -22, -64, -76, -16, 26, 26, 11, -1, 1, 0, -1],
  [0, 0, 0, 0, 0, -1, -3, -4, -4, 3, 15, 20, 33, 40, 4, -1, 20, 34, 49, 33, 36, -1, -17, 36, 36, 7, -5, -5, -1],
  [0, 0, 0, 0, 1, 4, 6, 4, -5, -20, -16, 20, 43, 14, -44, -100, -200, -274, -132, 120, 337, 395, 114, -178, -139, 12, 44, 6, -9, -3],
  [0, 0, 0, 0, 1, 3, 4, 4, -2, -11, -7, -1, -13, -31, -54, -67, -112, -127, -35, 50, 141, 109, -46, -88, -44, -5, 5, 0, 1, 1],
  [0, 0, 0, 0, 0, -2, -8, -9, 4, 14, -3, -27, -6, 40, 60, 112, 175, 146, 13, -311, -517, -101, 393, 256, -105, -148, -16, 30, 10],
  [-1, -4, -6, -4, 5, 18, 10, -15, -12, 25, 58, 39, 34, 43, -124, -302, -206, -37, 32, -15, -56, 58, 49, -93, -150, -88, 20, 50, 25, 7, -3, -4, -1],
  [0, 0, 0, 0, 0, 0, -1, -4, 5, 40, 48, -21, -77, -77, -96, -58, 118, 306, 405, 286, -198, -590, -367, 42, 144, 86, 31, -7, -12, -3],
  [0, -2, -8, -12, -8, 10, 39, 29, -27, -39, 8, 65, 129, 245, 312, 60, -312, -454, -350, -8, 218, 102, -18, -7, 21, 20, -1, -9, -3],
  [0, 0, 0, 0, 0, 0, 0, 1, 4, 13, 32, 27, -27, -55, -47, -78, -78, -2, 86, 140, 92, -10, -52, -37, -10, 0, -1, 1, 1],
  [0, 0, -1, -4, -6, -4, 5, 21, 19, -10, -21, -9, 12, 77, 176, 220, 108, -98, -273, -319, -98, 152, 113, -23, -43, -7, 9, 4],
  [],
  []]).getD i.val [])

def thirteenThreeQ4V3 : Fin 13 → K[X] := fun i =>
  integerPolynomial (([
  [0, 0, 0, 0, 1, 4, 6, 4, -5, -21, -19, 10, 21, 9, -12, -77, -176, -220, -108, 98, 273, 319, 98, -152, -113, 23, 43, 7, -9, -4],
  [0, 0, 0, 0, 1, 3, 3, 1, -6, -15, -4, 14, 7, 2, -14, -63, -113, -107, -1, 99, 174, 145, -47, -105, -8, 31, 12, -5, -4],
  [0, 0, 0, 0, 0, -1, -4, -3, 8, 9, -23, -43, 14, 83, 74, 68, 75, -54, -261, -443, -397, 236, 788, 370, -283, -287, -4, 74, 16, -9, -3],
  [-1, -4, -6, -4, 5, 19, 13, -11, -8, 23, 47, 32, 33, 30, -155, -356, -273, -149, -95, -50, -6, 199, 158, -139, -238, -132, 15, 55, 25, 8, -2, -4, -1],
  [0, 0, 0, 0, 0, 0, -3, -12, -4, 44, 62, -24, -104, -83, -56, 2, 230, 481, 551, 299, -509, -1107, -468, 435, 400, -19, -117, -23, 18, 7],
  [0, -3, -12, -18, -12, 15, 57, 39, -42, -51, 33, 123, 168, 279, 355, -64, -614, -660, -387, 24, 203, 46, 40, 42, -72, -130, -89, 11, 47, 25, 7, -3, -4, -1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 72, 75, -48, -132, -124, -174, -136, 116, 392, 545, 378, -208, -642, -404, 32, 144, 85, 32, -6, -12, -3],
  [0, 0, -3, -12, -18, -12, 15, 60, 48, -37, -60, -1, 77, 206, 421, 532, 168, -410, -727, -669, -106, 370, 215, -41, -50, 14, 29, 3, -9, -3],
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 13, 32, 27, -27, -55, -47, -78, -78, -2, 86, 140, 92, -10, -52, -37, -10, 0, -1, 1, 1],
  [0, 0, 0, -1, -4, -6, -4, 5, 21, 19, -10, -21, -9, 12, 77, 176, 220, 108, -98, -273, -319, -98, 152, 113, -23, -43, -7, 9, 4],
  [],
  [],
  []]).getD i.val [])

def thirteenThreeQ4V4 : Fin 13 → K[X] := fun i =>
  integerPolynomial (([
  [-1, -4, -6, -4, 5, 20, 16, -8, -7, 17, 32, 28, 47, 37, -153, -370, -336, -262, -202, -51, 93, 373, 303, -186, -343, -140, 46, 67, 20, 4, -2, -4, -1],
  [0, 0, 0, 0, 0, 0, -4, -16, -7, 52, 71, -47, -147, -69, 27, 76, 298, 556, 497, 38, -952, -1504, -232, 1223, 770, -302, -404, -27, 92, 23, -9, -3],
  [0, -4, -16, -24, -16, 20, 76, 52, -53, -59, 56, 170, 200, 312, 385, -219, -970, -933, -536, -71, 153, 40, 239, 200, -211, -368, -221, 26, 102, 50, 15, -5, -8, -2],
  [0, 0, 0, 0, 0, 0, 0, -3, -12, 14, 116, 137, -72, -236, -207, -230, -134, 346, 873, 1096, 677, -717, -1749, -872, 467, 544, 66, -85, -29, 6, 4],
  [0, 0, -6, -24, -36, -24, 30, 117, 87, -79, -111, 32, 200, 374, 700, 887, 104, -1024, -1387, -1056, -82, 573, 261, -1, -8, -58, -101, -86, 2, 44, 25, 7, -3, -4, -1],
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 31, 104, 102, -75, -187, -171, -252, -214, 114, 478, 685, 470, -218, -694, -441, 22, 144, 84, 33, -5, -12, -3],
  [0, 0, 0, -4, -16, -24, -16, 20, 81, 67, -47, -81, -10, 89, 283, 597, 752, 276, -508, -1000, -988, -204, 522, 328, -64, -93, 7, 38, 7, -9, -3],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 13, 32, 27, -27, -55, -47, -78, -78, -2, 86, 140, 92, -10, -52, -37, -10, 0, -1, 1, 1],
  [0, 0, 0, 0, -1, -4, -6, -4, 5, 21, 19, -10, -21, -9, 12, 77, 176, 220, 108, -98, -273, -319, -98, 152, 113, -23, -43, -7, 9, 4],
  [],
  [],
  [],
  []]).getD i.val [])

def thirteenThreeQ4TerminalCoefficients : List (List ℤ) :=
  [
  [-1, -4, -6, -4, 5, 20, 16, -8, -7, 17, 32, 28, 47, 37, -153, -370, -336, -262, -202, -51, 93, 373, 303, -186, -343, -140, 46, 67, 20, 4, -2, -4, -1],
  [0, 0, 0, 0, 0, 0, -4, -20, -23, 45, 123, 24, -194, -216, -42, 103, 374, 854, 1053, 535, -914, -2456, -1736, 991, 1993, 468, -706, -431, 65, 115, 14, -12, -3],
  [0, -5, -20, -36, -44, -11, 72, 98, 56, 21, -6, 91, 260, 559, 796, 328, -453, -1165, -1822, -1660, -954, 51, 1185, 764, -398, -719, -419, -29, 83, 72, 63, 18, -5, -6, -4, -1]]

def thirteenThreeQ4F : Fin 3 → K[X] := fun i =>
  integerPolynomial (thirteenThreeQ4TerminalCoefficients.getD i.val [])

theorem thirteenThreeQ4_step0 : thirteenThreeQ4M (K := K) *ᵥ thirteenThreeQ4V0 = thirteenThreeQ4V1 := by
  funext i
  fin_cases i <;>
    norm_num [thirteenThreeQ4M,thirteenThreeQ4V0,thirteenThreeQ4V1,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    (try simp only [add_mul,one_mul,← integerPolynomial_zero_cons,← integerPolynomial_add]) <;>
    (try change _ = integerPolynomial (K := K) []) <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem thirteenThreeQ4_step1 : thirteenThreeQ4M (K := K) *ᵥ thirteenThreeQ4V1 = thirteenThreeQ4V2 := by
  funext i
  fin_cases i <;>
    norm_num [thirteenThreeQ4M,thirteenThreeQ4V1,thirteenThreeQ4V2,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    (try simp only [add_mul,one_mul,← integerPolynomial_zero_cons,← integerPolynomial_add]) <;>
    (try change _ = integerPolynomial (K := K) []) <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem thirteenThreeQ4_step2 : thirteenThreeQ4M (K := K) *ᵥ thirteenThreeQ4V2 = thirteenThreeQ4V3 := by
  funext i
  fin_cases i <;>
    norm_num [thirteenThreeQ4M,thirteenThreeQ4V2,thirteenThreeQ4V3,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    (try simp only [add_mul,one_mul,← integerPolynomial_zero_cons,← integerPolynomial_add]) <;>
    (try change _ = integerPolynomial (K := K) []) <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem thirteenThreeQ4_step3 : thirteenThreeQ4M (K := K) *ᵥ thirteenThreeQ4V3 = thirteenThreeQ4V4 := by
  funext i
  fin_cases i <;>
    norm_num [thirteenThreeQ4M,thirteenThreeQ4V3,thirteenThreeQ4V4,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    (try simp only [add_mul,one_mul,← integerPolynomial_zero_cons,← integerPolynomial_add]) <;>
    (try change _ = integerPolynomial (K := K) []) <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem thirteenThreeQ4_output0 : thirteenThreeQ4P (K := K) *ᵥ thirteenThreeQ4V0 = 0 := by
  funext i
  fin_cases i <;>
    norm_num [thirteenThreeQ4P,thirteenThreeQ4V0,thirteenThreeQ4F,thirteenThreeQ4TerminalCoefficients,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    (try simp only [add_mul,one_mul,← integerPolynomial_zero_cons,← integerPolynomial_add]) <;>
    change _ = integerPolynomial (K := K) [] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem thirteenThreeQ4_output1 : thirteenThreeQ4P (K := K) *ᵥ thirteenThreeQ4V1 = 0 := by
  funext i
  fin_cases i <;>
    norm_num [thirteenThreeQ4P,thirteenThreeQ4V1,thirteenThreeQ4F,thirteenThreeQ4TerminalCoefficients,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    (try simp only [add_mul,one_mul,← integerPolynomial_zero_cons,← integerPolynomial_add]) <;>
    change _ = integerPolynomial (K := K) [] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem thirteenThreeQ4_output2 : thirteenThreeQ4P (K := K) *ᵥ thirteenThreeQ4V2 = 0 := by
  funext i
  fin_cases i <;>
    norm_num [thirteenThreeQ4P,thirteenThreeQ4V2,thirteenThreeQ4F,thirteenThreeQ4TerminalCoefficients,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    (try simp only [add_mul,one_mul,← integerPolynomial_zero_cons,← integerPolynomial_add]) <;>
    change _ = integerPolynomial (K := K) [] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem thirteenThreeQ4_output3 : thirteenThreeQ4P (K := K) *ᵥ thirteenThreeQ4V3 = 0 := by
  funext i
  fin_cases i <;>
    norm_num [thirteenThreeQ4P,thirteenThreeQ4V3,thirteenThreeQ4F,thirteenThreeQ4TerminalCoefficients,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    (try simp only [add_mul,one_mul,← integerPolynomial_zero_cons,← integerPolynomial_add]) <;>
    change _ = integerPolynomial (K := K) [] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem thirteenThreeQ4_output4 : thirteenThreeQ4P (K := K) *ᵥ thirteenThreeQ4V4 = thirteenThreeQ4F := by
  funext i
  fin_cases i <;>
    norm_num [thirteenThreeQ4P,thirteenThreeQ4V4,thirteenThreeQ4F,thirteenThreeQ4TerminalCoefficients,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    (try simp only [add_mul,one_mul,← integerPolynomial_zero_cons,← integerPolynomial_add]) <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem thirteenThreeQ4_M_degree : DegreeBound (thirteenThreeQ4M (K := K)) 1 := by
  intro i j
  fin_cases i <;> (fin_cases j <;> norm_num [thirteenThreeQ4M,Polynomial.natDegree_X])

theorem thirteenThreeQ4_P_degree : DegreeBound (thirteenThreeQ4P (K := K)) 1 := by
  intro i j
  fin_cases i <;> (fin_cases j <;> norm_num [thirteenThreeQ4P,Polynomial.natDegree_X]) <;>
    exact Polynomial.natDegree_add_le_of_degree_le (by simp) (by simp)

end FD56
