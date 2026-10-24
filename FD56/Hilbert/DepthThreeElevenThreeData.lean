/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.IntegerPolynomial
import FD56.LinearAlgebra.PolynomialMatrix

/-! Integer certificates for an eleven-state, three-row affine witness. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def elevenThreeM : Matrix (Fin 11) (Fin 11) K[X] :=
  ![![0, (1) * X, (1), 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, (1) * X, (1), 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, (1) * X, (1), 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, (1) * X, (1), 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, (1) * X, (1), 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, (1) * X, (1), 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, (1) * X, (1), 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, (1) * X, (1), 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, (1) * X, (1)], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1) * X], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def elevenThreeP : Matrix (Fin 3) (Fin 11) K[X] :=
  ![![(1), 0, 0, 0, 0, 0, 0, 0, (1) * X, 0, 0], ![(1) * X, 0, 0, 0, 0, (1), 0, 0, (1), 0, 0], ![0, (1), 0, 0, (1) * X, 0, 0, 0, 0, 0, 0]]

def elevenThreeVA0 : Fin 11 → K[X] := fun i =>
  integerPolynomial ([[0, 0, 0, -10, -46, -81, 15],
    [0, 0, 0, -68, -18, -164, 4, 170],
    [0, 5, -16, 6, -93, -5, 199, 13, -139],
    [0, -34, -9, -82, 2, 51, -2, -126, -30, 108],
    [0, 0, 68, 18, 164, -4, -170],
    [0, 0, -10, -46, -71, 61, 81, -15],
    [34, 4, 98, 2, 88, 78, -134, -64, 46],
    [5, -50, -3, -243, -31, 108, -38, 130, 47, -77],
    [0, 0, 10, 46, 81, -15],
    [0, 0, 0, 14, -88, -64, 46],
    [-5, 16, -6, 161, 9, 53, 47, -77]].getD i.val [])

def elevenThreeVA1 : Fin 11 → K[X] := fun i =>
  integerPolynomial ([[0, 5, -16, 6, -161, -23, 35, 17, 31],
    [0, -34, -4, -98, 8, -42, -7, 73, -17, -31],
    [0, 0, 34, 9, 82, -2, -119, -2, -126, -30, 108],
    [0, 0, -10, 22, -53, 225, 77, -185],
    [34, 4, 98, -8, 42, 7, -73, 17, 31],
    [5, -16, 1, -145, -29, 196, 40, -4, -17, -31],
    [0, 5, -40, 43, -162, -46, 108, -38, 130, 47, -77],
    [0, 0, 0, 24, -42, 17, 31],
    [-5, 16, -6, 161, 23, -35, -17, -31],
    [0, -5, 16, -6, 161, 9, 53, 47, -77],
    [0]].getD i.val [])

def elevenThreeVA2 : Fin 11 → K[X] := fun i =>
  integerPolynomial ([[0, 0, 0, 5, -16, 6, -161, -9, -53, -47, 77],
    [0, 0, -10, 56, -44, 307, 75, -304, -2, -126, -30, 108],
    [34, 4, 98, -18, 64, -46, 152, 94, -154],
    [5, 18, 5, -47, -37, 238, 47, -77],
    [0, 10, -56, 44, -307, -75, 304, 2, 126, 30, -108],
    [0, 0, 5, -16, 1, -145, -15, 108, -38, 130, 47, -77],
    [-5, 16, -6, 161, 47, -77],
    [0, -10, 32, -12, 322, 32, 18, 30, -108],
    [0, 0, -5, 16, -6, 161, 9, 53, 47, -77],
    [0],
    [0]].getD i.val [])

def elevenThreeVA3 : Fin 11 → K[X] := fun i =>
  integerPolynomial ([[34, 4, 98, -28, 120, -90, 459, 169, -458, -2, -126, -30, 108],
    [5, 52, 9, 51, -55, 302, 1, 75, 94, -154],
    [0, 15, -38, 49, -354, -112, 542, 49, 49, 30, -108],
    [0, 0, 15, -72, 45, -452, -90, 412, -36, 256, 77, -185],
    [-5, 16, -6, 166, 31, -76, -145, -15, 108, -38, 130, 47, -77],
    [0, -15, 48, -18, 483, 79, -59, 30, -108],
    [0, 0, -15, 48, -18, 483, 41, 71, 77, -185],
    [0, 0, 0, -5, 16, -6, 161, 9, 53, 47, -77],
    [0],
    [0],
    [0]].getD i.val [])

def elevenThreeVB0 : Fin 11 → K[X] := fun i =>
  integerPolynomial ([[0, 0, 0, -418, -300, 31, -176],
    [0, 0, 0, -324, -1302, 170, 866, 104],
    [0, 209, -221, -921, 252, 1411, -92, -699, -48],
    [0, -162, -651, 85, 433, -110, -988, 6, 532, -8],
    [0, 0, 324, 1302, -170, -866, -104],
    [0, 0, -418, -300, 449, 124, -31, 176],
    [162, 442, 136, 906, 158, -872, -38, 198, -120],
    [209, -383, -1572, 13, 124, -8, 930, 16, -365, 64],
    [0, 0, 418, 300, -31, 176],
    [0, 0, 0, -674, -158, 198, -120],
    [-209, 221, 921, 72, 565, 80, -365, 64]].getD i.val [])

def elevenThreeVB1 : Fin 11 → K[X] := fun i =>
  integerPolynomial ([[0, 209, -221, -921, -72, 109, 78, 167, 56],
    [0, -162, -442, -136, -488, 142, 423, -86, -167, -56],
    [0, 0, 162, 651, -85, -433, -214, -988, 6, 532, -8],
    [0, 0, -418, 24, 1751, -46, -897, 72],
    [162, 442, 136, 488, -142, -423, 86, 167, 56],
    [209, -221, -1130, 149, 1030, 150, 58, -22, -167, -56],
    [0, 209, 35, -1272, -18, 300, -8, 930, 16, -365, 64],
    [0, 0, 0, -256, 142, 167, 56],
    [-209, 221, 921, 72, -109, -78, -167, -56],
    [0, -209, 221, 921, 72, 565, 80, -365, 64],
    [0]].getD i.val [])

def elevenThreeVB2 : Fin 11 → K[X] := fun i =>
  integerPolynomial ([[0, 0, 0, 209, -221, -921, -72, -565, -80, 365, -64],
    [0, 0, -418, 186, 2402, -131, -1330, -142, -988, 6, 532, -8],
    [162, 442, 136, 70, -118, 1328, 40, -730, 128],
    [209, -59, -688, 285, 1518, 8, -365, 64],
    [0, 418, -186, -2402, 131, 1330, 142, 988, -6, -532, 8],
    [0, 0, 209, -221, -1130, 149, 356, -8, 930, 16, -365, 64],
    [-209, 221, 921, 72, -365, 64],
    [0, -418, 442, 1842, 144, 456, 2, -532, 8],
    [0, 0, -209, 221, 921, 72, 565, 80, -365, 64],
    [0],
    [0]].getD i.val [])

def elevenThreeVB3 : Fin 11 → K[X] := fun i =>
  integerPolynomial ([[162, 442, 136, -348, 68, 3730, -91, -2060, -14, -988, 6, 532, -8],
    [209, 103, -246, 421, 1588, -110, 963, 104, -730, 128],
    [0, 627, -245, -3090, 416, 2848, 150, 623, 58, -532, 8],
    [0, 0, 627, -407, -3532, 280, 1686, 134, 1918, 10, -897, 72],
    [-209, 221, 921, 281, -586, -1066, 149, 356, -8, 930, 16, -365, 64],
    [0, -627, 663, 2763, 216, 91, 66, -532, 8],
    [0, 0, -627, 663, 2763, 216, 1021, 82, -897, 72],
    [0, 0, 0, -209, 221, 921, 72, 565, 80, -365, 64],
    [0],
    [0],
    [0]].getD i.val [])

def elevenThreeF : Fin 3 → K[X] := fun i =>
  integerPolynomial ([[34, 4, 98, -28, 120, -90, 459, 169, -458, -2, -126, -30, 108],
    [0, 19, 52, 80, 455, 199, -149, 489, 61, -458, -2, -126, -30, 108],
    [5, 47, 25, 45, 111, 333, -75, -70, 79, -46, -38, 130, 47, -77]].getD i.val [])

def elevenThreeG : Fin 3 → K[X] := fun i =>
  integerPolynomial ([[162, 442, 136, -348, 68, 3730, -91, -2060, -14, -988, 6, 532, -8],
    [0, -465, 1105, 2899, -132, 159, 3796, -623, -2052, -14, -988, 6, 532, -8],
    [209, -106, -25, 1342, 1869, -696, -103, 253, -374, 120, 930, 16, -365, 64]].getD i.val [])

def elevenThreeT0 : K[X] :=
  integerPolynomial [0, 6296, 25184, -44072, -31480, 31480, 6296, -62960, 62960, 37776, -62960, -75552, 119624, -18888, -119624, 107032, 151104, -50368, -69256, -6296, -6296, 6296, 18888, 0, -18888, 0, 6296]

def elevenThreeT1 : K[X] :=
  integerPolynomial [-6296, 12592, 6296, -6296, -69256, 37776, 69256, 6296, -44072, -18888, -12592, -50368, 107032, 132216, -119624, -169992, 50368, 69256, 18888, 6296, -12592, -18888, 0, 18888, 0, -6296]

def elevenThreeT2 : K[X] :=
  integerPolynomial [0, -18888, 18888, 18888, 18888, -25184, 37776, -31480, 25184, -81848, 6296, 50368, -25184, 25184, -18888, -12592, 0, 0, 6296]

def elevenThreeU : K[X] :=
  integerPolynomial [7421142095560049730907129706273, 65893516419994373295490016839813, 33293145309550027798900729603914, -19131254067209156650165893892113, -166312758719941550323432261426580, -80212366157358361867390001352470, 79466273428635206487793171282363, 109073719778037419987444418944748, 35372045578593023515733578400927, -86510998981072296076107325225728, -176564198931140897619348928842098, -178025626256384715422546251308322, 126171393632740962706747082092909, 393636190173550956728468211909346, 183285205167869763717207755483537, -177731775059529093187489780002018, -143489331005865781869186959327314, -25448119909580503323564787440429, 24557435814625613842138149694770, 42723350306268698443828096930385, 13125608121395580178373186835385, -23627376133139118796858014698598, -27604133585655442338096822198318, 6160522510664495699134987037819, 10083925621545007732029864382773]

def elevenThreeW : K[X] :=
  integerPolynomial [-51211070304308524780018706861948, -95000998513056999829130284017623, -145634982528187952219160739232289, -90140676944517206622922166600998, -51912562803541500233197754821747, -78837921983436394769151433880168, -91912311360444069688902027941303, -12624272441174587763019335663823, -173734817357512848868163620012379, -194681701724782614204384255592631, -94626049670921033227540150597503, 50767623244577971591706477088919, -27619548710244404532849672287272, 116332445578618194460520866035725, 349792623726865267008821888341372, 154105305373195176338207808868977, -163253249595269231027766144639085, -126022477383391158771463931666535, -7927911945470068717497829624884, 18396913303961118143003162656951, 32639424684723690711798232547612, 13125608121395580178373186835385, -23627376133139118796858014698598, -27604133585655442338096822198318, 6160522510664495699134987037819, 10083925621545007732029864382773]

theorem elevenThree_bezout : elevenThreeU (K := K)*elevenThreeT0 + elevenThreeW*elevenThreeT1 = 322424898635926472014997778402824608 := by
  unfold elevenThreeU elevenThreeW elevenThreeT0 elevenThreeT1
  calc
    _ = integerPolynomial [322424898635926472014997778402824608] := by
      rw [← integerPolynomial_mul,← integerPolynomial_mul,← integerPolynomial_add]
      apply integerPolynomial_eq_of_trim_eq
      decide
    _ = _ := by simp

theorem elevenThree_cross0 : elevenThreeT0 (K := K) =
    elevenThreeF 1 * elevenThreeG 2 - elevenThreeF 2 * elevenThreeG 1 := by
  norm_num [elevenThreeT0,elevenThreeF,elevenThreeG,List.getD]
  simp only [sub_eq_add_neg,← integerPolynomial_mul,← integerPolynomial_neg,← integerPolynomial_add]
  apply integerPolynomial_eq_of_trim_eq
  decide

theorem elevenThree_cross1 : elevenThreeT1 (K := K) =
    elevenThreeF 2 * elevenThreeG 0 - elevenThreeF 0 * elevenThreeG 2 := by
  norm_num [elevenThreeT1,elevenThreeF,elevenThreeG,List.getD]
  simp only [sub_eq_add_neg,← integerPolynomial_mul,← integerPolynomial_neg,← integerPolynomial_add]
  apply integerPolynomial_eq_of_trim_eq
  decide

theorem elevenThree_cross2 : elevenThreeT2 (K := K) =
    elevenThreeF 0 * elevenThreeG 1 - elevenThreeF 1 * elevenThreeG 0 := by
  norm_num [elevenThreeT2,elevenThreeF,elevenThreeG,List.getD]
  simp only [sub_eq_add_neg,← integerPolynomial_mul,← integerPolynomial_neg,← integerPolynomial_add]
  apply integerPolynomial_eq_of_trim_eq
  decide

theorem elevenThree_stepA0 : elevenThreeM (K := K) *ᵥ elevenThreeVA0 = elevenThreeVA1 := by
  funext i
  fin_cases i <;>
    norm_num [elevenThreeM,elevenThreeVA0,elevenThreeVA1,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem elevenThree_stepA1 : elevenThreeM (K := K) *ᵥ elevenThreeVA1 = elevenThreeVA2 := by
  funext i
  fin_cases i <;>
    norm_num [elevenThreeM,elevenThreeVA1,elevenThreeVA2,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem elevenThree_stepA2 : elevenThreeM (K := K) *ᵥ elevenThreeVA2 = elevenThreeVA3 := by
  funext i
  fin_cases i <;>
    norm_num [elevenThreeM,elevenThreeVA2,elevenThreeVA3,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem elevenThree_outputA0 : elevenThreeP (K := K) *ᵥ elevenThreeVA0 = 0 := by
  funext i
  fin_cases i <;>
    norm_num [elevenThreeP,elevenThreeVA0,elevenThreeF,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    change _ = integerPolynomial (K := K) [] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem elevenThree_outputA1 : elevenThreeP (K := K) *ᵥ elevenThreeVA1 = 0 := by
  funext i
  fin_cases i <;>
    norm_num [elevenThreeP,elevenThreeVA1,elevenThreeF,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    change _ = integerPolynomial (K := K) [] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem elevenThree_outputA2 : elevenThreeP (K := K) *ᵥ elevenThreeVA2 = 0 := by
  funext i
  fin_cases i <;>
    norm_num [elevenThreeP,elevenThreeVA2,elevenThreeF,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    change _ = integerPolynomial (K := K) [] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem elevenThree_outputA3 : elevenThreeP (K := K) *ᵥ elevenThreeVA3 = elevenThreeF := by
  funext i
  fin_cases i <;>
    norm_num [elevenThreeP,elevenThreeVA3,elevenThreeF,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem elevenThree_stepB0 : elevenThreeM (K := K) *ᵥ elevenThreeVB0 = elevenThreeVB1 := by
  funext i
  fin_cases i <;>
    norm_num [elevenThreeM,elevenThreeVB0,elevenThreeVB1,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem elevenThree_stepB1 : elevenThreeM (K := K) *ᵥ elevenThreeVB1 = elevenThreeVB2 := by
  funext i
  fin_cases i <;>
    norm_num [elevenThreeM,elevenThreeVB1,elevenThreeVB2,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem elevenThree_stepB2 : elevenThreeM (K := K) *ᵥ elevenThreeVB2 = elevenThreeVB3 := by
  funext i
  fin_cases i <;>
    norm_num [elevenThreeM,elevenThreeVB2,elevenThreeVB3,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem elevenThree_outputB0 : elevenThreeP (K := K) *ᵥ elevenThreeVB0 = 0 := by
  funext i
  fin_cases i <;>
    norm_num [elevenThreeP,elevenThreeVB0,elevenThreeG,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    change _ = integerPolynomial (K := K) [] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem elevenThree_outputB1 : elevenThreeP (K := K) *ᵥ elevenThreeVB1 = 0 := by
  funext i
  fin_cases i <;>
    norm_num [elevenThreeP,elevenThreeVB1,elevenThreeG,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    change _ = integerPolynomial (K := K) [] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem elevenThree_outputB2 : elevenThreeP (K := K) *ᵥ elevenThreeVB2 = 0 := by
  funext i
  fin_cases i <;>
    norm_num [elevenThreeP,elevenThreeVB2,elevenThreeG,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    change _ = integerPolynomial (K := K) [] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem elevenThree_outputB3 : elevenThreeP (K := K) *ᵥ elevenThreeVB3 = elevenThreeG := by
  funext i
  fin_cases i <;>
    norm_num [elevenThreeP,elevenThreeVB3,elevenThreeG,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,List.getD] <;>
    simp only [← integerPolynomial_zero_cons,← integerPolynomial_add] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem elevenThree_M_degree : DegreeBound (elevenThreeM (K := K)) 1 := by
  intro i j
  fin_cases i <;> (fin_cases j <;> norm_num [elevenThreeM,Polynomial.natDegree_X])

theorem elevenThree_P_degree : DegreeBound (elevenThreeP (K := K)) 1 := by
  intro i j
  fin_cases i <;> (fin_cases j <;> norm_num [elevenThreeP,Polynomial.natDegree_X])

end FD56
