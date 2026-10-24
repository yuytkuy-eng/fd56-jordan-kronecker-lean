/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeBetaSingleTest

/-! Explicit polynomial data for a depth-three witness with seven states and two rows. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]

def sevenTwoM : Matrix (Fin 7) (Fin 7) K[X] :=
  ![![0, 0, (1), 0, 0, 0, 0], ![0, 0, 0, 0, (1), (1) * X, (1) * X], ![0, (1), 0, 0, (1) * X, 0, (1) * X], ![0, 0, 0, 0, (1) * X, 0, 0], ![(1) * X, 0, 0, 0, 0, 0, 0], ![(1), 0, 0, 0, 0, 0, 0], ![0, 0, 0, (1) * X, 0, (1), 0]]

def sevenTwoP : Matrix (Fin 2) (Fin 7) K[X] :=
  ![![0, 0, (1) * X, 0, 0, 0, (1)], ![(1), (1) * X, 0, (1), 0, 0, 0]]

def sevenTwoV0 : Fin 7 → K[X] :=
  ![(1) * X + (1) * X^2 + (-3) * X^5 + (-2) * X^7 + (3) * X^8 + (1) * X^10 + (-1) * X^11, (1) * X + (-1) * X^3 + (-3) * X^4 + (4) * X^6 + (9) * X^8 + (-9) * X^9 + (2) * X^10, (2) * X + (1) * X^4 + (-2) * X^5 + (9) * X^6 + (-9) * X^7 + (4) * X^8 + (-3) * X^10 + (1) * X^11, (-1) * X + (-2) * X^2 + (1) * X^4 + (6) * X^5 + (-2) * X^7 + (-3) * X^8 + (-9) * X^9 + (8) * X^10 + (-1) * X^11, (-1) + (-6) * X^5 + (4) * X^6 + (3) * X^8 + (-1) * X^9 + (-3) * X^11 + (1) * X^12, (1) * X^2 + (2) * X^3 + (3) * X^4 + (2) * X^5 + (-6) * X^6 + (3) * X^7 + (-4) * X^8 + (3) * X^9 + (6) * X^10 + (-5) * X^11 + (1) * X^12, (-2) * X^2 + (-1) * X^5 + (2) * X^6 + (-9) * X^7 + (9) * X^8 + (-4) * X^9 + (3) * X^11 + (-1) * X^12]

def sevenTwoV1 : Fin 7 → K[X] :=
  ![(2) * X + (1) * X^4 + (-2) * X^5 + (9) * X^6 + (-9) * X^7 + (4) * X^8 + (-3) * X^10 + (1) * X^11, (-1) + (-1) * X^3 + (2) * X^4 + (-3) * X^5 + (5) * X^6 + (-4) * X^7 + (-3) * X^8 + (4) * X^9 + (-1) * X^10 + (3) * X^11 + (-1) * X^12, (-3) * X^3 + (-3) * X^4 + (-3) * X^6 + (6) * X^7 + (3) * X^9 + (-3) * X^10, (-1) * X + (-6) * X^6 + (4) * X^7 + (3) * X^9 + (-1) * X^10 + (-3) * X^12 + (1) * X^13, (1) * X^2 + (1) * X^3 + (-3) * X^6 + (-2) * X^8 + (3) * X^9 + (1) * X^11 + (-1) * X^12, (1) * X + (1) * X^2 + (-3) * X^5 + (-2) * X^7 + (3) * X^8 + (1) * X^10 + (-1) * X^11, (3) * X^4 + (3) * X^5 + (3) * X^7 + (-6) * X^8 + (-3) * X^10 + (3) * X^11]

def sevenTwoV2 : Fin 7 → K[X] :=
  ![(-3) * X^3 + (-3) * X^4 + (-3) * X^6 + (6) * X^7 + (3) * X^9 + (-3) * X^10, (2) * X^2 + (2) * X^3 + (3) * X^5 + (-3) * X^6 + (-1) * X^8 + (-1) * X^11 + (1) * X^12, (-1) + (3) * X^4 + (8) * X^6 + (-7) * X^7 + (-4) * X^9 + (2) * X^10 + (3) * X^12 + (-1) * X^13, (1) * X^3 + (1) * X^4 + (-3) * X^7 + (-2) * X^9 + (3) * X^10 + (1) * X^12 + (-1) * X^13, (2) * X^2 + (1) * X^5 + (-2) * X^6 + (9) * X^7 + (-9) * X^8 + (4) * X^9 + (-3) * X^11 + (1) * X^12, (2) * X + (1) * X^4 + (-2) * X^5 + (9) * X^6 + (-9) * X^7 + (4) * X^8 + (-3) * X^10 + (1) * X^11, (1) * X + (-3) * X^5 + (-8) * X^7 + (7) * X^8 + (4) * X^10 + (-2) * X^11 + (-3) * X^13 + (1) * X^14]

set_option maxHeartbeats 2000000 in
def sevenTwoV3 : Fin 7 → K[X] :=
  ![(-1) + (3) * X^4 + (8) * X^6 + (-7) * X^7 + (-4) * X^9 + (2) * X^10 + (3) * X^12 + (-1) * X^13, (5) * X^2 + (2) * X^5 + (-7) * X^6 + (18) * X^7 + (-26) * X^8 + (15) * X^9 + (-2) * X^11 + (-3) * X^14 + (1) * X^15, (3) * X^2 + (4) * X^3 + (3) * X^5 + (-5) * X^6 + (-2) * X^7 + (-2) * X^9 + (4) * X^10 + (3) * X^11 + (-4) * X^12 + (1) * X^13 + (-3) * X^14 + (1) * X^15, (2) * X^3 + (1) * X^6 + (-2) * X^7 + (9) * X^8 + (-9) * X^9 + (4) * X^10 + (-3) * X^12 + (1) * X^13, (-3) * X^4 + (-3) * X^5 + (-3) * X^7 + (6) * X^8 + (3) * X^10 + (-3) * X^11, (-3) * X^3 + (-3) * X^4 + (-3) * X^6 + (6) * X^7 + (3) * X^9 + (-3) * X^10, (2) * X + (2) * X^4 + (-1) * X^5 + (9) * X^6 + (-9) * X^7 + (1) * X^8 + (-5) * X^10 + (4) * X^11 + (1) * X^13 + (-1) * X^14]

def sevenTwoF0 : K[X] :=
  (2) * X + (3) * X^3 + (6) * X^4 + (-1) * X^5 + (12) * X^6 + (-14) * X^7 + (-1) * X^8 + (-7) * X^10 + (8) * X^11 + (3) * X^12 + (-3) * X^13 + (-3) * X^15 + (1) * X^16

def sevenTwoF1 : K[X] :=
  (-1) + (7) * X^3 + (3) * X^4 + (11) * X^6 + (-16) * X^7 + (27) * X^8 + (-39) * X^9 + (21) * X^10 + (-2) * X^12 + (-3) * X^15 + (1) * X^16

def sevenTwoU : K[X] :=
  (-135442849351680354650092) + (200347162597317846346187) * X + (-283069049204689382151100) * X^2 + (1770762673252767873587778) * X^3 + (-2337070785447598874720358) * X^4 + (4110084347195596111942476) * X^5 + (-5321008586414695637299303) * X^6 + (6493561607015120496539104) * X^7 + (-5986089004091684721615698) * X^8 + (2432743137122293487164429) * X^9 + (90538744813759144547833) * X^10 + (-177725011801879162919564) * X^11 + (-116697776793587306233600) * X^12 + (235806184078438709788166) * X^13 + (-419708528174534831452129) * X^14 + (117462045523254836951345) * X^15

def sevenTwoW : K[X] :=
  (-49592742382823085437211) + (-270885698703360709300184) * X + (400694325194635692692374) * X^2 + (-1319615843144181426312953) * X^3 + (1284931620115412936900644) * X^4 + (-2193619713321310742220736) * X^5 + (1427632971467460603671525) * X^6 + (404196405403995690232621) * X^7 + (-639795568632769596242875) * X^8 + (1180035977042753585532719) * X^9 + (-592106123183562993186471) * X^10 + (-611552390628705983631443) * X^11 + (469083913363351817087635) * X^12 + (-235806184078438709788166) * X^13 + (419708528174534831452129) * X^14 + (-117462045523254836951345) * X^15

set_option maxHeartbeats 2000000 in
theorem sevenTwo_bezout : sevenTwoU (K := K)*sevenTwoF0 + sevenTwoW*sevenTwoF1 = 49592742382823085437211 := by
  unfold sevenTwoU sevenTwoW sevenTwoF0 sevenTwoF1
  ring

set_option maxHeartbeats 2000000 in
theorem sevenTwo_step0 : sevenTwoM (K := K) *ᵥ sevenTwoV0 = sevenTwoV1 := by
  funext i
  fin_cases i <;> norm_num [sevenTwoM,sevenTwoV0,sevenTwoV1,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 2000000 in
theorem sevenTwo_step1 : sevenTwoM (K := K) *ᵥ sevenTwoV1 = sevenTwoV2 := by
  funext i
  fin_cases i <;> norm_num [sevenTwoM,sevenTwoV1,sevenTwoV2,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 2000000 in
theorem sevenTwo_step2 : sevenTwoM (K := K) *ᵥ sevenTwoV2 = sevenTwoV3 := by
  funext i
  fin_cases i <;> norm_num [sevenTwoM,sevenTwoV2,sevenTwoV3,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 2000000 in
theorem sevenTwo_output0 : sevenTwoP (K := K) *ᵥ sevenTwoV0 = 0 := by
  funext i
  fin_cases i <;> norm_num [sevenTwoP,sevenTwoV0,sevenTwoF0,sevenTwoF1,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 2000000 in
theorem sevenTwo_output1 : sevenTwoP (K := K) *ᵥ sevenTwoV1 = 0 := by
  funext i
  fin_cases i <;> norm_num [sevenTwoP,sevenTwoV1,sevenTwoF0,sevenTwoF1,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 2000000 in
theorem sevenTwo_output2 : sevenTwoP (K := K) *ᵥ sevenTwoV2 = 0 := by
  funext i
  fin_cases i <;> norm_num [sevenTwoP,sevenTwoV2,sevenTwoF0,sevenTwoF1,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 2000000 in
theorem sevenTwo_output3 : sevenTwoP (K := K) *ᵥ sevenTwoV3 = ![sevenTwoF0,sevenTwoF1] := by
  funext i
  fin_cases i <;> norm_num [sevenTwoP,sevenTwoV3,sevenTwoF0,sevenTwoF1,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem sevenTwo_M_degree : DegreeBound (sevenTwoM (K := K)) 1 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [sevenTwoM,Polynomial.natDegree_X]

theorem sevenTwo_P_degree : DegreeBound (sevenTwoP (K := K)) 1 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [sevenTwoP,Polynomial.natDegree_X]

end FD56
