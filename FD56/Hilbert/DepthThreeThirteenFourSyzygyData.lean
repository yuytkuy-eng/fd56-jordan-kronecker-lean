/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeThirteenFourData
import FD56.LinearAlgebra.CofactorKernelComplement
import Mathlib.Data.List.GetD

/-! Compact reduced-syzygy certificates for the thirteen-state, four-row witness. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def thirteenFourSyzygyCoefficients : Fin 4 → Fin 3 → List ℤ :=
  ![ ![[15513, -11262, -6591, 6465, -55480, 19371, 5800, 41054, -11957, -12447], [-5937, 4065, 18097, -28084, -53690, -6431, 27973, 2562, -17089, 14350], [-14, 30, -3, -38, 73, -68, -14, -43, 90, -26, -17]],
    ![[11384, -13237, -4703, -3667, 23227, -19354, -2785, 33517, -22056, -5504], [-39087, -29504, 41912, 30819, -14038, -15158, 28214, -13779, -19155, 15048], [10, 17, -57, 35, -4, 17, -40, -13, 48, -39, 16]],
    ![[0, -45327, 52315, -60561, 15354, 91546, -52893, 42176, 4552, 4494], [0, 24775, -78226, -67164, 46517, -71864, -14922, 39254, -26367, 17266], [0, 50, -68, 69, -131, -37, 130, -131, 96, -47]],
    ![[-1212, -22658, 78359, -56858, 23986, 7829, -48690, -4552, -4494], [-6964, 32881, -20696, 18739, 85285, -34707, 8108, 26367, -17266], [-8, 2, -73, 149, -73, 73, 22, -64, 47]] ]

def thirteenFourSyzygy : Matrix (Fin 4) (Fin 3) K[X] :=
  fun i j => integerPolynomial (thirteenFourSyzygyCoefficients i j)

def thirteenFourBezoutCoefficients : Fin 4 → List ℤ :=
  ![[-4271840383050, 7957526259484, -5526866558715, 6134605692018, -19034878096, 499959664758, -5953616975480, 2421667980775, 4537654018069, 1069857679876, -3531388549076],
    [6990174470673, -8389006229785, 2382379384127, 3179954826699, 103458081480, -1106955764512, -2290731194833, 1846007734107, -1887691783714, 1205613368320, -1030485460853],
    [1241486621744, 14398756966276, -1631404218502, 5876347375745, -4377271694835, 5548504109313, 441366411856, 8813426703637, -2792894543880, 2703258464875, -1554901378317],
    [-1583235817126, -7254699840995, -5642280188869, -513243557769, 4389233912877, -2881542274179, -4729426962975, -822977756143, -2703258464875, 1554901378317, 0]]

def thirteenFourBezout : Fin 4 → K[X] :=
  fun i => integerPolynomial (thirteenFourBezoutCoefficients i)

theorem thirteenFour_syzygy_cofactors :
    rectangularCofactors (thirteenFourSyzygy (K := K)) = C (7235563024 : K) • thirteenFourF := by
  have hcast : C (7235563024 : K) = integerPolynomial (K := K) [7235563024] := by
    rw [integerPolynomial_singleton]
    simpa using (C_eq_intCast (R := K) (7235563024))
  rw [hcast]
  funext i
  fin_cases i <;>
    norm_num only [rectangularCofactors, Matrix.det_fin_three, Matrix.submatrix_apply,
      Fin.succAbove, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
      even_two, Even.neg_pow, one_pow, one_mul, neg_one_mul,
      Pi.smul_apply, smul_eq_mul, thirteenFourSyzygy, thirteenFourSyzygyCoefficients,
      thirteenFourF, thirteenFourTerminalCoefficients, List.getD, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Fin.reduceFinMk, Fin.reduceLT, Fin.reduceAdd, Fin.reduceSub] <;>
    simp only [sub_eq_add_neg, ← integerPolynomial_mul,
      ← integerPolynomial_neg, ← integerPolynomial_add] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem thirteenFour_syzygy_bezout :
    thirteenFourF (K := K) ⬝ᵥ thirteenFourBezout = C (1241486621744 : K) := by
  have hcast : C (1241486621744 : K) = integerPolynomial (K := K) [1241486621744] := by
    rw [integerPolynomial_singleton]
    simpa using (C_eq_intCast (R := K) (1241486621744))
  rw [hcast]
  norm_num only [dotProduct, Fin.sum_univ_succ, thirteenFourF, thirteenFourTerminalCoefficients,
    thirteenFourBezout, thirteenFourBezoutCoefficients, List.getD, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Fin.val_zero, Fin.val_one, Fin.val_two,
    Fin.reduceFinMk, Fin.sum_univ_zero, add_zero]
  simp only [← integerPolynomial_mul, ← integerPolynomial_add]
  apply integerPolynomial_eq_of_trim_eq
  decide

def thirteenFourSyzygyDegrees : Fin 3 → ℕ := ![9,9,10]

theorem thirteenFour_syzygy_degree :
    ∀ i j, (thirteenFourSyzygy (K := K) i j).natDegree ≤ thirteenFourSyzygyDegrees j := by
  have hlen : ∀ i j, (thirteenFourSyzygyCoefficients i j).length ≤ thirteenFourSyzygyDegrees j + 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  intro i j
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [thirteenFourSyzygy, integerPolynomial_coeff, List.getD_eq_default _ _ (by
    have := hlen i j
    omega)]
  simp

theorem thirteenFour_syzygy_leading :
    (fun i j => (thirteenFourSyzygy (K := K) i j).coeff (thirteenFourSyzygyDegrees j)) =
      ![![-12447,14350,-17], ![-5504,15048,16], ![4494,17266,0], ![0,0,0]] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [thirteenFourSyzygy,thirteenFourSyzygyCoefficients,integerPolynomial_coeff,List.getD,thirteenFourSyzygyDegrees]

theorem thirteenFour_syzygy_leading_injective [CharZero K] :
    Function.Injective (Matrix.mulVec (fun i j =>
      (thirteenFourSyzygy (K := K) i j).coeff (thirteenFourSyzygyDegrees j))) := by
  rw [thirteenFour_syzygy_leading]
  let A : Matrix (Fin 3) (Fin 3) K := ![![-12447,14350,-17], ![-5504,15048,16], ![4494,17266,0]]
  have hunit : IsUnit A.det := by
    apply isUnit_iff_ne_zero.mpr
    norm_num [A,Matrix.det_fin_three,Matrix.cons_val_two]
  have hi := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det A).mpr hunit)
  intro v w hvw
  apply hi
  funext i
  fin_cases i
  · simpa [A,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using congrFun hvw 0
  · simpa [A,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using congrFun hvw 1
  · simpa [A,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using congrFun hvw 2

end FD56
