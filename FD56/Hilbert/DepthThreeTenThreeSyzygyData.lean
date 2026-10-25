/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeTenThreeData
import FD56.LinearAlgebra.CofactorKernelComplement
import Mathlib.Data.List.GetD

/-! Compact reduced-syzygy certificates for the ten-state, three-row witness. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def tenThreeSyzygyCoefficients : Fin 3 → Fin 2 → List ℤ :=
  ![ ![[269, 939, -105, -85, 874, -40, 786, 390, 95, -85, -429, -259], [-836, -199, 25, 245, -316, -848, 524, -240, 120, -225, 161, 589]],
    ![[0, -744, 1100, 4164, -744, -514, -1470, -1602, -1032, 762, 352, 650], [0, 236, -3692, -844, 236, 1324, 350, 558, 2502, -358, -542, -400]],
    ![[372, -550, -2082, 372, 257, 735, 1173, 773, -762, -352, -650], [-118, 1846, 422, -118, -662, -175, -397, -1913, 358, 542, 400]] ]

def tenThreeSyzygy : Matrix (Fin 3) (Fin 2) K[X] :=
  fun i j => integerPolynomial (tenThreeSyzygyCoefficients i j)

def tenThreeBezoutCoefficients : Fin 3 → List ℤ :=
  ![[-73156645, -404322185, 697637796, -1241415529, 240852060, 91287034, -1150910110, 163005834, -70377591, 478718167, 274549408, -491604201],
    [40459886, 1095494344, -2483951332, 1046473292, -45835072, 969791078, 385552524, 1644593160, -3109139636, 185923370, -393433586, 265711962],
    [-547747172, 1241975666, -523236646, 22917536, -646735083, -172546319, -1370043752, 2617535435, -185923370, 393433586, -265711962, 0]]

def tenThreeBezout : Fin 3 → K[X] :=
  fun i => integerPolynomial (tenThreeBezoutCoefficients i)

theorem tenThree_syzygy_cofactors :
    rectangularCofactors (tenThreeSyzygy (K := K)) = C (-279250 : K) • tenThreeF := by
  have hcast : C (-279250 : K) = integerPolynomial (K := K) [-279250] := by
    rw [integerPolynomial_singleton]
    simpa using (C_eq_intCast (R := K) (-279250))
  rw [hcast]
  funext i
  fin_cases i <;>
    norm_num only [rectangularCofactors, Matrix.det_fin_two, Matrix.submatrix_apply,
      Fin.succAbove, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
      even_two, Even.neg_pow, one_pow, one_mul, neg_one_mul,
      Pi.smul_apply, smul_eq_mul, tenThreeSyzygy, tenThreeSyzygyCoefficients,
      tenThreeF, tenThreeTerminalCoefficients, List.getD, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Fin.reduceFinMk, Fin.reduceLT, Fin.reduceAdd, Fin.reduceSub] <;>
    simp only [sub_eq_add_neg, ← integerPolynomial_mul,
      ← integerPolynomial_neg, ← integerPolynomial_add] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem tenThree_syzygy_bezout :
    tenThreeF (K := K) ⬝ᵥ tenThreeBezout = C (40459886 : K) := by
  have hcast : C (40459886 : K) = integerPolynomial (K := K) [40459886] := by
    rw [integerPolynomial_singleton]
    simpa using (C_eq_intCast (R := K) (40459886))
  rw [hcast]
  norm_num only [dotProduct, Fin.sum_univ_succ, tenThreeF, tenThreeTerminalCoefficients,
    tenThreeBezout, tenThreeBezoutCoefficients, List.getD, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Fin.val_zero, Fin.val_one, Fin.val_two,
    Fin.reduceFinMk, Fin.sum_univ_zero, add_zero]
  simp only [← integerPolynomial_mul, ← integerPolynomial_add]
  apply integerPolynomial_eq_of_trim_eq
  decide

theorem tenThree_syzygy_degree :
    ∀ i j, (tenThreeSyzygy (K := K) i j).natDegree ≤ 11 := by
  have hlen : ∀ i j, (tenThreeSyzygyCoefficients i j).length ≤ 12 := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  intro i j
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [tenThreeSyzygy, integerPolynomial_coeff, List.getD_eq_default _ _ (by
    have := hlen i j
    omega)]
  simp

theorem tenThree_syzygy_leading :
    (fun i j => (tenThreeSyzygy (K := K) i j).coeff 11) =
      ![![-259,589], ![650,-400], ![0,0]] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tenThreeSyzygy,tenThreeSyzygyCoefficients,integerPolynomial_coeff,List.getD]

theorem tenThree_syzygy_leading_injective [CharZero K] :
    Function.Injective (Matrix.mulVec (fun i j =>
      (tenThreeSyzygy (K := K) i j).coeff 11)) := by
  rw [tenThree_syzygy_leading]
  let A : Matrix (Fin 2) (Fin 2) K := ![![-259,589], ![650,-400]]
  have hunit : IsUnit A.det := by
    apply isUnit_iff_ne_zero.mpr
    norm_num [A,Matrix.det_fin_two]
  have hi := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det A).mpr hunit)
  intro v w hvw
  apply hi
  funext i
  fin_cases i
  · simpa [A,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using congrFun hvw 0
  · simpa [A,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using congrFun hvw 1

end FD56
