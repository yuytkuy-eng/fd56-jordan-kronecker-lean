/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeSixteenFiveData
import FD56.LinearAlgebra.CofactorKernelComplement
import Mathlib.Data.List.GetD

/-! Compact reduced-syzygy certificates for the sixteen-state, five-row witness. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def sixteenFiveSyzygyCoefficients : Fin 5 → Fin 4 → List ℤ :=
  ![ ![[-543209817, 584586302, -1055661556, 361590896, -688251567, -930989479, -374933854, -1030017478, 477336930], [-198112155, -461141648, 131599562, -1331891714, 201176748, -1214859979, -628215473, -1116381372, -33168027], [-930, 327, -784, -501, -167, -2012, -837, -1023, 692, 231], [207, -211, 938, -1324, 1729, -248, 291, -266, -432, 668]],
    ![[347841516, -225867305, -869992677, 1345321894, 76640292, -727854191, 856708208, -1196180372], [-24038578, -1064028385, 1689827958, -1775435177, 410402435, 467509776, -2319716833, -1133717161], [590, -155, -421, -703, 1553, 77, -1384, 195, 332], [280, -497, 1514, -1201, 2428, 1547, -1657, 2026, -470]],
    ![[-114110947, 387396548, -161932970, 409905779, 97785083, -357148906, 477927961, -435564684, -225248911], [445787798, -786638305, 202357790, 922228128, 145512531, 508396457, 90690181, 27623552, -249633669], [-200, -158, 432, 694, -329, -99, -64, -739, -462, -46], [609, -425, 1092, 1201, 40, 181, -239, 577, -227, 77]],
    ![[196319245, -542424987, 307515496, 883408865, -631002319, 1116204996, 780371695, 98929684, 84442393], [411728269, 288774892, -1339612562, 752439514, 1318263542, -581675711, 564147563, 849239845, 1056412643], [551, -842, -680, 2232, -25, 88, 2093, 754, -225, -781], [37, 70, -1345, 1325, 1012, -2013, 905, 483, 367, -483]],
    ![[0, -196319245, 1085634804, -1088421043, 518358433, -121097201, 1549802, -387512341, 409152138], [0, -411728269, -90662737, 1389025941, -1584542237, 8837620, -227739420, -525566629, -139161124], [0, -551, 1772, -198, -1157, 767, 68, -561, 644, 172], [0, -37, -277, 1519, -2370, 1148, 7, -295, -267, 362]] ]

def sixteenFiveSyzygy : Matrix (Fin 5) (Fin 4) K[X] :=
  fun i j => integerPolynomial (sixteenFiveSyzygyCoefficients i j)

def sixteenFiveBezoutCoefficients : Fin 5 → List ℤ :=
  ![[-1793795523146047206286249769800, -2592945111680021185783525888629, -5392212379801591478398383476778, -862259710904021636757566382144, 1818751726756835538886073912512, 5465856925577008089103602396909, 3114095267364630745143888082146, -924056449264311160305474712978, -3117939832301366772445066009552, 85597970243425435588861841891],
    [7370584498881523984935287538391, -574431721842917562461376558786, -3418077731112630124788397148575, -7999925358647050903354586234728, 1040287266322701776688255436015, -3071960140130222898534924957552, 2675647826634274744667928494457, -138962319598725273484323723929, -1257326794914772274265683668508, 0],
    [-181868079409307379721919207058, -299008349034584788736181436199, 1471088946255885354926222066580, 1690110717341323464936614214302, 911462019547109834943635230429, -236569304425414901648268792724, 229416401713213368879169649366, 711211998598176103201734344463, 1870847153870826807944445481163, -759202505658400703098835313382],
    [2163236150800159180747931742549, -317274520377989404139124634875, -297804384097781203641353189949, 2188140231448044802542071989486, -959924299479773954029294764512, -2331123528392433798789768973170, -3651234885746669058286712593087, 3175480628469005479324710881369, 228031576962722007429377945383, 1493244477311259684591813877359],
    [1164239739686769372097826095241, -2163236150800159180747931742549, 2111070043524036610425374404675, -1600966134395895535518704854453, 1358110517931376899247504379618, -3666380159050871552940575524293, 1137428477572738377910680717583, -2873432861287221604903552533659, -2525815059386151730063331153851, -1080718158298313549013827364124]]

def sixteenFiveBezout : Fin 5 → K[X] :=
  fun i => integerPolynomial (sixteenFiveBezoutCoefficients i)

theorem sixteenFive_syzygy_cofactors :
    rectangularCofactors (sixteenFiveSyzygy (K := K)) = C (-33416268238642265571948 : K) • sixteenFiveF := by
  have hcast : C (-33416268238642265571948 : K) = integerPolynomial (K := K) [-33416268238642265571948] := by
    rw [integerPolynomial_singleton]
    simpa using (C_eq_intCast (R := K) (-33416268238642265571948))
  rw [hcast]
  funext i
  fin_cases i <;>
    simp only [rectangularCofactors] <;>
    rw [Matrix.det_succ_row_zero] <;>
    norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.det_fin_three, Matrix.submatrix_apply,
      Fin.succAbove, Fin.castSucc, Fin.castAdd, Fin.succ, Fin.lt_def, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
      even_two, Even.neg_pow, one_pow, one_mul, neg_one_mul,
      Pi.smul_apply, smul_eq_mul, sixteenFiveSyzygy, sixteenFiveSyzygyCoefficients,
      sixteenFiveF, sixteenFiveTerminalCoefficients, List.getD, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ,
      Fin.reduceFinMk, Fin.reduceLT, Fin.reduceAdd, Fin.reduceSub] <;>
    simp only [sub_eq_add_neg, ← integerPolynomial_mul,
      ← integerPolynomial_neg, ← integerPolynomial_add] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem sixteenFive_syzygy_bezout :
    sixteenFiveF (K := K) ⬝ᵥ sixteenFiveBezout = C (1164239739686769372097826095241 : K) := by
  have hcast : C (1164239739686769372097826095241 : K) = integerPolynomial (K := K) [1164239739686769372097826095241] := by
    rw [integerPolynomial_singleton]
    simpa using (C_eq_intCast (R := K) (1164239739686769372097826095241))
  rw [hcast]
  norm_num only [dotProduct, Fin.sum_univ_succ, sixteenFiveF, sixteenFiveTerminalCoefficients,
    sixteenFiveBezout, sixteenFiveBezoutCoefficients, List.getD, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ, Fin.val_zero, Fin.val_one, Fin.val_two,
    Fin.reduceFinMk, Fin.sum_univ_zero, add_zero]
  simp only [← integerPolynomial_mul, ← integerPolynomial_add]
  apply integerPolynomial_eq_of_trim_eq
  decide

def sixteenFiveSyzygyDegrees : Fin 4 → ℕ := ![8,8,9,9]

theorem sixteenFive_syzygy_degree :
    ∀ i j, (sixteenFiveSyzygy (K := K) i j).natDegree ≤ sixteenFiveSyzygyDegrees j := by
  have hlen : ∀ i j, (sixteenFiveSyzygyCoefficients i j).length ≤ sixteenFiveSyzygyDegrees j + 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  intro i j
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [sixteenFiveSyzygy, integerPolynomial_coeff, List.getD_eq_default _ _ (by
    have := hlen i j
    omega)]
  simp

theorem sixteenFive_syzygy_leading :
    (fun i j => (sixteenFiveSyzygy (K := K) i j).coeff (sixteenFiveSyzygyDegrees j)) =
      ![![477336930,-33168027,231,668], ![0,0,0,0], ![-225248911,-249633669,-46,77], ![84442393,1056412643,-781,-483], ![409152138,-139161124,172,362]] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sixteenFiveSyzygy,sixteenFiveSyzygyCoefficients,integerPolynomial_coeff,List.getD,sixteenFiveSyzygyDegrees]

theorem sixteenFive_syzygy_leading_injective [CharZero K] :
    Function.Injective (Matrix.mulVec (fun i j =>
      (sixteenFiveSyzygy (K := K) i j).coeff (sixteenFiveSyzygyDegrees j))) := by
  rw [sixteenFive_syzygy_leading]
  let A : Matrix (Fin 4) (Fin 4) K := ![![477336930,-33168027,231,668], ![-225248911,-249633669,-46,77], ![84442393,1056412643,-781,-483], ![409152138,-139161124,172,362]]
  let AI : Matrix (Fin 4) (Fin 4) ℤ := ![![477336930,-33168027,231,668], ![-225248911,-249633669,-46,77], ![84442393,1056412643,-781,-483], ![409152138,-139161124,172,362]]
  have hmap : A = AI.map (Int.castRingHom K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A,AI]
  have hdet : AI.det = -33416268238642265571948 := by decide
  have hdetmap : (AI.map (Int.castRingHom K)).det = (Int.castRingHom K) AI.det :=
    ((Int.castRingHom K).map_det AI).symm
  have hunit : IsUnit A.det := by
    apply isUnit_iff_ne_zero.mpr
    rw [hmap,hdetmap,hdet]
    norm_num
  have hi := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det A).mpr hunit)
  intro v w hvw
  apply hi
  funext i
  fin_cases i
  · simpa [A,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using congrFun hvw 0
  · simpa [A,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using congrFun hvw 2
  · simpa [A,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using congrFun hvw 3
  · simpa [A,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using congrFun hvw 4

end FD56
