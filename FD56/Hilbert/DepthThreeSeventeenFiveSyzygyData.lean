/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeSeventeenFiveData
import FD56.Hilbert.KernelDegreesFromBezout

/-! A reduced relation matrix with an exact Bezout certificate for its maximal minors. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

def seventeenFiveSyzygyCoefficients : Matrix (Fin 5) (Fin 3) (List ℤ) :=
  ![![[0, 7838029849928, -12949571682141, -14919523576786, 9583276309425, -75576814198202, -159292525019986, 27735769043075, 38444524462303, -41405012945368, -109473731304903, 45732615399964, 55907095779581], [0, 2076483235737, 1984793887243, -15852004693339, -27128785413658, 37849578099590, 35373134603441, -33790877562738, -28553185224218, 41933432391225, 16669884266704, -5552581595485, -11712089519251, -920755172777], [0, -7066036962218, 2219752085390, 25077340430758, 20602691116656, -3954160094356, 53256775642606, 37145301504560, -2551028881240, -26820263319210, 44058261376844, -1780246730718, -21028717456062, -5682207073406]],
    ![[0, -17230804355606, 4226095393997, -14265507531843, -34764451059090, -1517349161141, 22783648192926, -20313122667620, -31494178932272, 107229383686713, -91976089095339, -73762489862611, 3400136254291], [0, -3669208922266, 4843278471992, 6151058261883, -4410928487922, -3601057846107, 747582603737, 14774070068313, -13514978621050, -27480744875340, 13347258053822, 23182020666860, -9249425563164, 3669564797942], [0, 11001269607508, -4890271220716, 1152789580950, 22087776749380, 7325200617098, -14446285980586, -7755983768610, 32786892800412, -22849699192404, 15740908859656, 25651551323788, 15123838174780, -4732278734316]],
    ![[4757152532806, 1175372492288, -4224549015706, 26158123542696, 12674987669332, 47470376525087, 59751458697047, 72399017057820, 14032927172605], [-1387934099439, 638641871703, -18854765096, 8772757293451, -3548566049043, -11068726910107, -6652818469384, 3285964046965, -4603775863885], [-965472321114, -1810994622030, 1780863708584, -19018234970566, -4216108326866, -13433678691518, -27885288433596, -43297175637090, -7795564819290]],
    ![[17230804355606, -4226095393997, 14265507531843, 30007298526284, 341976668853, -18559099177220, 28616607836136, 44828609186158, -100159327224896, 102803746660940, 88242293274175, -593550819770], [3669208922266, -4843278471992, -6151058261883, 5798862587361, 2962415974404, -728727838641, -16208409517232, 14715405570641, 23899216162229, -14309519678588, -22524827857467, 8328670390387, -3669564797942], [-11001269607508, 4890271220716, -1152789580950, -21122304428266, -5514205995068, 12665422272002, 4771679524160, -40792781247130, 21755801948438, -20694321360832, -34310986451206, -16682951138638, 4732278734316]],
    ![[-7838029849928, 12949571682141, -7068433311626, -23763357763322, 52531146720456, 110318495168766, -72020830477778, -45487556866255, 9890618317790, 105170771447825, -32098372399842, -41427292368017, 2806585434521], [-2076483235737, -1984793887243, 13570729870512, 27664213091681, -30505595522885, -35281208828112, 33555153762173, 34378519643002, -35872481687747, -17657012416810, 0, 12369282328644], [7066036962218, -2219752085390, -13110598502136, -12680698107834, 9437084353514, -27854987491048, -11250891560202, 2620413183560, 34865132203414, -37533413274880, 0, 12369282328644, 4123094109548]]]

def seventeenFiveSyzygy : Matrix (Fin 5) (Fin 3) K[X] :=
  fun i j => integerPolynomial (seventeenFiveSyzygyCoefficients i j)

def seventeenFiveMinorRows : Fin 10 → Fin 3 → Fin 5 :=
  ![![0, 1, 2],
    ![0, 1, 3],
    ![0, 1, 4],
    ![0, 2, 3],
    ![0, 2, 4],
    ![0, 3, 4],
    ![1, 2, 3],
    ![1, 2, 4],
    ![1, 3, 4],
    ![2, 3, 4]]

def seventeenFiveMinorCoefficients : Fin 10 → List ℤ :=
  ![[0, 0, -1, 0, 3, 0, -3, -1, 6, 7, -7, -11, 8, -7, -4, 48, 24, -46, -40, 4, 30, 86, -79, -216, 6, 160, 16, 32, 31, -70, -7, 19, -13, 0, 5],
    [0, 0, 0, 0, 0, 1, 0, -3, 0, 3, 1, -2, -5, -11, 9, 20, -13, -16, 22, 12, 0, 20, -24, -28, 22, -1, -44, 4, 40, -8, 6, 11, -18, -1, 5, -3, 0, 1],
    [0, 0, 0, 0, 1, 0, -3, -1, 2, 5, -2, -8, 13, 9, -27, 12, 29, -29, -34, 12, -3, 35, 64, -80, -67, 114, 8, -74, 17, -38, -3, 43, 5, -2, -4, -3, -2, 0, 1],
    [0, -1, 0, 3, 0, -3, -1, 4, 5, -3, -5, 8, -11, -6, 50, 42, -42, -58, 6, 52, 74, -89, -212, 6, 150, 14, 38, 33, -70, -7, 19, -13, 0, 5],
    [0, 0, 0, 1, 1, -2, -4, -1, 4, 2, -5, -8, 4, 1, -11, -13, -5, -37, -42, -1, 77, 39, -56, -37, 65, 82, 15, -51, -56, -3, 20, 5],
    [0, 0, 0, -1, 0, 3, 0, -3, -3, 4, 7, -13, -7, 30, 0, -27, 14, 31, -5, -12, -38, -68, 61, 72, -97, -2, 65, -10, 50, 8, -50, -17, 1, 8, 4, 2, 0, -1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -2, 2, 4, 2, 4, -4, -2, 16, 8, -16, 10, 0, -10],
    [0, 1, 0, -3, 0, 3, 1, -6, -7, 8, 11, -11, 5, 2, -42, -23, 40, 38, -3, -56, -93, 83, 209, -46, -191, 11, 14, 9, 60, -18, -19, 13, 0, -5],
    [0, 0, 0, 0, -1, 0, 3, 0, -3, -1, 2, 5, 10, -9, -19, 13, 20, -22, -11, 6, -14, 15, 30, -29, -17, 51, -10, -43, 11, 0, -1, 16, -4, -5, 3, 0, -1],
    [1, 0, -3, 0, 3, 1, -4, -5, 4, 5, -11, 9, 4, -46, -43, 36, 58, -3, -76, -81, 91, 211, -46, -181, 13, 8, 7, 60, -18, -19, 13, 0, -5]]

def seventeenFiveMinor : Fin 10 → K[X] :=
  fun i => integerPolynomial (seventeenFiveMinorCoefficients i)

def seventeenFiveBezoutCoefficients : Fin 10 → List ℤ :=
  ![[-99257568471772280845109370808667873, 30685289918949393765016104293270895, 30471322446460808584687537533887424, -394236478742141891456300454046887888, 54841898604733118770417430521420299],
    [-322573001072630424571882629927029772, -19044350965846166866507576373389659, -44611153975250037686259945478329802, 15600688900263027040388381058019486, -39847384833808061354129839395710994],
    [-153925991286906089034819025752139040, -209947948771531255646626442977838308, 76831796486700123690355744806504774, 33733015299718323726385835722709270, 0],
    [103532573470635774482683306396569766, 181103470969603394707942635055965683, -82265979256289860469446458261956143, 82862297844967460199903159799892512, 311959854869969492263155294432272128],
    [-77551521954804474485588157362048640, 82332743941650831967641493105197148, 14733440234919629756671139398168354, -61306818485719491312068990925898828, 107424913558468029744704387241676292],
    [-36116192392841680467094028783642916, -239254986333903917550410549415136366, -214711717912973231978756549060457116, 92432485386963150730744125864524260, -6114369534089737627744003673001724],
    [199513701320279553108794801874860004, 163402907482775529205595518158863281, -351134851214952433455940631516764293, 224865704979761287588127670951958619, 1298197752573804387870103583429355],
    [103532573470635774482683306396569766, 87343736922787990529106743705763780, -10145359775377672685936225390279524, 63760549069460422254479309077624456, -47685051014039318490508456260252874],
    [29541476961962586134986512233058414, -261870385376303754742966852195909226, 0, 0, 0],
    [1832611474985625555424493152821990, 0, 0, 0, 0]]

def seventeenFiveBezout : Fin 10 → K[X] :=
  fun i => integerPolynomial (seventeenFiveBezoutCoefficients i)

theorem seventeenFive_syzygy_relation :
    (seventeenFiveF (K := K)).transpose * seventeenFiveSyzygy (K := K) = 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
      Matrix.submatrix_apply, seventeenFiveSyzygy, seventeenFiveSyzygyCoefficients,
      seventeenFiveF, seventeenFiveTerminalCoefficients,
      seventeenFiveMinorRows, seventeenFiveMinor, seventeenFiveMinorCoefficients,
      seventeenFiveBezout,seventeenFiveBezoutCoefficients,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ,
      Fin.val_zero, Fin.val_one, Fin.val_two, Fin.reduceFinMk] <;>
    simp only [← integerPolynomial_mul, ← integerPolynomial_add] <;>
    change _ = integerPolynomial (K := K) [] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem seventeenFive_syzygy_minor (i : Fin 10) :
    ((seventeenFiveSyzygy (K := K)).submatrix (seventeenFiveMinorRows i) id).det =
      integerPolynomial [70749800997046548362597663733543613664] * seventeenFiveMinor i := by
  fin_cases i <;>
    norm_num only [Matrix.det_fin_three, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
      Matrix.submatrix_apply, seventeenFiveSyzygy, seventeenFiveSyzygyCoefficients,
      seventeenFiveF, seventeenFiveTerminalCoefficients,
      seventeenFiveMinorRows, seventeenFiveMinor, seventeenFiveMinorCoefficients,
      seventeenFiveBezout,seventeenFiveBezoutCoefficients,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ,
      Fin.val_zero, Fin.val_one, Fin.val_two, Fin.reduceFinMk] <;>
    simp only [sub_eq_add_neg, ← integerPolynomial_mul,
      ← integerPolynomial_neg, ← integerPolynomial_add] <;>
    apply integerPolynomial_eq_of_trim_eq <;> decide

theorem seventeenFive_minor_bezout :
    (∑ i : Fin 10, seventeenFiveBezout (K := K) i * seventeenFiveMinor i) =
      integerPolynomial [1832611474985625555424493152821990] := by
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
      Matrix.submatrix_apply, seventeenFiveSyzygy, seventeenFiveSyzygyCoefficients,
      seventeenFiveF, seventeenFiveTerminalCoefficients,
      seventeenFiveMinorRows, seventeenFiveMinor, seventeenFiveMinorCoefficients,
      seventeenFiveBezout,seventeenFiveBezoutCoefficients,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ,
      Fin.val_zero, Fin.val_one, Fin.val_two, Fin.reduceFinMk]
  simp only [← integerPolynomial_mul, ← integerPolynomial_add]
  apply integerPolynomial_eq_of_trim_eq
  decide

def seventeenFiveSyzygyDegrees : Fin 3 → ℕ := ![12,13,13]

theorem seventeenFive_syzygy_degree :
    ∀ i j, (seventeenFiveSyzygy (K := K) i j).natDegree ≤ seventeenFiveSyzygyDegrees j := by
  have hlen : ∀ i j, (seventeenFiveSyzygyCoefficients i j).length ≤ seventeenFiveSyzygyDegrees j + 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  intro i j
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [seventeenFiveSyzygy, integerPolynomial_coeff, List.getD_eq_default _ _ (by
    have := hlen i j
    omega)]
  simp

theorem seventeenFive_syzygy_leading :
    (fun i j => (seventeenFiveSyzygy (K := K) i j).coeff (seventeenFiveSyzygyDegrees j)) =
      ![![55907095779581, -920755172777, -5682207073406],
    ![3400136254291, 3669564797942, -4732278734316],
    ![0, 0, 0],
    ![0, 0, 0],
    ![2806585434521, 0, 0]] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [seventeenFiveSyzygy,seventeenFiveSyzygyCoefficients,integerPolynomial_coeff,List.getD,seventeenFiveSyzygyDegrees]

theorem seventeenFive_syzygy_leading_injective [CharZero K] :
    Function.Injective (Matrix.mulVec (fun i j =>
      (seventeenFiveSyzygy (K := K) i j).coeff (seventeenFiveSyzygyDegrees j))) := by
  rw [seventeenFive_syzygy_leading]
  let A : Matrix (Fin 3) (Fin 3) K := ![![55907095779581, -920755172777, -5682207073406],
    ![3400136254291, 3669564797942, -4732278734316],
    ![2806585434521, 0, 0]]
  let AI : Matrix (Fin 3) (Fin 3) ℤ := ![![55907095779581, -920755172777, -5682207073406],
    ![3400136254291, 3669564797942, -4732278734316],
    ![2806585434521, 0, 0]]
  have hmap : A = AI.map (Int.castRingHom K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A,AI]
  have hdet : AI.det = 70749800997046548362597663733543613664 := by decide
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
  · simpa [A,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using congrFun hvw 1
  · simpa [A,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using congrFun hvw 4

end FD56
