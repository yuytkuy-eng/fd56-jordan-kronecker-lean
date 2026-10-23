/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformGeneralSLClassification
import FD56.Hilbert.UniformThreeSLClassification
import FD56.Hilbert.UniformTwoSLClassification
import FD56.Hilbert.GenericOneColumnSL
import FD56.Hilbert.UniformOneSLClassification

/-! A single interface for all positive uniform SL families with m = ar, n = (a+1)r. -/

noncomputable section
namespace FD56
open Matrix Polynomial

def uniformSLDegreeList (a r : ℕ) : List ℕ :=
  if r = 1 then List.replicate a (a + 1)
  else if a = 1 then [3 * r - 1]
  else if a = 2 then
    if r = 2 then List.replicate 3 5 ++ List.replicate 2 6
    else List.replicate 8 6 ++ List.replicate (r ^ 2 - 7) 7
  else if a = 3 then
    if r = 2 then List.replicate 3 5 ++ List.replicate 6 6
    else List.replicate (r ^ 2 + 8) 6 ++ List.replicate (r ^ 2 - 7) 7
  else
    List.replicate (a + 3 - 3 * r ^ 2) (a + 1) ++
      List.replicate ((a - 4) * r ^ 2 + a + 4 - 2 * (a + 3 - 3 * r ^ 2)) (a + 2) ++
      List.replicate (3 * r ^ 2 - (a + 3)) (a + 3)

theorem generic_uniform_middle_sl_minimal_degrees {K : Type*} [Field K]
    (a r : ℕ) (ha : 2 ≤ a) (hr : 0 < r) (i₀ : Fin ((a + 1) * r)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin ((a + 1) * r)) (Fin (a * r)))
      (genericAffineRows K (Fin ((a + 1) * r)) (Fin (a * r))) i₀)
      (uniformSLDegreeList a r) := by
  have ha1 : a ≠ 1 := by omega
  by_cases hr1 : r = 1
  · subst r
    simpa only [uniformSLDegreeList, if_pos rfl, Fintype.card_fin, Nat.mul_one] using
      (generic_one_more_column_sl_minimal_degrees (K := K)
        (n := Fin ((a + 1) * 1)) (m := Fin (a * 1)) i₀
        (by simp; omega) (by simp))
  · by_cases ha2 : a = 2
    · subst a
      by_cases hr2 : r = 2
      · subst r
        simpa only [uniformSLDegreeList, if_pos rfl, if_neg (by decide : ¬2 = 1)] using
          generic_uniform_two_two_sl_minimal_degrees (K := K) i₀
      · simpa only [uniformSLDegreeList, if_neg hr1, if_neg ha1, if_pos rfl, if_neg hr2] using
          generic_uniform_two_sl_minimal_degrees (K := K) r (by omega) i₀
    · by_cases ha3 : a = 3
      · subst a
        by_cases hr2 : r = 2
        · subst r
          simpa only [uniformSLDegreeList, if_pos rfl, if_neg (by decide : ¬2 = 1),
            if_neg (by decide : ¬3 = 2), if_neg (by decide : ¬3 = 1)] using
            generic_uniform_three_two_sl_minimal_degrees (K := K) i₀
        · simpa only [uniformSLDegreeList, if_neg hr1, if_neg ha1, if_neg ha2, if_pos rfl, if_neg hr2] using
            generic_uniform_three_sl_minimal_degrees (K := K) r (by omega) i₀
      · simpa only [uniformSLDegreeList, if_neg hr1, if_neg ha1, if_neg ha2, if_neg ha3] using
          generic_uniform_sl_minimal_degrees (K := K) a r (by omega) hr i₀

theorem generic_uniform_sl_all_minimal_degrees {K : Type*} [Field K]
    (a r : ℕ) (ha : 0 < a) (hr : 0 < r) (i₀ : Fin ((a + 1) * r)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin ((a + 1) * r)) (Fin (a * r)))
      (genericAffineRows K (Fin ((a + 1) * r)) (Fin (a * r))) i₀)
      (uniformSLDegreeList a r) := by
  by_cases ha1 : a = 1
  · subst a
    generalize hm : 1 * r = m
    have hm' : m = r := by omega
    clear hm
    subst m
    by_cases hr1 : r = 1
    · subst r
      simpa [uniformSLDegreeList] using generic_uniform_one_sl_minimal_degrees (K := K) 1 hr i₀
    · simpa [uniformSLDegreeList, hr1] using
        generic_uniform_one_sl_minimal_degrees (K := K) r hr i₀
  · exact generic_uniform_middle_sl_minimal_degrees a r (by omega) hr i₀

end FD56
