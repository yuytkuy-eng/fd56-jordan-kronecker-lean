/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedOneThreeCompletion1
import FD56.Hilbert.MixedOneThreeCompletion2
import FD56.Hilbert.MixedOneThreeCompletion3
import FD56.Hilbert.MixedOneThreeCompletion4
import FD56.Hilbert.MixedOneThreeIteration
import FD56.Hilbert.MiddleSLClassification

/-! The complete characteristic-zero SL degree list three columns below twice the row count. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m : Type*} [Field K] [CharZero K]
  [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

private theorem three_base2_zero :
    (mixedOneThreeBase2Completion (K := K)).ScalarZero 6 := by
  intro E c hE hc hr
  apply mixedOneThreeBase2_critical E c _ (hc.trans (by decide)) hr
  intro i x
  have hh := hE i x
  change (E i x).natDegree≤6-((if i.val<2 then 1 else 2)+1) at hh
  split_ifs at hh ⊢ <;> omega

private theorem three_base2_selector :
    (mixedOneThreeBase2Completion (K := K)).ScalarSelector 7 (fun j : Fin 0 => j.val) := by
  intro E c hE hc hr hs
  apply mixedOneThreeBase2_critical E c _ hc hr
  intro i x
  have hh := hE i x
  change (E i x).natDegree≤7-((if i.val<2 then 1 else 2)+1) at hh
  split_ifs at hh ⊢ <;> omega

private theorem three_base3_zero :
    (mixedOneThreeBase3Completion (K := K)).ScalarZero 7 := by
  intro E c hE hc hr
  apply mixedOneThreeBase3_zero E c _ (hc.trans (by decide)) hr
  intro i x
  have hh := hE i x
  change (E i x).natDegree≤7-((if i.val<3 then 1 else 2)+1) at hh
  split_ifs at hh ⊢ <;> omega

private theorem three_base3_selector :
    (mixedOneThreeBase3Completion (K := K)).ScalarSelector 8 (fun j : Fin 1 => j.val) := by
  intro E c hE hc hr hs
  apply mixedOneThreeBase3_critical E c _ hc hr (hs 0)
  intro i x
  have hh := hE i x
  change (E i x).natDegree≤8-((if i.val<3 then 1 else 2)+1) at hh
  split_ifs at hh ⊢ <;> omega

private theorem three_base4_zero :
    (mixedOneThreeBase4Completion (K := K)).ScalarZero 8 := by
  intro E c hE hc hr
  apply mixedOneThreeBase4_zero E c _ (hc.trans (by decide)) hr
  intro i x
  have hh := hE i x
  change (E i x).natDegree≤8-((if i.val<4 then 1 else 2)+1) at hh
  split_ifs at hh ⊢ <;> omega

private theorem three_base4_selector :
    (mixedOneThreeBase4Completion (K := K)).ScalarSelector 9 (fun j : Fin 2 => j.val) := by
  intro E c hE hc hr hs
  apply mixedOneThreeBase4_critical E c _ hc hr (hs 0) (hs 1)
  intro i x
  have hh := hE i x
  change (E i x).natDegree≤9-((if i.val<4 then 1 else 2)+1) at hh
  split_ifs at hh ⊢ <;> omega

theorem generic_mixed_one_three_small_sl_balanced
    (hm : Fintype.card m=7) (hn : Fintype.card n=11) (i₀ : n) :
    HasMinimalKernelDegrees (slEquationMatrix (genericAffineSquare K n m)
      (genericAffineRows K n m) i₀) (balancedDegreeList 92 13) := by
  obtain ⟨e,he⟩ := exists_one_two_degree_reindex
    (fun j : Fin 4 => if j.val<1 then 1 else 2) 1 3
    (by decide) (by decide) (by decide)
  apply generic_mixed_one_three_small_sl_balanced_of_zero hm hn i₀
  apply generic_mixed_uniform_zero_of_completion (mixedOneThreeBase1Completion (K := K))
    1 3 6 (by decide) hm hn (by decide) e he (by decide) (by decide) _ i₀
  intro E c hE hc hr
  apply mixedOneThreeBase1_critical E c _ hc hr
  intro i x
  have hh := hE i x
  change (E i x).natDegree≤6-((if i.val<1 then 1 else 2)+1) at hh
  split_ifs at hh ⊢ <;> exact hh

theorem generic_mixed_one_three_sl_balanced (u : ℕ) (hu : 0<u)
    (hm : Fintype.card m=u+6) (hn : Fintype.card n=2*u+9) (i₀ : n) :
    HasMinimalKernelDegrees (slEquationMatrix (genericAffineSquare K n m)
      (genericAffineRows K n m) i₀)
      (balancedDegreeList (3*u^2+27*u+62) (3*u+10)) := by
  by_cases hu1 : u=1
  · subst u
    exact generic_mixed_one_three_small_sl_balanced hm hn i₀
  have hu2 : 2≤u := by omega
  let k := (u-2)/3
  have hcases : u=3*k+2 ∨ u=3*k+3 ∨ u=3*k+4 := by
    dsimp [k]
    omega
  rcases hcases with he | he | he
  · have h := generic_mixed_one_three_iterated_sl_balanced (K := K)
      2 (by decide) (fun j : Fin 5 => if j.val<2 then 1 else 2)
      (by decide) (by decide) _ (mixedOneThreeBase2Completion (K := K))
      mixedOneThreeBase2_jet three_base2_zero (fun j : Fin 0 => j.val)
      three_base2_selector k (by simpa only [he] using hm) (by simpa only [he] using hn) i₀
    simpa only [he] using h
  · have h := generic_mixed_one_three_iterated_sl_balanced (K := K)
      3 (by decide) (fun j : Fin 6 => if j.val<3 then 1 else 2)
      (by decide) (by decide) _ (mixedOneThreeBase3Completion (K := K))
      mixedOneThreeBase3_jet three_base3_zero (fun j : Fin 1 => j.val)
      three_base3_selector k (by simpa only [he] using hm) (by simpa only [he] using hn) i₀
    simpa only [he] using h
  · have h := generic_mixed_one_three_iterated_sl_balanced (K := K)
      4 (by decide) (fun j : Fin 7 => if j.val<4 then 1 else 2)
      (by decide) (by decide) _ (mixedOneThreeBase4Completion (K := K))
      mixedOneThreeBase4_jet three_base4_zero (fun j : Fin 2 => j.val)
      three_base4_selector k (by simpa only [he] using hm) (by simpa only [he] using hn) i₀
    simpa only [he] using h

theorem generic_third_near_double_sl_minimal_degrees
    (hm : 7≤Fintype.card m) (hn : Fintype.card n+3=2*Fintype.card m) (i₀ : n) :
    HasMinimalKernelDegrees (slEquationMatrix (genericAffineSquare K n m)
      (genericAffineRows K n m) i₀)
      (balancedDegreeList (3*(Fintype.card m-2)*(Fintype.card m-1)+2)
        (3*Fintype.card m-8)) := by
  let u := Fintype.card m-6
  have hu : 0<u := by dsimp [u]; omega
  have hmu : Fintype.card m=u+6 := by dsimp [u]; omega
  have hnu : Fintype.card n=2*u+9 := by omega
  have h := generic_mixed_one_three_sl_balanced (K := K) u hu hmu hnu i₀
  have hc : 3*u+10=3*Fintype.card m-8 := by omega
  have hm2 : Fintype.card m-2=u+4 := by omega
  have hm1 : Fintype.card m-1=u+5 := by omega
  have hs : 3*u^2+27*u+62=3*(Fintype.card m-2)*(Fintype.card m-1)+2 := by
    rw [hm2,hm1]
    ring
  rw [hs,hc] at h
  exact h

theorem generic_third_near_double_sl_minimal_degrees_all
    (n m : ℕ) (hm : 4≤m) (hn : n+3=2*m) (i₀ : Fin n) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin n) (Fin m))
      (genericAffineRows K (Fin n) (Fin m)) i₀)
      (balancedDegreeList (3*(m-2)*(m-1)+2) (3*m-8)) := by
  by_cases hm7 : 7≤m
  · simpa only [Fintype.card_fin] using
      generic_third_near_double_sl_minimal_degrees (K := K) (n := Fin n) (m := Fin m)
        (by simpa using hm7) (by simpa using hn) i₀
  have hm6 : m≤6 := by omega
  interval_cases m
  · have hn5 : n=5 := by omega
    subst n
    simpa [balancedDegreeList] using
      generic_one_more_column_sl_minimal_degrees (K := K) (n := Fin 5) (m := Fin 4)
        i₀ (by decide) (by decide)
  · have hn7 : n=7 := by omega
    subst n
    have h := generic_mixed_two_sl_minimal_degrees_le (K := K)
      1 1 (by decide) (by decide) (by decide) i₀
    have hb := hasMinimalKernelDegrees_balanced_of_adjacent
      (slEquationMatrix (genericAffineSquare K (Fin 7) (Fin 5))
        (genericAffineRows K (Fin 7) (Fin 5)) i₀) 4 3 5 (by decide)
      (by simpa using h)
    norm_num at hb ⊢
    exact hb
  · have hn9 : n=9 := by omega
    subst n
    simpa using generic_uniform_two_sl_balanced (K := K) 3 (by decide) i₀

end FD56
