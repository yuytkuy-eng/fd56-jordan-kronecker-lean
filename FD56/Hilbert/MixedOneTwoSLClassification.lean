/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedOneTwoCompletionBases
import FD56.Hilbert.CubicTwoIteration
import FD56.Hilbert.CubicTwoRealization
import FD56.Hilbert.MixedOneTwoSLClosure
import FD56.Hilbert.AdjacentDegrees

/-! Complete SL degree lists when the first auxiliary list has two entries of degree two. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

private theorem one_two_degree_equiv {r : Type*} [Fintype r]
    (a : r → ℕ) (u : ℕ) (ha : ∀ i, 0<a i ∧ a i≤2)
    (hr : Fintype.card r=u+2) (h1 : Fintype.card {i // a i=1}=u) :
    ∃ e : r ≃ Fin u ⊕ Fin 2, ∀ i, mixedKernelDegree 1 u 2 (e i)=a i := by
  classical
  let e1 : {i // a i=1} ≃ Fin u := Fintype.equivOfCardEq (by simpa using h1)
  let e2 : {i // ¬a i=1} ≃ Fin 2 := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl,h1,hr,Fintype.card_fin]
    omega)
  let e := (Equiv.sumCompl (fun i => a i=1)).symm.trans (Equiv.sumCongr e1 e2)
  refine ⟨e,?_⟩
  intro i
  by_cases hi : a i=1
  · simp [e,Equiv.sumCompl_apply_symm_of_pos,hi,mixedKernelDegree]
  · have hi2 : a i=2 := by have := ha i; omega
    simp [e,Equiv.sumCompl_apply_symm_of_neg,hi,hi2,mixedKernelDegree]

variable {K n m : Type*} [Field K] [CharZero K]
  [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

private theorem even_completion_zero :
    (mixedOneTwoEvenCompletion (K := K)).ScalarZero 4 := by
  intro E c hE hc hr
  exact mixedOneTwoEvenBase_scalar_zero E c hE hc hr

private theorem even_completion_selector :
    (mixedOneTwoEvenCompletion (K := K)).ScalarSelector 5
      (fun j : Fin 3 => ![0,5,6] j) := by
  intro E c hE hc hr hs
  exact mixedOneTwoEvenBase_scalar_obstruction E c hE hc hr (hs 0) (hs 1) (hs 2)

private theorem odd_completion_zero :
    (mixedOneTwoOddCompletion (K := K)).ScalarZero 5 := by
  intro E c hE hc hr
  apply mixedOneTwoOddBase_scalar_zero E c _ hc hr
  intro i j
  have hh := hE i j
  dsimp only at hh
  split_ifs at hh ⊢ <;> exact hh

private theorem odd_completion_selector :
    (mixedOneTwoOddCompletion (K := K)).ScalarSelector 6
      (fun _ : Fin 1 => 0) := by
  intro E c hE hc hr hs
  apply mixedOneTwoOddBase_scalar_obstruction E c _ hc hr (hs 0)
  intro i j
  have hh := hE i j
  dsimp only at hh
  split_ifs at hh ⊢ <;> exact hh

theorem generic_mixed_one_two_even_sl_minimal_degrees (k : ℕ) (hk : 0<k)
    (hm : Fintype.card m=2*k+4) (hn : Fintype.card n=4*k+6) (i₀ : n) :
    HasMinimalKernelDegrees (slEquationMatrix (genericAffineSquare K n m)
      (genericAffineRows K n m) i₀)
      (List.replicate (3*k+3) (3*k+5) ++ List.replicate (k+2) (3*k+6)) := by
  let C := cubicCompletionIteration (mixedOneTwoEvenCompletion (K := K)) k
  obtain ⟨e,he⟩ := one_two_degree_equiv (cubicIterationAlpha (fun _ : Fin 2 => 2) k)
    (2*k) (fun i => ⟨cubicIterationAlpha_positive _ (by simp) k i,
      cubicIterationAlpha_le _ (by simp) k i⟩)
    (by rw [iteratedFin_card]) (by rw [cubicIterationAlpha_fiber]; simp)
  have hrow : Fintype.card (IteratedFin 2 4 k)=2*k+4 := iteratedFin_card _ _ _
  have hz := cubicCompletionIteration_even_zero (mixedOneTwoEvenCompletion (K := K))
    mixedOneTwoEvenCoordinates_scaled (by decide) (by simp) even_completion_zero k
  have hs := cubicCompletionIteration_even_selector (mixedOneTwoEvenCompletion (K := K))
    (by decide) (by simp) (fun j : Fin 3 => ![0,5,6] j) even_completion_selector k
  apply generic_mixed_one_two_even_sl_minimal_degrees_of_bounds k hk hm hn i₀
  · apply generic_mixed_one_two_zero_of_completion C (2*k) (3*k+4)
      hm (by omega) hrow e he (by omega) (by rw [cubicIterationBound_eq]; omega) _ i₀
    simpa only [cubicIterationBound_eq,show 4+3*k=3*k+4 by omega] using hz
  · have hu := generic_mixed_one_two_upper_of_completion C (2*k) (3*k+5)
      hm (by omega) hrow e he (by omega) (by rw [cubicIterationBound_eq]; omega)
      (cubicIterationSelector (fun j : Fin 3 => j.val) (fun j : Fin 3 => ![0,5,6] j) k)
      (by simpa only [cubicIterationBound_eq,show 4+3*k+1=3*k+5 by omega] using hs) i₀
    simpa only [iteratedFin_card] using hu

theorem generic_mixed_one_two_odd_sl_minimal_degrees (k : ℕ)
    (hm : Fintype.card m=2*k+5) (hn : Fintype.card n=4*k+8) (i₀ : n) :
    HasMinimalKernelDegrees (slEquationMatrix (genericAffineSquare K n m)
      (genericAffineRows K n m) i₀)
      (List.replicate (k+1) (3*k+6) ++ List.replicate (3*k+6) (3*k+7)) := by
  let alpha : Fin 3 → ℕ := fun j => if j=0 then 1 else 2
  have ha : ∀ j, 0<alpha j ∧ alpha j≤2 := by intro j; dsimp [alpha]; split_ifs <;> decide
  let C := cubicCompletionIteration (mixedOneTwoOddCompletion (K := K)) k
  obtain ⟨e,he⟩ := one_two_degree_equiv (cubicIterationAlpha alpha k) (2*k+1)
    (fun i => ⟨cubicIterationAlpha_positive _ (fun j => (ha j).1) k i,
      cubicIterationAlpha_le _ (fun j => (ha j).2) k i⟩)
    (by rw [iteratedFin_card]) (by
      rw [cubicIterationAlpha_fiber]
      simp [alpha,Fintype.card_subtype,Finset.card_filter,Fin.sum_univ_succ])
  have hrow : Fintype.card (IteratedFin 2 5 k)=(2*k+1)+4 := by rw [iteratedFin_card]
  have hz := cubicCompletionIteration_odd_zero (mixedOneTwoOddCompletion (K := K))
    mixedOneTwoOddCoordinates_scaled (by decide) (fun j => (ha j).2) odd_completion_zero k
  have hs := cubicCompletionIteration_odd_selector (mixedOneTwoOddCompletion (K := K))
    mixedOneTwoOddCoordinates_scaled (by decide) (fun j => (ha j).2)
    (fun _ : Fin 1 => 0) odd_completion_selector k
  apply generic_mixed_one_two_odd_sl_minimal_degrees_of_bounds k hm hn i₀
  · apply generic_mixed_one_two_zero_of_completion C (2*k+1) (3*k+5)
      (by omega) (by omega) hrow e he (by omega) (by rw [cubicIterationBound_eq]; omega) _ i₀
    simpa only [cubicIterationBound_eq,show 5+3*k=3*k+5 by omega] using hz
  · have hu := generic_mixed_one_two_upper_of_completion (n := n) (m := m) C (2*k+1) (3*k+6)
      (by omega) (by omega) hrow e he (by omega) (by rw [cubicIterationBound_eq]; omega)
      (cubicIterationSelector (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0) k)
      (by simpa only [cubicIterationBound_eq,show 5+3*k+1=3*k+6 by omega] using hs) i₀
    simpa only [iteratedFin_card,one_mul] using hu

theorem generic_second_near_double_sl_minimal_degrees
    (hm : 5≤Fintype.card m) (hn : Fintype.card n+2=2*Fintype.card m) (i₀ : n) :
    HasMinimalKernelDegrees (slEquationMatrix (genericAffineSquare K n m)
      (genericAffineRows K n m) i₀)
      (balancedDegreeList (3*(Fintype.card m-1)^2) (2*Fintype.card m-3)) := by
  let k := (Fintype.card m-4)/2
  by_cases heven : (Fintype.card m-4)%2=0
  · have hmk : Fintype.card m=2*k+4 := by dsimp [k]; omega
    have hnk : Fintype.card n=4*k+6 := by omega
    have hk : 0<k := by omega
    have h := generic_mixed_one_two_even_sl_minimal_degrees (K := K) k hk hmk hnk i₀
    have hh := hasMinimalKernelDegrees_balanced_of_adjacent _ (3*k+3) (k+2) (3*k+5)
      (by omega) (by simpa only [Nat.add_assoc,Nat.reduceAdd] using h)
    have hm1 : Fintype.card m-1=2*k+3 := by omega
    have hc : (3*k+3)+(k+2)=2*Fintype.card m-3 := by omega
    have hs : (3*k+5)*((3*k+3)+(k+2))+(k+2)=3*(Fintype.card m-1)^2 := by
      rw [hm1]
      ring
    rw [hs,hc] at hh
    exact hh
  · have hmk : Fintype.card m=2*k+5 := by dsimp [k]; omega
    have hnk : Fintype.card n=4*k+8 := by omega
    have h := generic_mixed_one_two_odd_sl_minimal_degrees (K := K) k hmk hnk i₀
    have hh := hasMinimalKernelDegrees_balanced_of_adjacent _ (k+1) (3*k+6) (3*k+6)
      (by omega) (by simpa only [Nat.add_assoc,Nat.reduceAdd] using h)
    have hm1 : Fintype.card m-1=2*k+4 := by omega
    have hc : (k+1)+(3*k+6)=2*Fintype.card m-3 := by omega
    have hs : (3*k+6)*((k+1)+(3*k+6))+(3*k+6)=3*(Fintype.card m-1)^2 := by
      rw [hm1]
      ring
    rw [hs,hc] at hh
    exact hh

end FD56
