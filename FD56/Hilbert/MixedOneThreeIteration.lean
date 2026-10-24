/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformCubicIteration
import FD56.Hilbert.UniformCubicRealization
import FD56.Hilbert.MixedOneThreeSLClosure

/-! From the three finite scalar obstructions to all larger dimensions. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

theorem exists_one_two_degree_reindex {r : Type*} [Fintype r]
    (a : r → ℕ) (u v : ℕ) (ha : ∀ i, 0<a i ∧ a i≤2)
    (hr : Fintype.card r=u+v) (h1 : Fintype.card {i // a i=1}=u) :
    ∃ e : r ≃ Fin u ⊕ Fin v, ∀ i, mixedKernelDegree 1 u v (e i)=a i := by
  classical
  let e1 : {i // a i=1} ≃ Fin u := Fintype.equivOfCardEq (by simpa using h1)
  let e2 : {i // ¬a i=1} ≃ Fin v := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl,h1,hr,Fintype.card_fin]
    omega)
  let e := (Equiv.sumCompl (fun i => a i=1)).symm.trans (Equiv.sumCongr e1 e2)
  refine ⟨e,?_⟩
  intro i
  by_cases hi : a i=1
  · simp [e,Equiv.sumCompl_apply_symm_of_pos,hi,mixedKernelDegree]
  · have hi2 : a i=2 := by have := ha i; omega
    simp [e,Equiv.sumCompl_apply_symm_of_neg,hi,hi2,mixedKernelDegree]

variable {K n m : Type*} [Field K]
  [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem generic_mixed_one_three_iterated_sl_balanced
    (s : ℕ) (hs : 2≤s) (alpha : Fin (s+3) → ℕ)
    (ha : ∀ i, 0<alpha i ∧ alpha i≤2)
    (h1 : Fintype.card {i // alpha i=1}=s)
    (W : Matrix (Fin 3) (Fin 3) K[X])
    (C : UniformCubicCompletion (m := Fin (s+6)) alpha (s+4) W)
    (hjet : Function.Injective (Matrix.mulVec
      (fun (ij : Fin 3 × Fin 3) (j : Fin 3) => (W ij.1 ij.2).coeff (2-j.val))))
    (hzero : C.ScalarZero (s+4)) (f : Fin (s-2) → ℕ)
    (hselector : C.ScalarSelector (s+5) f) (k : ℕ)
    (hm : Fintype.card m=(3*k+s)+6) (hn : Fintype.card n=2*(3*k+s)+9) (i₀ : n) :
    HasMinimalKernelDegrees (slEquationMatrix (genericAffineSquare K n m)
      (genericAffineRows K n m) i₀)
      (balancedDegreeList (3*(3*k+s)^2+27*(3*k+s)+62) (3*(3*k+s)+10)) := by
  let D := uniformCubicIteration C k
  obtain ⟨e,he⟩ := exists_one_two_degree_reindex (uniformCubicAlpha 3 alpha k) (3*k+s) 3
    (uniformCubicAlpha_range 3 alpha ha k)
    (by rw [iteratedFin_card]; omega)
    (by rw [uniformCubicAlpha_fiber,h1]; simp)
  have hrow : Fintype.card (IteratedFin 3 (s+6) k)=(3*k+s)+2*3 := by
    rw [iteratedFin_card]
    omega
  have hz := uniformCubicIteration_zero C (by omega) ha hjet hzero k
  have hsel := uniformCubicIteration_selector C (by omega) ha f
    (by simpa only [Nat.add_assoc,Nat.reduceAdd] using hselector) k
  apply generic_mixed_one_three_sl_balanced_of_bounds (3*k+s) (by omega) hm hn i₀
  · apply generic_mixed_uniform_zero_of_completion D (3*k+s) 3 (3*k+s+4)
      (by decide) hm hn hrow e he (by omega)
      (by rw [cubicIterationBound_eq]; omega) _ i₀
    simpa only [cubicIterationBound_eq,show s+4+3*k=3*k+s+4 by omega] using hz
  · have hu := generic_mixed_uniform_upper_of_completion D (3*k+s) 3 (3*k+s+5)
      (by decide) hm hn hrow e he (by omega)
      (by rw [cubicIterationBound_eq]; omega)
      (cubicIterationSelector (fun j : Fin 3 => j.val) f k)
      (by simpa only [cubicIterationBound_eq,show s+4+3*k+1=3*k+s+5 by omega] using hsel) i₀
    rw [iteratedFin_card] at hu
    omega

end FD56
