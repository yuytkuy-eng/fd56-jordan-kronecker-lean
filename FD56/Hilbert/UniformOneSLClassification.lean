/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformOneAdjugate
import FD56.Hilbert.UniformOneWitness
import FD56.Hilbert.UniformThreeSLRealization
import FD56.Hilbert.MinimalProfile

/-! Scalar coefficient bounds for square cubic auxiliary matrices transfer
to actual generic SL kernels in dimensions (2r,r). -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

theorem exists_uniform_one_sl_upper_witness_of_matrix (r : ℕ) (hr : 0 < r)
    (G : Matrix (Fin r) (Fin r) K[X]) (hG : DegreeBound G 3)
    (hGi : Function.Injective G.mulVec) (k t : ℕ) (f : Fin t → ℕ)
    (hz : ∀ (E : Matrix (Fin r) (Fin r) K[X]) (c : K[X]),
      DegreeBound E k → E * G = (-c) • 1 →
        (∀ j, c.coeff (f j) = 0) → E = 0 ∧ c = 0) :
    ∃ (M : Matrix (Fin (2 * r)) (Fin (2 * r)) K[X])
      (P : Matrix (Fin r) (Fin (2 * r)) K[X]),
      DegreeBound M 1 ∧ DegreeBound P 1 ∧ slHilbert M P (k + 2) ≤ t := by
  let W : Matrix (Fin 1 × Fin r) (Fin r) K[X] := fun x j => G x.2 j
  have hW : DegreeBound W 3 := fun x j => hG x.2 j
  have hWi : Function.Injective W.mulVec := by
    intro v w h
    apply hGi
    funext i
    exact congrFun h (0,i)
  have hzero : ∀ (E : Matrix (Fin r) (Fin 1 × Fin r) K[X]) (c : K[X]),
      DegreeBound E k → E * W = (-c) • 1 →
      (∀ j, c.coeff (f j) = 0) → E = 0 ∧ c = 0 := by
    intro E c hE hrel hc
    let E' : Matrix (Fin r) (Fin r) K[X] := fun i j => E i (0,j)
    have heprod : E' * G = E * W := by
      ext i j
      simp [Matrix.mul_apply, Fintype.sum_prod_type, E', W, Fin.sum_univ_one]
    obtain ⟨he,hc⟩ := hz E' c (fun i j => hE i (0,j)) (heprod.trans hrel) hc
    refine ⟨?_,hc⟩
    funext i x
    have hx : x.1 = 0 := Subsingleton.elim _ _
    have hh := congrFun (congrFun he i) x.2
    simpa only [E', Matrix.zero_apply, ← hx] using hh
  obtain ⟨M, P, hM, hP, hh⟩ := exists_uniform_sl_relation_upper_witness_of_matrix 1 k r
    (by decide) hr W hW hWi t f hzero
  let em : Fin r ≃ Fin (1 * r) := finCongr (by omega)
  refine ⟨M, P.submatrix em (Equiv.refl _), hM, fun i j => hP (em i) j, ?_⟩
  have he := slHilbert_reindex M P em (Equiv.refl _) (k + 2)
  rw [show M = M.submatrix (Equiv.refl _) (Equiv.refl _) from rfl, he]
  have hdeg : 1 + k + 1 = k + 2 := by omega
  simpa only [hdeg] using hh

theorem generic_uniform_one_sl_minimal_degrees_of_upper (r : ℕ) (hr : 0 < r)
    (i₀ : Fin (2 * r))
    (hupper : ∀ d, slHilbert (genericAffineSquare K (Fin (2 * r)) (Fin r))
      (genericAffineRows K (Fin (2 * r)) (Fin r)) d ≤ d + 1 - (3 * r - 1)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (2 * r)) (Fin r))
      (genericAffineRows K (Fin (2 * r)) (Fin r)) i₀) [3 * r - 1] := by
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [← slHilbert_eq_matrix_kernel _ _ i₀]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  exact le_antisymm (hupper d) (generic_uniform_one_slHilbert_lower r hr d)

theorem generic_uniform_one_slHilbert_upper (r : ℕ) (hr : 0 < r) (d : ℕ) :
    slHilbert (genericAffineSquare K (Fin (2 * r)) (Fin r))
      (genericAffineRows K (Fin (2 * r)) (Fin r)) d ≤ d + 1 - (3 * r - 1) := by
  let i₀ : Fin (2 * r) := ⟨0, by omega⟩
  by_cases hd : d < 2
  · rw [generic_uniform_slHilbert_low 1 r (by decide) hr (by simp) (by simp)
      i₀ d (by omega)]
    exact Nat.zero_le _
  obtain ⟨M, P, hM, hP, hh⟩ := exists_uniform_one_sl_upper_witness_of_matrix
    r hr (uniformOneWitness (K := K) r) (uniformOneWitness_degree r)
    (uniformOneWitness_injective r) (d - 2) (d - 2 + 4 - 3 * r)
    (fun j => 3 * r + j.val)
    (fun E c hE hrel hc => uniformOneWitness_scalar_obstruction r hr (d - 2) E c hE hrel hc)
  have hupper := (generic_slHilbert_le_witness M P hM hP i₀ (d - 2 + 2)).trans hh
  have hdegree : d - 2 + 2 = d := by omega
  have hdim : d - 2 + 4 - 3 * r = d + 1 - (3 * r - 1) := by omega
  rwa [hdegree, hdim] at hupper

theorem generic_uniform_one_sl_minimal_degrees (r : ℕ) (hr : 0 < r)
    (i₀ : Fin (2 * r)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (2 * r)) (Fin r))
      (genericAffineRows K (Fin (2 * r)) (Fin r)) i₀) [3 * r - 1] :=
  generic_uniform_one_sl_minimal_degrees_of_upper r hr i₀
    (generic_uniform_one_slHilbert_upper r hr)

theorem generic_uniform_one_slHilbert (r : ℕ) (hr : 0 < r) (d : ℕ) :
    slHilbert (genericAffineSquare K (Fin (2 * r)) (Fin r))
      (genericAffineRows K (Fin (2 * r)) (Fin r)) d = d + 1 - (3 * r - 1) :=
  le_antisymm (generic_uniform_one_slHilbert_upper r hr d)
    (generic_uniform_one_slHilbert_lower r hr d)

end FD56
