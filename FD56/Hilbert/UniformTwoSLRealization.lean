/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformWitnessExtension
import FD56.Hilbert.UniformTwoCoreWitness
import FD56.Hilbert.UniformTwoSmallWitness
import FD56.Hilbert.UniformThreeSLRealization

/-! Realization of the two-block scalar obstruction by affine SL pencils. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

theorem exists_uniform_two_sl_witness (r : ℕ) (hr : 3 ≤ r) :
    ∃ G : Matrix (Fin 2 × Fin r) (Fin r) K[X], DegreeBound G 4 ∧
      Function.Injective G.mulVec ∧
      ∀ (E : Matrix (Fin r) (Fin 2 × Fin r) K[X]) (c : K[X]), DegreeBound E 2 →
        E * G = (-c) • 1 → E = 0 ∧ c = 0 :=
  exists_uniform_two_witness_extension r 2 4 hr (by omega)
    uniformTwoCoreWitness uniformTwoCoreWitness_degree uniformTwoCoreWitness_injective
    uniformTwoCoreWitness_scalar_obstruction

theorem exists_uniform_two_sl_degree_five_witness (r : ℕ) (hr : 3 ≤ r) :
    ∃ (M : Matrix (Fin (3 * r)) (Fin (3 * r)) K[X])
      (P : Matrix (Fin (2 * r)) (Fin (3 * r)) K[X]),
      DegreeBound M 1 ∧ DegreeBound P 1 ∧ slHilbert M P 5 = 0 := by
  obtain ⟨G, hG, hGi, hz⟩ := exists_uniform_two_sl_witness (K := K) r hr
  obtain ⟨M, P, hM, hP, hH⟩ := exists_uniform_sl_relation_upper_witness_of_matrix
    2 2 r (by omega) (by omega) G hG hGi 0 Fin.elim0
    (fun E c hE hrel _ => hz E c hE hrel)
  exact ⟨M, P, hM, hP, Nat.eq_zero_of_le_zero hH⟩

theorem generic_uniform_two_slHilbert_five (r : ℕ) (hr : 3 ≤ r) :
    slHilbert (genericAffineSquare K (Fin (3 * r)) (Fin (2 * r)))
      (genericAffineRows K (Fin (3 * r)) (Fin (2 * r))) 5 = 0 := by
  obtain ⟨M, P, hM, hP, hH⟩ := exists_uniform_two_sl_degree_five_witness (K := K) r hr
  let i₀ : Fin (3 * r) := ⟨0, by omega⟩
  exact Nat.eq_zero_of_le_zero ((generic_slHilbert_le_witness M P hM hP i₀ 5).trans_eq hH)

theorem exists_uniform_two_two_sl_degree_four_witness :
    ∃ (M : Matrix (Fin 6) (Fin 6) K[X]) (P : Matrix (Fin 4) (Fin 6) K[X]),
      DegreeBound M 1 ∧ DegreeBound P 1 ∧ slHilbert M P 4 = 0 := by
  let er : (Fin 2 × Fin 2) ≃ Fin 4 := Fintype.equivOfCardEq (by simp)
  let G := (uniformTwoSmallWitness (K := K)).submatrix er (Equiv.refl _)
  have hG : DegreeBound G 4 := fun i j => uniformTwoSmallWitness_degree (er i) j
  have hGi : Function.Injective G.mulVec := by
    intro u v h
    apply uniformTwoSmallWitness_injective
    funext x
    simpa only [G, Matrix.submatrix_mulVec_equiv, Function.comp_apply,
      Equiv.refl_symm, Equiv.refl_apply, Equiv.apply_symm_apply] using congrFun h (er.symm x)
  obtain ⟨M, P, hM, hP, hH⟩ := exists_uniform_sl_relation_upper_witness_of_matrix
    2 1 2 (by omega) (by omega) G hG hGi 0 Fin.elim0 (by
      intro E c hE hrel _
      let E' : Matrix (Fin 2) (Fin 4) K[X] := E.submatrix (Equiv.refl _) er.symm
      have hE' : DegreeBound E' 1 := fun i j => hE i (er.symm j)
      have hrel' : E' * uniformTwoSmallWitness = (-c) • (1 : Matrix (Fin 2) (Fin 2) K[X]) := by
        have hEE : E'.submatrix (Equiv.refl _) er = E := by funext i j; simp [E']
        change E * uniformTwoSmallWitness.submatrix er (Equiv.refl _) = _ at hrel
        rw [← hEE, Matrix.submatrix_mul_equiv] at hrel
        simpa only [Matrix.submatrix_id_id, Equiv.coe_refl] using hrel
      obtain ⟨hE0, hc0⟩ := uniformTwoSmallWitness_affine_obstruction E' c hE' hrel'
      refine ⟨?_, hc0⟩
      funext i j
      simpa [E'] using congrFun (congrFun hE0 i) (er j))
  exact ⟨M, P, hM, hP, Nat.eq_zero_of_le_zero hH⟩

theorem generic_uniform_two_two_slHilbert_four :
    slHilbert (genericAffineSquare K (Fin 6) (Fin 4))
      (genericAffineRows K (Fin 6) (Fin 4)) 4 = 0 := by
  obtain ⟨M, P, hM, hP, hH⟩ := exists_uniform_two_two_sl_degree_four_witness (K := K)
  exact Nat.eq_zero_of_le_zero ((generic_slHilbert_le_witness M P hM hP 0 4).trans_eq hH)

theorem exists_uniform_two_two_sl_degree_five_witness :
    ∃ (M : Matrix (Fin 6) (Fin 6) K[X]) (P : Matrix (Fin 4) (Fin 6) K[X]),
      DegreeBound M 1 ∧ DegreeBound P 1 ∧ slHilbert M P 5 ≤ 3 := by
  let er : (Fin 2 × Fin 2) ≃ Fin 4 := Fintype.equivOfCardEq (by simp)
  let G := (uniformTwoSmallWitness (K := K)).submatrix er (Equiv.refl _)
  have hG : DegreeBound G 4 := fun i j => uniformTwoSmallWitness_degree (er i) j
  have hGi : Function.Injective G.mulVec := by
    intro u v h
    apply uniformTwoSmallWitness_injective
    funext x
    simpa only [G, Matrix.submatrix_mulVec_equiv, Function.comp_apply,
      Equiv.refl_symm, Equiv.refl_apply, Equiv.apply_symm_apply] using congrFun h (er.symm x)
  apply exists_uniform_sl_relation_upper_witness_of_matrix
    2 2 2 (by omega) (by omega) G hG hGi 3 ![0, 1, 4]
  intro E c hE hrel hc
  let E' : Matrix (Fin 2) (Fin 4) K[X] := E.submatrix (Equiv.refl _) er.symm
  have hE' : DegreeBound E' 2 := fun i j => hE i (er.symm j)
  have hrel' : E' * uniformTwoSmallWitness = (-c) • (1 : Matrix (Fin 2) (Fin 2) K[X]) := by
    have hEE : E'.submatrix (Equiv.refl _) er = E := by funext i j; simp [E']
    change E * uniformTwoSmallWitness.submatrix er (Equiv.refl _) = _ at hrel
    rw [← hEE, Matrix.submatrix_mul_equiv] at hrel
    simpa only [Matrix.submatrix_id_id, Equiv.coe_refl] using hrel
  obtain ⟨hE0, hc0⟩ := uniformTwoSmallWitness_quadratic_obstruction E' c hE' hrel'
    (hc 0) (hc 1) (hc 2)
  refine ⟨?_, hc0⟩
  funext i j
  simpa [E'] using congrFun (congrFun hE0 i) (er j)

theorem generic_uniform_two_two_slHilbert_five :
    slHilbert (genericAffineSquare K (Fin 6) (Fin 4))
      (genericAffineRows K (Fin 6) (Fin 4)) 5 = 3 := by
  apply le_antisymm
  · obtain ⟨M, P, hM, hP, hH⟩ := exists_uniform_two_two_sl_degree_five_witness (K := K)
    exact (generic_slHilbert_le_witness M P hM hP 0 5).trans hH
  · exact generic_uniform_slHilbert_relation_lower (K := K) 2 2 2 (by omega) (by omega)
      (by simp) (by simp) (0 : Fin 6)

end FD56
