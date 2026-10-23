/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformGeneralSLRealization
import FD56.Hilbert.UniformSLRelationDegree
import FD56.Hilbert.UniformThreeWitness
import FD56.Hilbert.UniformThreeSmallWitness
import FD56.Hilbert.GenericKernelBound

/-! Realizing a finite scalar-coefficient bound by an actual affine SL pencil. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

theorem exists_uniform_sl_block_relation_upper_witness_of_matrix (a k r : ℕ)
    (_ha : 0 < a) (hr : 0 < r)
    (W : Matrix (Fin a × Fin r) (Fin r) K[X])
    (hW : DegreeBound W (a + 2)) (hWi : Function.Injective W.mulVec)
    (t : ℕ) (f : Fin t → ℕ)
    (hzero : ∀ (E : Matrix (Fin r) (Fin a × Fin r) K[X]) (c : K[X]),
      DegreeBound E k → E * W = (-c) • 1 →
        (∀ j, c.coeff (f j) = 0) → E = 0 ∧ c = 0) :
    ∃ M : Matrix (UniformGeneralSLColumns a r) (UniformGeneralSLColumns a r) K[X],
      DegreeBound M 1 ∧
        slHilbert M (rectangularBlockPencil (fun _ : Fin r => a)) (a + k + 1) ≤ t := by
  let p : Fin r := ⟨0, hr⟩
  let e : Fin r → ℕ := fun _ => a
  let P : Matrix (UniformGeneralSLRows a r) (UniformGeneralSLColumns a r) K[X] := rectangularBlockPencil e
  let G : Matrix (UniformGeneralSLRows a r) (Fin r) K[X] :=
    W.submatrix (uniformGeneralSLRowEquiv a r) (Equiv.refl _)
  let B := rectangularBlockKernelBasis (K := K) e
  have hGdeg : ∀ x j, (G x j).natDegree ≤ e j + 2 := by
    intro x j
    exact hW (uniformGeneralSLRowEquiv a r x) j
  obtain ⟨M, hM, hPMG⟩ := rectangularBlockPencil_affine_middle_lift e
    (fun _ _ => by dsimp [e]; omega) G hGdeg
  obtain ⟨R, hPR⟩ := rectangularBlockPencil_right_inverse (K := K) e
  have hVB : polynomialKernelBasisMatrix P B = blockMonomialKernel e :=
    polynomialKernelBasisMatrix_rectangularBlock e
  have hGM : P * M * polynomialKernelBasisMatrix P B = G := by rw [hVB]; exact hPMG
  have hGi : Function.Injective G.mulVec := by
    intro u v h
    apply hWi
    funext x
    have hh := congrFun h ((uniformGeneralSLRowEquiv a r).symm x)
    simpa only [G, Matrix.submatrix_mulVec_equiv, Function.comp_apply,
      Equiv.refl_symm, Equiv.refl_apply, Equiv.apply_symm_apply] using hh
  have hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec := by
    rw [hGM]
    exact hGi
  have hV : ∀ x i, (polynomialKernelBasisMatrix P B x i).natDegree ≤ e i := by
    rw [hVB]
    exact blockMonomialKernel_column_degree e
  have hVL : Function.Injective (Matrix.mulVec
      (fun x i => (polynomialKernelBasisMatrix P B x i).coeff (e i))) := by
    rw [hVB]
    exact blockMonomialKernel_leading_injective e
  letI : Nonempty (UniformGeneralSLColumns a r) := ⟨⟨p, 0⟩⟩
  refine ⟨M, hM, ?_⟩
  apply uniform_middle_slHilbert_relation_upper M P B R hPR a k hM
    (rectangularBlockPencil_degree e) hV
    (rectangularBlockPencil_leading_transpose_injective e) p hG hVL t f
  intro E c hE hrel hc
  let E' := E.submatrix (Equiv.refl _) (uniformGeneralSLRowEquiv a r).symm
  have hE' : DegreeBound E' k := fun i j => hE i ((uniformGeneralSLRowEquiv a r).symm j)
  have hrel' : E' * W = (-c) • (1 : Matrix (Fin r) (Fin r) K[X]) := by
    rw [hGM] at hrel
    change E * (W).submatrix (uniformGeneralSLRowEquiv a r) (Equiv.refl _) = _ at hrel
    have hEE : E'.submatrix (Equiv.refl _) (uniformGeneralSLRowEquiv a r) = E := by
      funext i j
      simp [E']
    rw [← hEE, Matrix.submatrix_mul_equiv] at hrel
    simpa only [Matrix.submatrix_id_id, Equiv.coe_refl] using hrel
  obtain ⟨hzE, hzc⟩ := hzero E' c hE' hrel' hc
  refine ⟨?_, hzc⟩
  funext i j
  have hh := congrFun (congrFun hzE i) (uniformGeneralSLRowEquiv a r j)
  simpa [E'] using hh

theorem exists_uniform_sl_relation_upper_witness_of_matrix (a k r : ℕ)
    (ha : 0 < a) (hr : 0 < r)
    (W : Matrix (Fin a × Fin r) (Fin r) K[X])
    (hW : DegreeBound W (a + 2)) (hWi : Function.Injective W.mulVec)
    (t : ℕ) (f : Fin t → ℕ)
    (hzero : ∀ (E : Matrix (Fin r) (Fin a × Fin r) K[X]) (c : K[X]),
      DegreeBound E k → E * W = (-c) • 1 →
        (∀ j, c.coeff (f j) = 0) → E = 0 ∧ c = 0) :
    ∃ (M : Matrix (Fin ((a + 1) * r)) (Fin ((a + 1) * r)) K[X])
      (P : Matrix (Fin (a * r)) (Fin ((a + 1) * r)) K[X]),
      DegreeBound M 1 ∧ DegreeBound P 1 ∧ slHilbert M P (a + k + 1) ≤ t := by
  obtain ⟨M, hM, hH⟩ :=
    exists_uniform_sl_block_relation_upper_witness_of_matrix a k r ha hr W hW hWi t f hzero
  let en : Fin ((a + 1) * r) ≃ UniformGeneralSLColumns a r :=
    Fintype.equivOfCardEq (by simp [UniformGeneralSLColumns, Nat.mul_comm])
  let em : Fin (a * r) ≃ UniformGeneralSLRows a r :=
    Fintype.equivOfCardEq (by simp [UniformGeneralSLRows, Nat.mul_comm])
  refine ⟨M.submatrix en en,
    (rectangularBlockPencil (fun _ : Fin r => a)).submatrix em en,
    (fun i j => hM (en i) (en j)),
    (fun i j => rectangularBlockPencil_degree _ (em i) (en j)), ?_⟩
  rw [slHilbert_reindex]
  exact hH

theorem exists_uniform_three_sl_degree_five_witness (r : ℕ) (hr : 3 ≤ r) :
    ∃ (M : Matrix (Fin (4 * r)) (Fin (4 * r)) K[X])
      (P : Matrix (Fin (3 * r)) (Fin (4 * r)) K[X]),
      DegreeBound M 1 ∧ DegreeBound P 1 ∧ slHilbert M P 5 = 0 := by
  obtain ⟨G, hG, hGi, hz⟩ := exists_uniform_three_sl_witness (K := K) r hr
  obtain ⟨M, P, hM, hP, hH⟩ := exists_uniform_sl_relation_upper_witness_of_matrix
    3 1 r (by omega) (by omega) G hG hGi 0 Fin.elim0
    (fun E c hE hrel _ => hz E c hE hrel)
  exact ⟨M, P, hM, hP, Nat.eq_zero_of_le_zero hH⟩

theorem generic_uniform_three_slHilbert_five (r : ℕ) (hr : 3 ≤ r) :
    slHilbert (genericAffineSquare K (Fin (4 * r)) (Fin (3 * r)))
      (genericAffineRows K (Fin (4 * r)) (Fin (3 * r))) 5 = 0 := by
  obtain ⟨M, P, hM, hP, hH⟩ := exists_uniform_three_sl_degree_five_witness (K := K) r hr
  let i₀ : Fin (4 * r) := ⟨0, by omega⟩
  exact Nat.eq_zero_of_le_zero ((generic_slHilbert_le_witness M P hM hP i₀ 5).trans_eq hH)

theorem exists_uniform_three_two_sl_degree_five_witness :
    ∃ (M : Matrix (Fin 8) (Fin 8) K[X]) (P : Matrix (Fin 6) (Fin 8) K[X]),
      DegreeBound M 1 ∧ DegreeBound P 1 ∧ slHilbert M P 5 ≤ 3 := by
  obtain ⟨G, hG, hGi, hz⟩ := exists_uniform_three_small_sl_witness (K := K)
  exact exists_uniform_sl_relation_upper_witness_of_matrix
    3 1 2 (by omega) (by omega) G hG hGi 3 (fun j => 2 * j.val) hz

theorem generic_uniform_three_two_slHilbert_five :
    slHilbert (genericAffineSquare K (Fin 8) (Fin 6))
      (genericAffineRows K (Fin 8) (Fin 6)) 5 = 3 := by
  apply le_antisymm
  · obtain ⟨M, P, hM, hP, hH⟩ := exists_uniform_three_two_sl_degree_five_witness (K := K)
    exact (generic_slHilbert_le_witness M P hM hP 0 5).trans hH
  · exact generic_uniform_three_slHilbert_five_lower (K := K) 2 (by omega)
      (by simp) (by simp) (0 : Fin 8)

end FD56
