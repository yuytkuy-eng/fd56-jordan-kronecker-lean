/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedOneSingleHighWitness
import FD56.Hilbert.MixedOneSingleHighBounds
import FD56.Hilbert.MixedSLGeneralRealization
import FD56.Hilbert.GenericKernelBound
import FD56.Hilbert.GenericOneColumnSL

/-! The single-high quotient-one family has a uniform actual SL degree list. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option maxHeartbeats 800000

def mixedOneSingleHighDegree (u : ℕ) (j : Fin (u+1)) : ℕ :=
  if j.val < u then 1 else 2

abbrev MixedOneSingleHighRows (u : ℕ) := Σ j : Fin (u+1), Fin (mixedOneSingleHighDegree u j)
abbrev MixedOneSingleHighColumns (u : ℕ) := Σ j : Fin (u+1), Fin (mixedOneSingleHighDegree u j+1)

theorem mixedOneSingleHighDegree_add_two (u : ℕ) (j : Fin (u+1)) :
    mixedOneSingleHighDegree u j+2 = mixedOneChainDegree u j := by
  simp only [mixedOneSingleHighDegree,mixedOneChainDegree]
  split_ifs <;> rfl

theorem mixedOneSingleHighRows_card (u : ℕ) :
    Fintype.card (MixedOneSingleHighRows u) = u+2 := by
  simp only [MixedOneSingleHighRows,Fintype.card_sigma,Fintype.card_fin]
  rw [Fin.sum_univ_castSucc]
  simp [mixedOneSingleHighDegree]

theorem mixedOneSingleHighColumns_card (u : ℕ) :
    Fintype.card (MixedOneSingleHighColumns u) = 2*u+3 := by
  simp only [MixedOneSingleHighColumns,Fintype.card_sigma,Fintype.card_fin]
  rw [Fin.sum_univ_castSucc]
  simp [mixedOneSingleHighDegree,Nat.mul_comm]

variable {K : Type*} [Field K]

theorem exists_mixed_one_single_high_sl_block_zero (u : ℕ) (hu : 0 < u) :
    ∃ M : Matrix (MixedOneSingleHighColumns u) (MixedOneSingleHighColumns u) K[X],
      DegreeBound M 1 ∧
        slHilbert M (rectangularBlockPencil (mixedOneSingleHighDegree u)) (3*u+2) = 0 := by
  let e := mixedOneSingleHighDegree u
  let P := rectangularBlockPencil (K := K) e
  let B := rectangularBlockKernelBasis (K := K) e
  let er : MixedOneSingleHighRows u ≃ Fin (u+2) :=
    Fintype.equivOfCardEq (by rw [mixedOneSingleHighRows_card,Fintype.card_fin])
  let G := (mixedOneChain (K := K) u).submatrix er (Equiv.refl _)
  have hGdeg : ∀ x j, (G x j).natDegree ≤ e j+2 := by
    intro x j
    rw [mixedOneSingleHighDegree_add_two]
    exact mixedOneChain_degree u (er x) j
  obtain ⟨M,hM,hPMG⟩ := rectangularBlockPencil_affine_middle_lift e
    (by intro i j; dsimp [e,mixedOneSingleHighDegree]; split_ifs <;> omega) G hGdeg
  obtain ⟨R,hPR⟩ := rectangularBlockPencil_right_inverse (K := K) e
  have hVB : polynomialKernelBasisMatrix P B = blockMonomialKernel e :=
    polynomialKernelBasisMatrix_rectangularBlock e
  have hGM : P * M * polynomialKernelBasisMatrix P B = G := by rw [hVB]; exact hPMG
  have hGi : Function.Injective G.mulVec := by
    intro x y h
    apply mixedOneChain_injective u
    funext i
    have hh := congrFun h (er.symm i)
    simpa only [G,Matrix.submatrix_mulVec_equiv,Function.comp_apply,
      Equiv.refl_symm,Equiv.refl_apply,Equiv.apply_symm_apply] using hh
  have hG : Function.Injective (P*M*polynomialKernelBasisMatrix P B).mulVec := by
    rw [hGM]; exact hGi
  have hV : ∀ x i, (polynomialKernelBasisMatrix P B x i).natDegree ≤ e i := by
    rw [hVB]; exact blockMonomialKernel_column_degree e
  have hVL : Function.Injective (Matrix.mulVec
      (fun x i => (polynomialKernelBasisMatrix P B x i).coeff (e i))) := by
    rw [hVB]; exact blockMonomialKernel_leading_injective e
  have hbot : boundedSLKernel M P (3*u+2) = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro z hz
    obtain ⟨E,c,hEG,hX,hU⟩ := (middle_sl_radical_iff M P B R hPR hG
      (entries z.1) (entries z.2)).mp hz
    have hw := (middle_product_degree_iff (polynomialKernelBasisMatrix P B) P E e (3*u+2)
      hV hVL (rectangularBlockPencil_degree e)
      (rectangularBlockPencil_leading_transpose_injective e)).mp (by
        change DegreeBound (middleSLX P B E) (3*u+2)
        rw [← hX]
        exact entries_degree z.1)
    let E' := E.submatrix (Equiv.refl _) er.symm
    have hE' : ∀ i x, (E' i x).natDegree ≤ 3*u+3-mixedOneChainDegree u i := by
      intro i x
      rcases hw i (er.symm x) with hh | ⟨_,hh⟩
      · change (E i (er.symm x)).natDegree ≤ _
        rw [hh]
        simp
      · change (E i (er.symm x)).natDegree ≤ _
        have heq := mixedOneSingleHighDegree_add_two u i
        change e i+2 = mixedOneChainDegree u i at heq
        have hi : 1 ≤ e i := by dsimp [e,mixedOneSingleHighDegree]; split_ifs <;> omega
        omega
    have hrel' : E' * mixedOneChain u = (-c) •
        (1 : Matrix (Fin (u+1)) (Fin (u+1)) K[X]) := by
      rw [hGM] at hEG
      have hEE : E'.submatrix (Equiv.refl _) er = E := by
        funext i j; simp [E']
      change E * (mixedOneChain u).submatrix er (Equiv.refl _) = _ at hEG
      rw [← hEE,Matrix.submatrix_mul_equiv] at hEG
      simpa only [Matrix.submatrix_id_id,Equiv.coe_refl] using hEG
    let p : Fin (u+1) := ⟨u,by omega⟩
    have hEp : DegreeBound (E'.submatrix (fun _ : Unit => p) id) (3*u-1) := by
      intro i j
      have hh := hE' p j
      simpa [p,mixedOneChainDegree] using hh
    have hGc : DegreeBound (mixedOneChain (K := K) u) 4 := by
      intro i j
      exact (mixedOneChain_degree u i j).trans (by
        simp only [mixedOneChainDegree]; split_ifs <;> omega)
    have hc : c.natDegree ≤ 3*u+3 := by
      have hh := degreeBound_mul hEp hGc () p
      change ((E' * mixedOneChain (K := K) u) p p).natDegree ≤ (3*u-1)+4 at hh
      rw [hrel'] at hh
      simp only [Matrix.smul_apply,Matrix.one_apply,if_true,smul_eq_mul,mul_one,
        Polynomial.natDegree_neg] at hh
      omega
    obtain ⟨hEz,hcz⟩ := mixedOneChain_scalar_obstruction u hu E' c hE' hc hrel'
    have hE : E = 0 := by
      funext i j
      have hh := congrFun (congrFun hEz i) (er j)
      simpa [E'] using hh
    apply Prod.ext
    · apply entries_injective (3*u+2)
      simpa [middleSLX,hE] using hX
    · apply entries_injective (3*u+2)
      simpa [middleSLTranslation,middleSLX,hE,hcz] using hU
  refine ⟨M,hM,?_⟩
  change slHilbert M P (3*u+2) = 0
  simp [slHilbert,hbot]

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem generic_mixed_one_single_high_slHilbert_zero (u : ℕ) (hu : 0 < u)
    (hm : Fintype.card m = u+2) (hn : Fintype.card n = 2*u+3) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) (3*u+2) = 0 := by
  obtain ⟨M,hM,hH⟩ := exists_mixed_one_single_high_sl_block_zero (K := K) u hu
  let en : n ≃ MixedOneSingleHighColumns u := Fintype.equivOfCardEq (by
    rw [mixedOneSingleHighColumns_card,hn])
  let em : m ≃ MixedOneSingleHighRows u := Fintype.equivOfCardEq (by
    rw [mixedOneSingleHighRows_card,hm])
  have hh := generic_slHilbert_le_witness (M.submatrix en en)
    ((rectangularBlockPencil (mixedOneSingleHighDegree u)).submatrix em en)
    (fun i j => hM (en i) (en j))
    (fun i j => rectangularBlockPencil_degree _ (em i) (en j)) i₀ (3*u+2)
  rw [slHilbert_reindex,hH] at hh
  exact Nat.eq_zero_of_le_zero hh

theorem generic_mixed_one_single_high_sl_minimal_degrees (u : ℕ) (hu : 0 < u)
    (hm : Fintype.card m = u+2) (hn : Fintype.card n = 2*u+3) (i₀ : n) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) i₀)
      (List.replicate (u+2) (3*u+3)) := by
  apply hasMinimalKernelDegrees_replicate_of_bounds _ (3*u+3) (u+2) 1 (by omega)
  · rw [← slHilbert_eq_matrix_kernel]
    simpa only [show 3*u+3-1 = 3*u+2 by omega] using
      generic_mixed_one_single_high_slHilbert_zero (K := K) u hu hm hn i₀
  · rw [← slHilbert_eq_matrix_kernel]
    exact generic_mixed_one_single_high_slHilbert_lower u hu hm hn i₀
  · intro d
    rw [← slHilbert_eq_matrix_kernel]
    exact generic_mixed_one_single_high_slHilbert_upper u hu hm hn i₀ d

theorem generic_near_double_sl_minimal_degrees
    (hm : 2 ≤ Fintype.card m) (hn : Fintype.card n+1 = 2*Fintype.card m) (i₀ : n) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) i₀)
      (List.replicate (Fintype.card m) (3*Fintype.card m-3)) := by
  by_cases hm2 : Fintype.card m = 2
  · have h := generic_one_more_column_sl_minimal_degrees (K := K) (n := n) (m := m)
      i₀ (by omega) (by omega)
    simpa only [hm2,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub] using h
  · have hc : Fintype.card m-2+2 = Fintype.card m := by omega
    have hd : 3*(Fintype.card m-2)+3 = 3*Fintype.card m-3 := by omega
    have h := generic_mixed_one_single_high_sl_minimal_degrees (K := K) (n := n) (m := m)
      (Fintype.card m-2) (by omega) (by omega) (by omega) i₀
    simpa only [hc,hd] using h

end FD56
