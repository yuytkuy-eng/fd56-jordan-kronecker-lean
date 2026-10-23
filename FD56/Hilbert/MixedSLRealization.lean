/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedScalarWitness
import FD56.Hilbert.MixedKernelBasis
import FD56.Hilbert.MixedSLScalarUpper
import FD56.Hilbert.MiddleGLShift
import FD56.Hilbert.MiddleWitness
import FD56.Hilbert.SLReindex
import FD56.Hilbert.MiddleBetaWitness
import FD56.Hilbert.FamilySLRealization

/-! Actual affine realizations of simultaneous mixed auxiliary witnesses. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

abbrev MixedSLRows (a u v : ℕ) := Σ i, Fin (mixedKernelDegree a u v i)
abbrev MixedSLColumns (a u v : ℕ) := Σ i, Fin (mixedKernelDegree a u v i + 1)

def mixedSLRowEquiv (a u v : ℕ) :
    MixedSLRows a u v ≃ MixedScalarRows a (Fin u) (Fin v) where
  toFun x := match x with
    | ⟨Sum.inl i, k⟩ => Sum.inl (k,i)
    | ⟨Sum.inr i, k⟩ => Sum.inr (k,i)
  invFun x := match x with
    | Sum.inl (k,i) => ⟨Sum.inl i,k⟩
    | Sum.inr (k,i) => ⟨Sum.inr i,k⟩
  left_inv x := by rcases x with ⟨i,k⟩; cases i <;> rfl
  right_inv x := by cases x <;> rfl

theorem mixedSLRows_card (a u v : ℕ) :
    Fintype.card (MixedSLRows a u v) = a * (u+v) + v := by
  simp only [MixedSLRows, Fintype.card_sigma, Fintype.card_fin, Fintype.sum_sum_type,
    mixedKernelDegree_inl, mixedKernelDegree_inr, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

theorem mixedSLColumns_card (a u v : ℕ) :
    Fintype.card (MixedSLColumns a u v) = a * (u+v) + v + (u+v) := by
  simp only [MixedSLColumns, Fintype.card_sigma, Fintype.card_fin, Fintype.sum_sum_type,
    mixedKernelDegree_inl, mixedKernelDegree_inr, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

variable {K : Type*} [Field K]

theorem exists_mixed_sl_block_critical_upper_witness_of_matrix (a u v : ℕ)
    (hv : 0 < v)
    (W : Matrix (MixedScalarRows a (Fin u) (Fin v)) (Fin u ⊕ Fin v) K[X])
    (hW : ∀ x j, (W x j).natDegree ≤ mixedKernelDegree a u v j + 2)
    (hWi : Function.Injective W.mulVec)
    (hW0 : Module.finrank K (polynomialKernelAtDegree W.transpose 0) = 0)
    (hW1 : Module.finrank K (polynomialKernelAtDegree W.transpose 1) =
      a * (u+v) + v - 4 * (u+v))
    (t : ℕ) (f : Fin t → ℕ)
    (hzero : ∀ (E : Matrix (Fin v) (MixedScalarRows a (Fin u) (Fin v)) K[X]) (c : K[X]),
      DegreeBound E 0 → c.natDegree ≤ a+3 →
      E * W = (-c) • (fun i j => if Sum.inr i = j then 1 else 0 :
        Matrix (Fin v) (Fin u ⊕ Fin v) K[X]) →
      (∀ j, c.coeff (f j) = 0) → c = 0) :
    ∃ M : Matrix (MixedSLColumns a u v) (MixedSLColumns a u v) K[X],
      DegreeBound M 1 ∧
        slHilbert M (rectangularBlockPencil (mixedKernelDegree a u v)) (a+2) ≤
          u * (a * (u+v) + v - 4 * (u+v)) + t := by
  let p : Fin v := ⟨0,hv⟩
  let e := mixedKernelDegree a u v
  let P : Matrix (MixedSLRows a u v) (MixedSLColumns a u v) K[X] := rectangularBlockPencil e
  let G : Matrix (MixedSLRows a u v) (Fin u ⊕ Fin v) K[X] :=
    W.submatrix (mixedSLRowEquiv a u v) (Equiv.refl _)
  let B := rectangularBlockKernelBasis (K := K) e
  have hGdeg : ∀ x j, (G x j).natDegree ≤ e j + 2 :=
    fun x j => hW (mixedSLRowEquiv a u v x) j
  obtain ⟨M,hM,hPMG⟩ := rectangularBlockPencil_affine_middle_lift e
    (by intro i j; cases i <;> cases j <;>
        simp only [e, mixedKernelDegree_inl, mixedKernelDegree_inr] <;> omega) G hGdeg
  obtain ⟨R,hPR⟩ := rectangularBlockPencil_right_inverse (K := K) e
  have hVB : polynomialKernelBasisMatrix P B = blockMonomialKernel e :=
    polynomialKernelBasisMatrix_rectangularBlock e
  have hGM : P * M * polynomialKernelBasisMatrix P B = G := by rw [hVB]; exact hPMG
  have hGi : Function.Injective G.mulVec := by
    intro x y h
    apply hWi
    funext i
    have hh := congrFun h ((mixedSLRowEquiv a u v).symm i)
    simpa only [G, Matrix.submatrix_mulVec_equiv, Function.comp_apply,
      Equiv.refl_symm, Equiv.refl_apply, Equiv.apply_symm_apply] using hh
  have hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec := by
    rw [hGM]; exact hGi
  have hV : ∀ x i, (polynomialKernelBasisMatrix P B x i).natDegree ≤ e i := by
    rw [hVB]; exact blockMonomialKernel_column_degree e
  have hVL : Function.Injective (Matrix.mulVec
      (fun x i => (polynomialKernelBasisMatrix P B x i).coeff (e i))) := by
    rw [hVB]; exact blockMonomialKernel_leading_injective e
  have hGH (d : ℕ) : Module.finrank K (polynomialKernelAtDegree G.transpose d) =
      Module.finrank K (polynomialKernelAtDegree W.transpose d) :=
    reindex_kernel_hilbert W.transpose (Equiv.refl _) (mixedSLRowEquiv a u v) d
  have hGL : Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) (a+2)) =
      u * (a * (u+v) + v - 4 * (u+v)) := by
    rw [middle_gl_kernel_hilbert_shifted M P B R hPR hG e hM
      (rectangularBlockPencil_degree e) hV hVL
      (rectangularBlockPencil_leading_transpose_injective e) (a+2)
      (by intro i; cases i <;> simp [e]), hGM]
    simp only [Fintype.sum_sum_type, e, mixedKernelDegree_inl, mixedKernelDegree_inr,
      hGH, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have h1 : a+2-(a+1) = 1 := by omega
    have h0 : a+2-(a+1+1) = 0 := by omega
    rw [h1,h0,hW0,hW1,mul_zero,add_zero]
  refine ⟨M,hM,?_⟩
  rw [← hGL]
  apply mixed_middle_slHilbert_critical_upper M P a u v B R hPR hG hM
    (rectangularBlockPencil_degree e) hV hVL
    (rectangularBlockPencil_leading_transpose_injective e) ⟨Sum.inr p,0⟩ t f
  intro E c hE hrel hc
  let E' := E.submatrix (Equiv.refl _) (mixedSLRowEquiv a u v).symm
  have hE' : DegreeBound E' 0 := fun i j => hE i ((mixedSLRowEquiv a u v).symm j)
  have hrel' : E' * W = (-c) • (fun i j => if Sum.inr i = j then 1 else 0 :
      Matrix (Fin v) (Fin u ⊕ Fin v) K[X]) := by
    rw [hGM] at hrel
    have hEE : E'.submatrix (Equiv.refl _) (mixedSLRowEquiv a u v) = E := by
      funext i j; simp [E']
    change E * W.submatrix (mixedSLRowEquiv a u v) (Equiv.refl _) = _ at hrel
    rw [← hEE, Matrix.submatrix_mul_equiv] at hrel
    simpa only [Matrix.submatrix_id_id, Equiv.coe_refl] using hrel
  have hWb : DegreeBound W (a+3) := by
    intro x j
    have hj := hW x j
    cases j <;> simp only [mixedKernelDegree_inl, mixedKernelDegree_inr] at hj <;> omega
  have hcb : c.natDegree ≤ a+3 := by
    have hh := degreeBound_mul hE' hWb p (Sum.inr p)
    rw [hrel'] at hh
    simpa using hh
  exact hzero E' c hE' hcb hrel' hc

theorem exists_mixed_sl_critical_upper_witness_of_matrix
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (a u v : ℕ) (hv : 0 < v)
    (hm : Fintype.card m = a * (u+v) + v)
    (hn : Fintype.card n = Fintype.card m + (u+v))
    (W : Matrix (MixedScalarRows a (Fin u) (Fin v)) (Fin u ⊕ Fin v) K[X])
    (hW : ∀ x j, (W x j).natDegree ≤ mixedKernelDegree a u v j + 2)
    (hWi : Function.Injective W.mulVec)
    (hW0 : Module.finrank K (polynomialKernelAtDegree W.transpose 0) = 0)
    (hW1 : Module.finrank K (polynomialKernelAtDegree W.transpose 1) =
      a * (u+v) + v - 4 * (u+v))
    (t : ℕ) (f : Fin t → ℕ)
    (hzero : ∀ (E : Matrix (Fin v) (MixedScalarRows a (Fin u) (Fin v)) K[X]) (c : K[X]),
      DegreeBound E 0 → c.natDegree ≤ a+3 →
      E * W = (-c) • (fun i j => if Sum.inr i = j then 1 else 0 :
        Matrix (Fin v) (Fin u ⊕ Fin v) K[X]) →
      (∀ j, c.coeff (f j) = 0) → c = 0) :
    ∃ (M : Matrix n n K[X]) (P : Matrix m n K[X]),
      DegreeBound M 1 ∧ DegreeBound P 1 ∧
        slHilbert M P (a+2) ≤ u * (Fintype.card m - 4 * (u+v)) + t := by
  obtain ⟨M,hM,hH⟩ := exists_mixed_sl_block_critical_upper_witness_of_matrix
    a u v hv W hW hWi hW0 hW1 t f hzero
  let en : n ≃ MixedSLColumns a u v := Fintype.equivOfCardEq (by
    rw [mixedSLColumns_card, hn, hm])
  let em : m ≃ MixedSLRows a u v := Fintype.equivOfCardEq (by
    rw [mixedSLRows_card, hm])
  refine ⟨M.submatrix en en,
    (rectangularBlockPencil (mixedKernelDegree a u v)).submatrix em en,
    (fun i j => hM (en i) (en j)),
    (fun i j => rectangularBlockPencil_degree _ (em i) (en j)), ?_⟩
  rw [slHilbert_reindex,hm]
  exact hH

end FD56
