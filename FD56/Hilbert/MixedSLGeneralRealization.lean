/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedSLRealization

/-! Mixed affine realizations with arbitrary bounded relation degrees. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]

theorem exists_mixed_sl_block_upper_witness_of_matrix (a u v d : ℕ)
    (hv : 0 < v) (hd : a+2 ≤ d)
    (W : Matrix (MixedScalarRows a (Fin u) (Fin v)) (Fin u ⊕ Fin v) K[X])
    (hW : ∀ x j, (W x j).natDegree ≤ mixedKernelDegree a u v j+2)
    (hWi : Function.Injective W.mulVec) (g : ℕ)
    (hH : (∑ i, Module.finrank K (polynomialKernelAtDegree W.transpose
      (d-(mixedKernelDegree a u v i+1)))) = g)
    (t : ℕ) (f : Fin t → ℕ)
    (hzero : ∀ (E : Matrix (Fin u ⊕ Fin v) (MixedScalarRows a (Fin u) (Fin v)) K[X])
      (c : K[X]),
      (∀ i j, E i j = 0 ∨ (mixedKernelDegree a u v i+1 ≤ d ∧
        (E i j).natDegree ≤ d-(mixedKernelDegree a u v i+1))) →
      c.natDegree ≤ d+1 → E * W = (-c) • 1 →
      (∀ j, c.coeff (f j) = 0) → c = 0) :
    ∃ M : Matrix (MixedSLColumns a u v) (MixedSLColumns a u v) K[X],
      DegreeBound M 1 ∧ slHilbert M (rectangularBlockPencil (mixedKernelDegree a u v)) d ≤
        g+t := by
  let p : Fin v := ⟨0,hv⟩
  let e := mixedKernelDegree a u v
  let P : Matrix (MixedSLRows a u v) (MixedSLColumns a u v) K[X] := rectangularBlockPencil e
  let G : Matrix (MixedSLRows a u v) (Fin u ⊕ Fin v) K[X] :=
    W.submatrix (mixedSLRowEquiv a u v) (Equiv.refl _)
  let B := rectangularBlockKernelBasis (K := K) e
  have hGdeg : ∀ x j, (G x j).natDegree ≤ e j+2 :=
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
  have hGH (k : ℕ) : Module.finrank K (polynomialKernelAtDegree G.transpose k) =
      Module.finrank K (polynomialKernelAtDegree W.transpose k) :=
    reindex_kernel_hilbert W.transpose (Equiv.refl _) (mixedSLRowEquiv a u v) k
  have hGL : Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d) = g := by
    rw [middle_gl_kernel_hilbert_shifted M P B R hPR hG e hM
      (rectangularBlockPencil_degree e) hV hVL
      (rectangularBlockPencil_leading_transpose_injective e) d
      (by intro i; cases i <;> simp only [e,mixedKernelDegree_inl,mixedKernelDegree_inr] <;>
        omega), hGM]
    simpa only [hGH] using hH
  refine ⟨M,hM,?_⟩
  rw [← hGL]
  apply middle_slHilbert_le_gl_add_selector M P B R hPR hG e hM
    (rectangularBlockPencil_degree e) hV hVL
    (rectangularBlockPencil_leading_transpose_injective e) ⟨Sum.inr p,0⟩ d t f
  intro E c hE hrel hc
  let E' := E.submatrix (Equiv.refl _) (mixedSLRowEquiv a u v).symm
  have hE' : ∀ i j, E' i j = 0 ∨ (e i+1 ≤ d ∧ (E' i j).natDegree ≤ d-(e i+1)) :=
    fun i j => hE i ((mixedSLRowEquiv a u v).symm j)
  have hrel' : E' * W = (-c) • (1 : Matrix (Fin u ⊕ Fin v) (Fin u ⊕ Fin v) K[X]) := by
    rw [hGM] at hrel
    have hEE : E'.submatrix (Equiv.refl _) (mixedSLRowEquiv a u v) = E := by
      funext i j; simp [E']
    change E * W.submatrix (mixedSLRowEquiv a u v) (Equiv.refl _) = _ at hrel
    rw [← hEE, Matrix.submatrix_mul_equiv] at hrel
    simpa only [Matrix.submatrix_id_id, Equiv.coe_refl] using hrel
  let Eh := E'.submatrix Sum.inr id
  have hEh : DegreeBound Eh (d-(a+2)) := by
    intro i j
    rcases hE' (Sum.inr i) j with hh | ⟨_,hh⟩
    · change (E' (Sum.inr i) j).natDegree ≤ _
      rw [hh]
      simp
    · simpa only [e,mixedKernelDegree_inr,Nat.add_assoc,Nat.reduceAdd] using hh
  have hrelh : Eh * W = (-c) • (fun i j => if Sum.inr i = j then 1 else 0 :
      Matrix (Fin v) (Fin u ⊕ Fin v) K[X]) := by
    funext i j
    have hh := congrArg (fun A : Matrix (Fin u ⊕ Fin v) (Fin u ⊕ Fin v) K[X] =>
      A (Sum.inr i) j) hrel'
    simpa [Eh, Matrix.mul_apply, Matrix.one_apply] using hh
  have hWb : DegreeBound W (a+3) := by
    intro x j
    have hj := hW x j
    cases j <;> simp only [mixedKernelDegree_inl, mixedKernelDegree_inr] at hj <;> omega
  have hcb : c.natDegree ≤ d+1 := by
    have hh := degreeBound_mul hEh hWb p (Sum.inr p)
    rw [hrelh] at hh
    simp only [Matrix.smul_apply, Pi.smul_apply, if_true, smul_eq_mul, mul_one,
      Polynomial.natDegree_neg] at hh
    omega
  exact hzero E' c hE' hcb hrel' hc

theorem exists_mixed_sl_upper_witness_of_matrix
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (a u v d : ℕ) (hv : 0 < v) (hd : a+2 ≤ d)
    (hm : Fintype.card m = a*(u+v)+v)
    (hn : Fintype.card n = Fintype.card m+(u+v))
    (W : Matrix (MixedScalarRows a (Fin u) (Fin v)) (Fin u ⊕ Fin v) K[X])
    (hW : ∀ x j, (W x j).natDegree ≤ mixedKernelDegree a u v j+2)
    (hWi : Function.Injective W.mulVec) (g : ℕ)
    (hH : (∑ i, Module.finrank K (polynomialKernelAtDegree W.transpose
      (d-(mixedKernelDegree a u v i+1)))) = g)
    (t : ℕ) (f : Fin t → ℕ)
    (hzero : ∀ (E : Matrix (Fin u ⊕ Fin v) (MixedScalarRows a (Fin u) (Fin v)) K[X])
      (c : K[X]),
      (∀ i j, E i j = 0 ∨ (mixedKernelDegree a u v i+1 ≤ d ∧
        (E i j).natDegree ≤ d-(mixedKernelDegree a u v i+1))) →
      c.natDegree ≤ d+1 → E * W = (-c) • 1 →
      (∀ j, c.coeff (f j) = 0) → c = 0) :
    ∃ (M : Matrix n n K[X]) (P : Matrix m n K[X]),
      DegreeBound M 1 ∧ DegreeBound P 1 ∧ slHilbert M P d ≤ g+t := by
  obtain ⟨M,hM,hbound⟩ := exists_mixed_sl_block_upper_witness_of_matrix
    a u v d hv hd W hW hWi g hH t f hzero
  let en : n ≃ MixedSLColumns a u v := Fintype.equivOfCardEq (by
    rw [mixedSLColumns_card,hn,hm])
  let em : m ≃ MixedSLRows a u v := Fintype.equivOfCardEq (by rw [mixedSLRows_card,hm])
  refine ⟨M.submatrix en en, (rectangularBlockPencil (mixedKernelDegree a u v)).submatrix em en,
    (fun i j => hM (en i) (en j)),
    (fun i j => rectangularBlockPencil_degree _ (em i) (en j)),?_⟩
  rw [slHilbert_reindex]
  exact hbound

end FD56
