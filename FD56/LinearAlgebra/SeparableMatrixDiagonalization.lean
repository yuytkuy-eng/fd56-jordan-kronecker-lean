/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.GenericMatrixSeparable
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Fintype.EquivFin

/-! Constant diagonalization from a split separable characteristic polynomial. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem matrix_eigenvector_of_charpoly_root (M : Matrix n n K) (a : K)
    (ha : M.charpoly.IsRoot a) :
    ∃ v : n → K, Module.End.HasEigenvector (Matrix.toLin' M) a v := by
  have hd : (Matrix.diagonal (fun _ : n => a) - M).det = 0 := by
    have he : M.charmatrix.map (Polynomial.evalRingHom a) = Matrix.diagonal (fun _ => a)-M := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [Matrix.charmatrix_apply_ne,hij]
    have hh : M.charpoly.eval a = (M.charmatrix.map (Polynomial.evalRingHom a)).det :=
      (Polynomial.evalRingHom a).map_det M.charmatrix
    change M.charpoly.eval a = _ at hh
    rw [he] at hh
    exact hh.symm.trans ha
  obtain ⟨v,hv,hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  refine ⟨v,?_,hv⟩
  apply Module.End.mem_eigenspace_iff.mpr
  change M.mulVec v = a • v
  rw [Matrix.sub_mulVec] at hMv
  have hh := (sub_eq_zero.mp hMv).symm
  funext i
  simpa only [Matrix.mulVec_diagonal,Pi.smul_apply,smul_eq_mul] using congrFun hh i

theorem exists_diagonalization_of_separable_charpoly (M : Matrix n n K)
    (hsep : M.charpoly.Separable) (hsplit : M.charpoly.Splits (RingHom.id K)) :
    ∃ (S T : Matrix n n K) (ev : n → K), Function.Injective ev ∧
      S*T = 1 ∧ T*S = 1 ∧ M*S = S*(Matrix.diagonal ev) := by
  classical
  let s := M.charpoly.roots.toFinset
  have hc : Fintype.card s = Fintype.card n := by
    rw [Fintype.card_coe,Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
      Polynomial.splits_iff_card_roots.mp hsplit,Matrix.charpoly_natDegree_eq_dim]
  let e : n ≃ s := Fintype.equivOfCardEq hc.symm
  let ev : n → K := fun i => (e i).val
  have hev : Function.Injective ev := Subtype.val_injective.comp e.injective
  have hr : ∀ i, M.charpoly.IsRoot (ev i) := by
    intro i
    apply (Polynomial.mem_roots (Matrix.charpoly_monic M).ne_zero).mp
    exact Multiset.mem_toFinset.mp (e i).property
  choose v hv using fun i => matrix_eigenvector_of_charpoly_root M (ev i) (hr i)
  have hli := Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) ev hev v hv
  let S : Matrix n n K := fun i j => v j i
  have hS : IsUnit S := Matrix.mulVec_injective_iff_isUnit.mp
    (Matrix.mulVec_injective_iff.mpr hli)
  obtain ⟨u,hu⟩ := hS
  refine ⟨S,↑(u⁻¹),ev,hev,?_,?_,?_⟩
  · rw [← hu]
    exact u.mul_inv
  · rw [← hu]
    exact u.inv_mul
  · ext i j
    have hj := congrFun (hv j).apply_eq_smul i
    simpa only [Matrix.toLin'_apply,Pi.smul_apply,smul_eq_mul,Matrix.mul_diagonal,mul_comm] using hj

end FD56
