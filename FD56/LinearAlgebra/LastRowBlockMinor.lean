/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.NonzeroMaximalMinor
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Finset.Fin

/-! A corank-one row stack has a nonsingular minor deleting a last-block row. -/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators

theorem exists_last_block_complement_minor {F n m : Type*} [Field F]
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (q : ℕ) (A : Matrix (Fin (q + 1) × m) n F)
    (hcard : Fintype.card n + 1 = (q + 1) * Fintype.card m)
    (hA : Function.Injective A.mulVec)
    (hprefix : Function.Injective
      (A.submatrix (fun ij : Fin q × m => (ij.1.castSucc, ij.2)) id).transpose.mulVec) :
    ∃ (j : m) (e : n ≃ {ij : Fin (q + 1) × m // ij ≠ (Fin.last q, j)}),
      (A.submatrix (fun i => (e i).val) id).det ≠ 0 := by
  classical
  have hker : LinearMap.ker (Matrix.toLin' A.transpose) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by
      simp only [Module.finrank_pi, Fintype.card_prod, Fintype.card_fin]
      omega)
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).mp hker
  change A.transpose *ᵥ y = 0 at hy
  have hlast : ∃ j, y (Fin.last q, j) ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hp : (A.submatrix (fun ij : Fin q × m => (ij.1.castSucc, ij.2)) id).transpose *ᵥ
        (fun ij => y (ij.1.castSucc, ij.2)) = 0 := by
      funext i
      have hi := congrFun hy i
      simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.submatrix_apply,
        id_eq, Fintype.sum_prod_type, Fin.sum_univ_castSucc, hn, mul_zero,
        Finset.sum_const_zero, add_zero, Pi.zero_apply] using hi
    have hp0 := hprefix (hp.trans (Matrix.mulVec_zero _).symm)
    apply hy0
    funext ij
    rcases ij with ⟨i, j⟩
    refine Fin.lastCases (hn j) (fun k => ?_) i
    exact congrFun hp0 (k, j)
  obtain ⟨j, hj⟩ := hlast
  have hc : Fintype.card {ij : Fin (q + 1) × m // ij ≠ (Fin.last q, j)} =
      Fintype.card n := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_unique]
    omega
  let e : n ≃ {ij : Fin (q + 1) × m // ij ≠ (Fin.last q, j)} :=
    Fintype.equivOfCardEq hc.symm
  refine ⟨j, e, ?_⟩
  have hinj : Function.Injective (A.submatrix (fun i => (e i).val) id).mulVec := by
    intro v w hvw
    let x := v - w
    have hx : (A.submatrix (fun i => (e i).val) id) *ᵥ x = 0 := by
      rw [Matrix.mulVec_sub, hvw, sub_self]
    have hr : ∀ ij ≠ (Fin.last q, j), (A *ᵥ x) ij = 0 := by
      intro ij hij
      obtain ⟨i, hi⟩ := e.surjective ⟨ij, hij⟩
      have hh := congrFun hx i
      change (A *ᵥ x) (e i).val = 0 at hh
      simpa only [hi] using hh
    have hd : y ⬝ᵥ (A *ᵥ x) = 0 := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hy, zero_dotProduct]
    have hl : y (Fin.last q, j) * (A *ᵥ x) (Fin.last q, j) = 0 := by
      rw [dotProduct, Finset.sum_eq_single (Fin.last q, j)] at hd
      · exact hd
      · intro ij _ hij
        rw [hr ij hij, mul_zero]
      · simp
    have hAx : A *ᵥ x = 0 := by
      funext ij
      by_cases hij : ij = (Fin.last q, j)
      · subst ij
        exact (mul_eq_zero.mp hl).resolve_left hj
      · exact hr ij hij
    exact sub_eq_zero.mp (hA (hAx.trans (Matrix.mulVec_zero A).symm))
  obtain ⟨L, hL⟩ := matrix_left_inverse_of_injective _ hinj
  intro hz
  have hd := congrArg Matrix.det hL
  rw [Matrix.det_mul, hz, mul_zero, Matrix.det_one] at hd
  exact zero_ne_one hd

end FD56
