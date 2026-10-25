/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.FullKrylovGeneratorBound
import FD56.LinearAlgebra.NonzeroMaximalMinor
import Mathlib.Logic.Equiv.Set

/-! The full-rank Krylov generator bound without a prescribed coordinate chart. -/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators

universe u v w w'

/-- Complete a coordinate embedding by the coordinates outside its range. -/
def coordinateEmbeddingSumEquiv {s n : Type*} (r : s ↪ n) :
    s ⊕ {i : n // i ∉ Set.range r} ≃ n := by
  classical
  exact ((Equiv.ofInjective r r.injective).sumCongr (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range r))

@[simp] theorem coordinateEmbeddingSumEquiv_inl {s n : Type*} (r : s ↪ n) (j : s) :
    coordinateEmbeddingSumEquiv r (Sum.inl j) = r j := by
  rfl

theorem submatrix_mulVec_equiv {F n a s b : Type*} [Semiring F]
    [Fintype n] [Fintype s] (A : Matrix a n F) (r : b → a) (e : s ≃ n)
    (v : n → F) :
    A.submatrix r e *ᵥ (v ∘ e) = (A *ᵥ v) ∘ r := by
  funext i
  exact e.sum_comp (fun j => A (r i) j * v j)

theorem submatrix_power_mulVec_equiv {F n s : Type*} [Semiring F]
    [Fintype n] [Fintype s] [DecidableEq n] [DecidableEq s]
    (M : Matrix n n F) (e : s ≃ n) (v : n → F) (k : ℕ) :
    (M.submatrix e e) ^ k *ᵥ (v ∘ e) = (M ^ k *ᵥ v) ∘ e := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, pow_succ', ← Matrix.mulVec_mulVec]
    exact submatrix_mulVec_equiv M e e _

theorem matrixEntryGenerators_range_submatrix_equiv {F n s m : Type*}
    (M : Matrix n n F) (P : Matrix m n F) (e : s ≃ n) :
    Set.range (matrixEntryGenerators (M.submatrix e e) (P.submatrix id e)) =
      Set.range (matrixEntryGenerators M P) := by
  ext z
  constructor
  · rintro ⟨ij, rfl⟩
    cases ij with
    | inl ij => exact ⟨Sum.inl (e ij.1, e ij.2), rfl⟩
    | inr ij => exact ⟨Sum.inr (ij.1, e ij.2), rfl⟩
  · rintro ⟨ij, rfl⟩
    cases ij with
    | inl ij =>
      refine ⟨Sum.inl (e.symm ij.1, e.symm ij.2), ?_⟩
      simp [matrixEntryGenerators, Matrix.submatrix]
    | inr ij =>
      refine ⟨Sum.inr (ij.1, e.symm ij.2), ?_⟩
      simp [matrixEntryGenerators, Matrix.submatrix]

/-- Independent Krylov columns yield the full-rank generator bound over arbitrary fields. -/
theorem card_algebraicIndependent_le_fullKrylov_bound
    {K : Type u} {F : Type v} {n : Type w} {m : Type w'} {κ : Type*}
    [Field K] [Field F] [Algebra K F] [Fintype n] [DecidableEq n]
    [Fintype m] [Fintype κ] {x : κ → F} (hx : AlgebraicIndependent K x)
    {q : ℕ} (M : Matrix n n F) (P : Matrix m n F) (v : n → F) (c : n)
    (hv : v c = 1) (hlin : LinearIndependent F (fun j : Fin q => M ^ j.val *ᵥ v))
    (hker : ∀ j : Fin q, P *ᵥ (M ^ j.val *ᵥ v) = 0)
    (hgen : IntermediateField.adjoin K (Set.range (matrixEntryGenerators M P)) = ⊤) :
    Fintype.card κ ≤ Fintype.card n ^ 2 + (Fintype.card n - 1) +
      Fintype.card m * (Fintype.card n - q) := by
  classical
  obtain ⟨r, hr⟩ := exists_nonsingular_coordinate_embedding (krylovMatrix M v q)
    (Matrix.mulVec_injective_iff.mpr hlin)
  let t := {i : n // i ∉ Set.range r}
  let e : Fin q ⊕ t ≃ n := coordinateEmbeddingSumEquiv r
  let M' := M.submatrix e e
  let P' := P.submatrix id e
  let v' := v ∘ e
  let A := (krylovMatrix M v q).submatrix r id
  have hpivot : (krylovMatrix M' v' q).submatrix Sum.inl id = A := by
    ext i j
    change ((M.submatrix e e) ^ j.val *ᵥ (v ∘ e)) (Sum.inl i) =
      (M ^ j.val *ᵥ v) (r i)
    rw [submatrix_power_mulVec_equiv]
    rfl
  have hU : (krylovMatrix M' v' q).submatrix Sum.inl id * A⁻¹ = 1 := by
    rw [hpivot]
    exact Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hr)
  have hv' : v' (e.symm c) = 1 := by simpa [v'] using hv
  have hker' : ∀ j : Fin q, P' *ᵥ (M' ^ j.val *ᵥ v') = 0 := by
    intro j
    dsimp [P', M', v']
    rw [submatrix_power_mulVec_equiv, submatrix_mulVec_equiv, hker j]
    rfl
  have hgen' : IntermediateField.adjoin K (Set.range (matrixEntryGenerators M' P')) = ⊤ := by
    simpa only [M', P', matrixEntryGenerators_range_submatrix_equiv] using hgen
  have hb := card_algebraicIndependent_le_fullKrylovChart_bound hx M' P' v' (e.symm c)
    A⁻¹ hv' hker' hU hgen'
  simpa only [Fintype.card_congr e] using hb

end FD56
