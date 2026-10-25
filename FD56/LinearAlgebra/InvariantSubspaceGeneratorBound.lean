/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.InvariantGraphGeneratorBound
import FD56.LinearAlgebra.CoordinateGraphChart

/-! Generator bounds from an invariant subspace contained in an output kernel. -/

noncomputable section
namespace FD56
open Matrix

universe u v w w'

/-- The columns are a finite basis of the given subspace. -/
def submoduleBasisMatrix {F n : Type*} [Field F] [Fintype n]
    (W : Submodule F (n → F)) : Matrix n (Fin (Module.finrank F W)) F :=
  fun i j => (Module.finBasis F W j).val i

theorem submoduleBasisMatrix_injective {F n : Type*} [Field F] [Fintype n]
    (W : Submodule F (n → F)) : Function.Injective (submoduleBasisMatrix W).mulVec := by
  apply Matrix.mulVec_injective_iff.mpr
  exact (Module.finBasis F W).linearIndependent.map' W.subtype W.ker_subtype

theorem submoduleBasisMatrix_range {F n : Type*} [Field F] [Fintype n]
    (W : Submodule F (n → F)) :
    LinearMap.range (Matrix.toLin' (submoduleBasisMatrix W)) = W := by
  rw [Matrix.range_toLin']
  have h := congrArg (Submodule.map W.subtype) (Module.finBasis F W).span_eq
  simpa only [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
    Submodule.range_subtype] using h

/-- Reindexing ambient coordinates transports the range without choosing new vectors. -/
theorem mem_range_row_reindex_iff {F n s t : Type*} [Field F]
    [Fintype s] [DecidableEq s] (A : Matrix n s F) (e : t ≃ n) (x : t → F) :
    x ∈ LinearMap.range (Matrix.toLin' (A.submatrix e id)) ↔
      x ∘ e.symm ∈ LinearMap.range (Matrix.toLin' A) := by
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨v, ?_⟩
    funext i
    simp only [Matrix.toLin'_apply, Function.comp_apply, Matrix.mulVec, dotProduct,
      Matrix.submatrix_apply, id_eq, Equiv.apply_symm_apply]
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    funext i
    have hi := congrFun hv (e i)
    simpa only [Matrix.toLin'_apply, Function.comp_apply, Matrix.mulVec, dotProduct,
      Matrix.submatrix_apply, id_eq, Equiv.symm_apply_apply] using hi

/-- An actual invariant subspace supplies a reduced family of field generators. -/
theorem exists_invariantSubspace_field_generators
    {K : Type u} {F : Type v} {n : Type w} {m : Type w'}
    [Field K] [Field F] [Algebra K F] [Fintype n] [Fintype m] [DecidableEq n]
    (M : Matrix n n F) (P : Matrix m n F) (W : Submodule F (n → F))
    (hinv : ∀ x ∈ W, M *ᵥ x ∈ W)
    (hker : W ≤ LinearMap.ker (Matrix.toLin' P))
    (hgen : IntermediateField.adjoin K (Set.range (matrixEntryGenerators M P)) = ⊤) :
    ∃ y : Fin (Fintype.card n ^ 2 + Fintype.card m *
        (Fintype.card n - Module.finrank F W)) → F,
      IntermediateField.adjoin K (Set.range y) = ⊤ := by
  classical
  let A := submoduleBasisMatrix W
  obtain ⟨r, C, U, _, _, hchart, hrange⟩ :=
    exists_coordinate_graph_chart A (submoduleBasisMatrix_injective W)
  let t := {i : n // i ∉ Set.range r}
  let e : Fin (Module.finrank F W) ⊕ t ≃ n := coordinateEmbeddingSumEquiv r
  let M' := M.submatrix e e
  let P' := P.submatrix id e
  have hrW (z : (Fin (Module.finrank F W) ⊕ t) → F) :
      z ∈ LinearMap.range (Matrix.toLin' (graphSubspaceBasis C)) ↔ z ∘ e.symm ∈ W := by
    rw [← hrange, mem_range_row_reindex_iff, submoduleBasisMatrix_range]
  have hinv' : ∀ z ∈ LinearMap.range (Matrix.toLin' (graphSubspaceBasis C)),
      M' *ᵥ z ∈ LinearMap.range (Matrix.toLin' (graphSubspaceBasis C)) := by
    intro z hz
    apply (hrW _).mpr
    have hh := FD56.submatrix_mulVec_equiv M e e (z ∘ e.symm)
    have he : (M' *ᵥ z) ∘ e.symm = M *ᵥ (z ∘ e.symm) := by
      simpa [M', Function.comp_def] using congrArg (fun v => v ∘ e.symm) hh
    rw [he]
    exact hinv _ ((hrW z).mp hz)
  have hPA : P * A = 0 := by
    ext i j
    have hj := LinearMap.mem_ker.mp (hker (Module.finBasis F W j).property)
    exact congrFun hj i
  have hker' : P' * graphSubspaceBasis C = 0 := by
    rw [← hchart, ← Matrix.mul_assoc]
    change (P.submatrix id e * A.submatrix e id) * U = 0
    rw [Matrix.submatrix_mul_equiv, hPA]
    simp
  have hgen' : IntermediateField.adjoin K (Set.range (matrixEntryGenerators M' P')) = ⊤ := by
    simpa only [M', P', matrixEntryGenerators_range_submatrix_equiv] using hgen
  have hsmall := invariantGraphChartGenerators_adjoin_eq_top C M' P' hinv' hker' hgen'
  have ht : Fintype.card t = Fintype.card n - Module.finrank F W := by
    dsimp [t]
    rw [Fintype.card_subtype_compl, Fintype.card_range, Fintype.card_fin]
  have hn : Fintype.card (Fin (Module.finrank F W)) + Fintype.card t =
      Fintype.card n := by
    simpa only [Fintype.card_sum] using Fintype.card_congr e
  have hc : Fintype.card (InvariantGraphChartIndex (Fin (Module.finrank F W)) t m) =
      Fintype.card n ^ 2 + Fintype.card m * (Fintype.card n - Module.finrank F W) := by
    rw [invariantGraphChartIndex_card, hn, ht]
  let f := Fintype.equivFinOfCardEq hc
  refine ⟨invariantGraphChartGenerators C M' P' ∘ f.symm, ?_⟩
  rw [f.symm.surjective.range_comp]
  exact hsmall

theorem trdeg_le_invariantSubspace_bound
    {K : Type u} {F : Type v} {n : Type w} {m : Type w'}
    [Field K] [Field F] [Algebra K F] [Fintype n] [Fintype m] [DecidableEq n]
    (M : Matrix n n F) (P : Matrix m n F) (W : Submodule F (n → F))
    (hinv : ∀ x ∈ W, M *ᵥ x ∈ W)
    (hker : W ≤ LinearMap.ker (Matrix.toLin' P))
    (hgen : IntermediateField.adjoin K (Set.range (matrixEntryGenerators M P)) = ⊤) :
    Algebra.trdeg K F ≤ ((Fintype.card n ^ 2 + Fintype.card m *
      (Fintype.card n - Module.finrank F W) : ℕ) : Cardinal.{v}) := by
  obtain ⟨y, hy⟩ := exists_invariantSubspace_field_generators M P W hinv hker hgen
  simpa only [Fintype.card_fin] using trdeg_le_card_of_finite_field_generators y hy

theorem card_algebraicIndependent_le_invariantSubspace_bound
    {K : Type u} {F : Type v} {n : Type w} {m : Type w'} {κ : Type*}
    [Field K] [Field F] [Algebra K F] [Fintype n] [Fintype m] [Fintype κ] [DecidableEq n]
    {x : κ → F} (hx : AlgebraicIndependent K x)
    (M : Matrix n n F) (P : Matrix m n F) (W : Submodule F (n → F))
    (hinv : ∀ z ∈ W, M *ᵥ z ∈ W)
    (hker : W ≤ LinearMap.ker (Matrix.toLin' P))
    (hgen : IntermediateField.adjoin K (Set.range (matrixEntryGenerators M P)) = ⊤) :
    Fintype.card κ ≤ Fintype.card n ^ 2 + Fintype.card m *
      (Fintype.card n - Module.finrank F W) := by
  obtain ⟨y, hy⟩ := exists_invariantSubspace_field_generators M P W hinv hker hgen
  simpa only [Fintype.card_fin] using
    card_le_card_of_algebraicIndependent_of_finite_field_generators hx y hy

end FD56
