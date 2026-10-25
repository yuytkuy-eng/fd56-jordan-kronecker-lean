/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-! Transcendence-degree bounds from a finite family of field generators. -/

noncomputable section
namespace FD56
open scoped nonZeroDivisors

universe u v w w'
variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

theorem isAlgebraic_algebra_adjoin_of_field_adjoin_eq_top (S : Set F)
    (hS : IntermediateField.adjoin K S = ⊤) :
    Algebra.IsAlgebraic (Algebra.adjoin K S) F := by
  letI : IsFractionRing (Algebra.adjoin K S) F := IsFractionRing.of_field _ _ (fun z => by
    have hz : z ∈ IntermediateField.adjoin K S := by rw [hS]; trivial
    obtain ⟨x, hx, y, hy, he⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, he⟩)
  exact IsLocalization.isAlgebraic F (Algebra.adjoin K S)⁰

theorem trdeg_le_cardinalMk_of_field_adjoin_eq_top (S : Set F)
    (hS : IntermediateField.adjoin K S = ⊤) :
    Algebra.trdeg K F ≤ Cardinal.mk S := by
  letI := isAlgebraic_algebra_adjoin_of_field_adjoin_eq_top S hS
  exact Algebra.IsAlgebraic.trdeg_le_cardinalMk K S

/-- The generator index may live in a different universe from the extension field. -/
theorem trdeg_le_card_of_finite_field_generators {ι : Type w} [Fintype ι] (y : ι → F)
    (hy : IntermediateField.adjoin K (Set.range y) = ⊤) :
    Algebra.trdeg K F ≤ (Fintype.card ι : Cardinal.{v}) := by
  classical
  letI : Fintype (Set.range y) := Fintype.ofFinite _
  have hc : Fintype.card (Set.range y) ≤ Fintype.card ι :=
    Fintype.card_le_of_surjective (fun i => (⟨y i, Set.mem_range_self i⟩ : Set.range y)) (by
      rintro ⟨z, i, rfl⟩
      exact ⟨i, rfl⟩)
  have ht := trdeg_le_cardinalMk_of_field_adjoin_eq_top (Set.range y) hy
  rw [Cardinal.mk_fintype] at ht
  exact ht.trans (by exact_mod_cast hc)

/-- A finite independent family cannot be larger than a finite family of field generators. -/
theorem card_le_card_of_algebraicIndependent_of_finite_field_generators
    {κ : Type w'} {ι : Type w} [Fintype κ] [Fintype ι]
    {x : κ → F} (hx : AlgebraicIndependent K x) (y : ι → F)
    (hy : IntermediateField.adjoin K (Set.range y) = ⊤) :
    Fintype.card κ ≤ Fintype.card ι := by
  have hi : (Fintype.card κ : Cardinal.{v}) ≤ Algebra.trdeg K F := by
    simpa only [Cardinal.mk_fintype, Cardinal.lift_natCast, Cardinal.nat_le_lift_iff]
      using hx.lift_cardinalMk_le_trdeg
  exact_mod_cast hi.trans (trdeg_le_card_of_finite_field_generators y hy)

end FD56
