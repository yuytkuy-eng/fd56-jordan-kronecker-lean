/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import FD56.LinearAlgebra.RankSpecializationExtension

/-! Injectivity of specialization from a preserved transcendence basis. -/

noncomputable section
namespace FD56
open scoped nonZeroDivisors

universe u v w z
variable {K : Type u} {A : Type v} {B : Type w} {ι : Type z}
  [Field K] [CommRing A] [IsDomain A] [CommRing B] [Algebra K A] [Algebra K B]

/-- An algebraic domain cannot acquire a nonzero kernel when its transcendence
basis remains algebraically independent after specialization. -/
theorem injective_of_independent_transcendence_basis (φ : A →ₐ[K] B)
    {x : ι → A} (hx : IsTranscendenceBasis K x)
    (hφx : AlgebraicIndependent K (φ ∘ x)) : Function.Injective φ := by
  letI := hx.isAlgebraic
  apply (injective_iff_map_eq_zero φ).2
  intro a hφa
  by_contra ha
  obtain ⟨b, hb, c, hc⟩ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := Algebra.adjoin K (Set.range x)) a).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero ha)
  have hφb : φ (b : A) = 0 := by
    change φ (algebraMap (Algebra.adjoin K (Set.range x)) A b) = 0
    rw [hc, map_mul, hφa, zero_mul]
  have hbr : (b : A) ∈ (MvPolynomial.aeval x : MvPolynomial ι K →ₐ[K] A).range := by
    rw [← Algebra.adjoin_range_eq_range_aeval]
    exact b.property
  obtain ⟨p, hp⟩ := hbr
  change MvPolynomial.aeval x p = (b : A) at hp
  have hp0 : p = 0 := hφx.eq_zero_of_aeval_eq_zero p (by
    change MvPolynomial.aeval (fun i => φ (x i)) p = 0
    rw [← MvPolynomial.comp_aeval_apply, hp]
    exact hφb)
  apply hb
  apply Subtype.ext
  change (b : A) = 0
  rw [← hp, hp0, map_zero]

/-- A finite independent image of maximal possible size already prevents all
new polynomial relations in the source domain. The index universe is arbitrary. -/
theorem injective_of_independent_cardinality_bound [Fintype ι]
    (φ : A →ₐ[K] B) {x : ι → A}
    (hφx : AlgebraicIndependent K (φ ∘ x))
    (htr : Algebra.trdeg K A ≤ (Fintype.card ι : Cardinal.{v})) :
    Function.Injective φ := by
  have hx := AlgebraicIndependent.of_comp φ hφx
  apply injective_of_independent_transcendence_basis φ _ hφx
  apply hx.isTranscendenceBasis_of_lift_trdeg_le_of_finite
  simpa only [Cardinal.mk_fintype, Cardinal.lift_natCast] using
    (Cardinal.lift_le.{z}.2 htr)

/-- A finite-field or other specialized matrix certificate transfers whenever
the actual family preserves a full independent parameter family. -/
theorem matrix_injective_of_independent_specialization [Fintype ι]
    {L F r c : Type*} [Field L] [Field F] [Algebra K L]
    [Fintype r] [Fintype c] [DecidableEq r] [DecidableEq c]
    (φ : A →ₐ[K] L) (ψ : A →+* F) {x : ι → A}
    (hφx : AlgebraicIndependent K (φ ∘ x))
    (htr : Algebra.trdeg K A ≤ (Fintype.card ι : Cardinal.{v}))
    (M : Matrix r c A) (hM : Function.Injective (M.map ψ).mulVec) :
    Function.Injective (M.map φ.toRingHom).mulVec :=
  matrix_injective_of_field_specialization ψ φ.toRingHom
    (injective_of_independent_cardinality_bound φ hφx htr) M hM

theorem matrix_kernel_finrank_le_of_independent_specialization [Fintype ι]
    {L F r c : Type*} [Field L] [Field F] [Algebra K L]
    [Fintype r] [Fintype c] [DecidableEq r] [DecidableEq c]
    (φ : A →ₐ[K] L) (ψ : A →+* F) {x : ι → A}
    (hφx : AlgebraicIndependent K (φ ∘ x))
    (htr : Algebra.trdeg K A ≤ (Fintype.card ι : Cardinal.{v}))
    (M : Matrix r c A) :
    Module.finrank L (LinearMap.ker (Matrix.toLin' (M.map φ.toRingHom))) ≤
      Module.finrank F (LinearMap.ker (Matrix.toLin' (M.map ψ))) :=
  matrix_kernel_finrank_le_of_field_specialization ψ φ.toRingHom
    (injective_of_independent_cardinality_bound φ hφx htr) M

end FD56
