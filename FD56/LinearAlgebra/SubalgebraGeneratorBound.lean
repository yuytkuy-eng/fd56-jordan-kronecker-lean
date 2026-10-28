/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-! A source algebra embedded in an algebra with finitely many generators
inherits the corresponding transcendence-degree bound. -/

noncomputable section
namespace FD56

universe u v w z
variable {K : Type u} {A : Type v} {B : Type w} {ι : Type z}
  [Field K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] [Fintype ι]

theorem trdeg_adjoin_le_card_of_finite_generators (y : ι → B) :
    Algebra.trdeg K (Algebra.adjoin K (Set.range y)) ≤ (Fintype.card ι : Cardinal.{w}) := by
  have h := lift_trdeg_le_of_surjective
    (MvPolynomial.aeval y : MvPolynomial ι K →ₐ[K] B).rangeRestrict
    (AlgHom.rangeRestrict_surjective (MvPolynomial.aeval y : MvPolynomial ι K →ₐ[K] B))
  rw [← Algebra.adjoin_range_eq_range_aeval] at h
  simpa only [MvPolynomial.trdeg_of_isDomain,Cardinal.mk_fintype,Cardinal.lift_natCast,
    Cardinal.lift_le_nat_iff] using h

theorem trdeg_le_card_of_injective_into_adjoin (φ : A →ₐ[K] B)
    (hφ : Function.Injective φ) (y : ι → B)
    (hy : ∀ a, φ a ∈ Algebra.adjoin K (Set.range y)) :
    Algebra.trdeg K A ≤ (Fintype.card ι : Cardinal.{v}) := by
  let ψ : A →ₐ[K] Algebra.adjoin K (Set.range y) := φ.codRestrict _ hy
  have hi : Function.Injective ψ := by
    intro a b h
    exact hφ (congrArg Subtype.val h)
  have h := lift_trdeg_le_of_injective ψ hi
  have hb := trdeg_adjoin_le_card_of_finite_generators (K:=K) y
  have h' := h.trans (Cardinal.lift_le.2 hb)
  simpa only [Cardinal.lift_natCast,Cardinal.lift_le_nat_iff] using h'

/-- Fixed base-field coordinates cost no generators; retain one scalar for
the common multiplier of the normalized coordinates. -/
theorem trdeg_le_card_sub_fixed_add_one (φ : A →ₐ[K] B)
    (hφ : Function.Injective φ) (x : ι → B) (c : B) (S : Finset ι)
    (hfixed : ∀ i ∈ S, x i ∈ Set.range (algebraMap K B))
    (hsource : ∀ a, φ a ∈ Algebra.adjoin K (insert c (Set.range x))) :
    Algebra.trdeg K A ≤ (Fintype.card ι-S.card+1 : ℕ) := by
  classical
  let y : Option {i // i ∉ S} → B := fun z =>
    match z with
    | none => c
    | some i => x i.val
  let T := Algebra.adjoin K (Set.range y)
  have hc : c ∈ T := Algebra.subset_adjoin (Set.mem_range_self none)
  have hx (i : ι) : x i ∈ T := by
    by_cases hi : i ∈ S
    · obtain ⟨k,hk⟩ := hfixed i hi
      rw [← hk]
      exact T.algebraMap_mem k
    · exact Algebra.subset_adjoin (show x i ∈ Set.range y from ⟨some ⟨i,hi⟩,rfl⟩)
  have hT : Algebra.adjoin K (insert c (Set.range x)) ≤ T := by
    apply Algebra.adjoin_le
    rintro z (rfl | ⟨i,rfl⟩)
    · exact hc
    · exact hx i
  have h := trdeg_le_card_of_injective_into_adjoin φ hφ y (fun a => hT (hsource a))
  simpa only [Fintype.card_option,Fintype.card_subtype_compl,Fintype.card_coe] using h

omit [Fintype ι] in
theorem scaled_two_column_minor_coeff_mem {m : Type*} (T : Subalgebra K B)
    (c : B) (u v : m → Polynomial B) (hc : c ∈ T)
    (hu : ∀ i k, (u i).coeff k ∈ T) (hv : ∀ i k, (v i).coeff k ∈ T)
    (i j : m) (k : ℕ) :
    (Polynomial.C c*(u i*v j-u j*v i)).coeff k ∈ T := by
  rw [Polynomial.coeff_C_mul,Polynomial.coeff_sub]
  apply T.mul_mem hc
  apply T.sub_mem
  · rw [Polynomial.coeff_mul]
    apply T.sum_mem
    intro z _
    exact T.mul_mem (hu i z.1) (hv j z.2)
  · rw [Polynomial.coeff_mul]
    apply T.sum_mem
    intro z _
    exact T.mul_mem (hu j z.1) (hv i z.2)

end FD56
