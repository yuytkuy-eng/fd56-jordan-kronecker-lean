/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.DerivationAlgebraicIndependence
import FD56.LinearAlgebra.RankSpecializationExtension
import FD56.LinearAlgebra.AlgebraicDominance

/-! Independent coordinates selected from the image of coefficient derivations. -/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]

def derivationValuesMap (f : ι → L) : Derivation K L L →ₗ[L] (ι → L) where
  toFun D i := D (f i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem exists_algebraicIndependent_subfamily_of_derivation_rank
    [CharZero K] [Fintype ι] (f : ι → L) :
    ∃ (r : ℕ) (g : Fin r → ι), Function.Injective g ∧
      r=Module.finrank L (LinearMap.range (derivationValuesMap (K:=K) f)) ∧
      AlgebraicIndependent K (f ∘ g) := by
  classical
  let E := LinearMap.range (derivationValuesMap (K:=K) f)
  let b := Module.finBasis L E
  let M : Matrix ι (Fin (Module.finrank L E)) L := fun i j => (b j).val i
  have hM : Function.Injective M.mulVec := by
    apply Matrix.mulVec_injective_iff.mpr
    exact b.linearIndependent.map' E.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  obtain ⟨J,hJ⟩ := matrix_left_inverse_of_injective M hM
  have ht : M.transpose*J.transpose=1 := by
    rw [← Matrix.transpose_mul,hJ,Matrix.transpose_one]
  have hsurj : Function.Surjective M.transpose.mulVec := by
    intro v
    exact ⟨J.transpose *ᵥ v,by rw [Matrix.mulVec_mulVec,ht,Matrix.one_mulVec]⟩
  obtain ⟨κ,g,hg,hs,hi⟩ := exists_linearIndependent' L M.row
  letI : Finite κ := Finite.of_injective g hg
  letI : Fintype κ := Fintype.ofFinite κ
  let A : Matrix κ (Fin (Module.finrank L E)) L := M.submatrix g id
  have hA : Function.Injective A.transpose.mulVec := Matrix.mulVec_injective_iff.mpr hi
  obtain ⟨Q,hQ⟩ := matrix_left_inverse_of_injective A.transpose hA
  have hAt : A*Q.transpose=1 := by
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_one]
      using congrArg Matrix.transpose hQ
  have hAsurj : Function.Surjective A.mulVec := by
    intro v
    exact ⟨Q.transpose *ᵥ v,by rw [Matrix.mulVec_mulVec,hAt,Matrix.one_mulVec]⟩
  have htop : Submodule.span L (Set.range M.row)=⊤ := by
    change Submodule.span L (Set.range M.transpose.col)=⊤
    rw [← Matrix.range_toLin' M.transpose]
    exact LinearMap.range_eq_top.mpr hsurj
  have hcard : Fintype.card κ=Module.finrank L E := by
    have h := finrank_span_eq_card hi
    rw [hs,htop,finrank_top,Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at h
    exact h.symm
  have hind : AlgebraicIndependent K (f ∘ g) := by
    apply algebraicIndependent_of_derivation_values_surjective
    intro u
    obtain ⟨v,hv⟩ := hAsurj u
    let w : E := ∑ j, v j • b j
    obtain ⟨D,hD⟩ := w.property
    refine ⟨D,?_⟩
    intro i
    have h := congrFun hD (g i)
    change D (f (g i)) = w.val (g i) at h
    change D (f (g i)) = u i
    rw [h]
    have he : w.val (g i)=(A *ᵥ v) i := by
      simp [w,A,M,Matrix.mulVec,dotProduct,smul_eq_mul,mul_comm]
    rw [he,hv]
  refine ⟨Fintype.card κ,g ∘ (Fintype.equivFin κ).symm,
    hg.comp (Fintype.equivFin κ).symm.injective,hcard,?_⟩
  exact hind.comp _ (Fintype.equivFin κ).symm.injective

/-- A sufficiently large actual differential image prevents every nonzero
relation from being lost under specialization of a domain. -/
theorem injective_of_derivation_rank_bound
    [CharZero K] [Fintype ι] {A : Type*} [CommRing A] [IsDomain A] [Algebra K A]
    (φ : A →ₐ[K] L) (x : ι → A)
    (htr : Algebra.trdeg K A ≤ (Module.finrank L
      (LinearMap.range (derivationValuesMap (K:=K) (φ ∘ x))) : Cardinal)) :
    Function.Injective φ := by
  obtain ⟨r,g,_,hr,hi⟩ :=
    exists_algebraicIndependent_subfamily_of_derivation_rank (K:=K) (φ ∘ x)
  apply injective_of_independent_cardinality_bound φ (x:=x ∘ g) hi
  simpa only [Fintype.card_fin,hr] using htr

end FD56
