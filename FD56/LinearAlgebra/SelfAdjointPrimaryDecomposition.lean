/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.SelfAdjointFitting
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Algebra.DirectSum.Module

/-! Orthogonality and assembly of the primary spaces of a self-adjoint operator. -/

noncomputable section
namespace FD56
open DirectSum
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance : DecidableEq K := Classical.decEq K

theorem primary_space_le_shift_power_range (f : Module.End K V) (a b : K)
    (hab : a≠b) (k : ℕ) :
    f.maxGenEigenspace b ≤ LinearMap.range ((f-a•1)^k) := by
  let U := f.maxGenEigenspace b
  let g := (f-a•1)^k
  have hg : ∀ x ∈ U, g x ∈ U := by
    intro x hx
    exact f.mapsTo_genEigenspace_of_comm
      (Algebra.mul_sub_algebraMap_pow_commutes f a k) b ⊤ hx
  let r := g.restrict hg
  have hi : Function.Injective r := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro x hx
    rw [Submodule.mem_bot]
    apply Subtype.ext
    have hxg : g x.val=0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    have hxa : x.val ∈ f.genEigenspace a (k : ℕ∞) := by
      rw [Module.End.genEigenspace_nat]
      exact hxg
    have hz : x.val ∈ (⊥ : Submodule K V) := by
      rw [← (f.disjoint_genEigenspace hab (k : ℕ∞) ⊤).eq_bot]
      exact ⟨hxa,x.property⟩
    exact hz
  have hs : Function.Surjective r := (LinearMap.injective_iff_surjective).mp hi
  intro y hy
  obtain ⟨x,hx⟩ := hs ⟨y,hy⟩
  exact ⟨x.val,congrArg Subtype.val hx⟩

theorem bilinear_primary_spaces_orthogonal
    (B : V →ₗ[K] V →ₗ[K] K) (f : Module.End K V)
    (hf : ∀ x y, B (f x) y=B x (f y)) (a b : K) (hab : a≠b)
    (x y : V) (hx : x ∈ f.maxGenEigenspace a) (hy : y ∈ f.maxGenEigenspace b) :
    B x y=0 := by
  apply bilinear_power_kernel_range_orthogonal B (f-a•1)
    (bilinear_self_adjoint_shift B f hf a) (Module.finrank K V) x y
  · simpa only [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
      Module.End.genEigenspace_nat] using hx
  · exact primary_space_le_shift_power_range f a b hab _ hy

theorem bilinear_primary_spaces_commuting_orthogonal
    (B : V →ₗ[K] V →ₗ[K] K) (f g : Module.End K V)
    (hf : ∀ x y, B (f x) y=B x (f y)) (hfg : Commute f g)
    (a b : K) (hab : a≠b) (x y : V)
    (hx : x ∈ f.maxGenEigenspace a) (hy : y ∈ f.maxGenEigenspace b) :
    B x (g y)=0 :=
  bilinear_primary_spaces_orthogonal B f hf a b hab x (g y) hx
    (Module.End.mapsTo_maxGenEigenspace_of_comm hfg b hy)

theorem primary_eigenvalues_span [IsAlgClosed K] (f : Module.End K V) :
    (⨆ a : f.Eigenvalues, f.maxGenEigenspace a.val)=⊤ := by
  apply le_antisymm le_top
  rw [← f.iSup_maxGenEigenspace_eq_top]
  apply iSup_le
  intro a
  by_cases ha : f.HasEigenvalue a
  · exact le_iSup (fun a : f.Eigenvalues => f.maxGenEigenspace a.val) ⟨a,ha⟩
  · have hz : f.maxGenEigenspace a=⊥ := by
      by_contra h
      exact ha (Module.End.HasUnifEigenvalue.lt zero_lt_one h)
    rw [hz]
    exact bot_le

theorem primary_eigenvalues_internal [IsAlgClosed K] (f : Module.End K V) :
    DirectSum.IsInternal (fun a : f.Eigenvalues => f.maxGenEigenspace a.val) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact f.independent_maxGenEigenspace.comp Subtype.val_injective
  · exact primary_eigenvalues_span f

def primaryDecompositionEquiv [IsAlgClosed K] (f : Module.End K V) :
    (⨁ a : f.Eigenvalues, f.maxGenEigenspace a.val) ≃ₗ[K] V := by
  classical
  exact LinearEquiv.ofBijective (DirectSum.coeLinearMap _) (primary_eigenvalues_internal f)

def primaryCollectedBasis [IsAlgClosed K] (f : Module.End K V)
    {α : f.Eigenvalues → Type*}
    (e : ∀ a, Basis (α a) K (f.maxGenEigenspace a.val)) :
    Basis (Σ a, α a) K V := by
  classical
  exact (primary_eigenvalues_internal f).collectedBasis e

theorem primaryCollectedBasis_apply [IsAlgClosed K] (f : Module.End K V)
    {α : f.Eigenvalues → Type*}
    (e : ∀ a, Basis (α a) K (f.maxGenEigenspace a.val)) (i : Σ a, α a) :
    primaryCollectedBasis f e i=(e i.1 i.2).val := by
  classical
  exact congrFun ((primary_eigenvalues_internal f).collectedBasis_coe e) i

theorem primaryCollectedBasis_pairing_zero [IsAlgClosed K]
    (B : V →ₗ[K] V →ₗ[K] K) (f : Module.End K V)
    (hf : ∀ x y, B (f x) y=B x (f y))
    {α : f.Eigenvalues → Type*}
    (e : ∀ a, Basis (α a) K (f.maxGenEigenspace a.val))
    (i j : Σ a, α a) (hij : i.1≠j.1) :
    B (primaryCollectedBasis f e i) (primaryCollectedBasis f e j)=0 := by
  rw [primaryCollectedBasis_apply,primaryCollectedBasis_apply]
  apply bilinear_primary_spaces_orthogonal B f hf i.1.val j.1.val
    (fun h => hij (Subtype.ext h)) _ _ (e i.1 i.2).property (e j.1 j.2).property

theorem primaryCollectedBasis_operator_pairing_zero [IsAlgClosed K]
    (B : V →ₗ[K] V →ₗ[K] K) (f : Module.End K V)
    (hf : ∀ x y, B (f x) y=B x (f y))
    {α : f.Eigenvalues → Type*}
    (e : ∀ a, Basis (α a) K (f.maxGenEigenspace a.val))
    (i j : Σ a, α a) (hij : i.1≠j.1) :
    B (primaryCollectedBasis f e i) (f (primaryCollectedBasis f e j))=0 := by
  rw [primaryCollectedBasis_apply,primaryCollectedBasis_apply]
  exact bilinear_primary_spaces_commuting_orthogonal B f f hf (Commute.refl f)
    i.1.val j.1.val (fun h => hij (Subtype.ext h)) _ _
    (e i.1 i.2).property (e j.1 j.2).property

end FD56
