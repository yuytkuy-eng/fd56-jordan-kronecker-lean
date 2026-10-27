/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Projection

/-! Orthogonal Fitting decompositions for an operator self-adjoint relative to a bilinear form. -/

noncomputable section
namespace FD56
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem bilinear_self_adjoint_pow (B : V →ₗ[K] V →ₗ[K] K) (f : Module.End K V)
    (hf : ∀ x y, B (f x) y=B x (f y)) (k : ℕ) :
    ∀ x y, B ((f^k) x) y=B x ((f^k) y) := by
  induction k with
  | zero => simp
  | succ k ih =>
    intro x y
    rw [pow_succ,Module.End.mul_apply,ih,hf,← Module.End.mul_apply,← pow_succ']
    rw [pow_succ]

theorem bilinear_self_adjoint_shift (B : V →ₗ[K] V →ₗ[K] K) (f : Module.End K V)
    (hf : ∀ x y, B (f x) y=B x (f y)) (a : K) :
    ∀ x y, B ((f-a•1) x) y=B x ((f-a•1) y) := by
  intro x y
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
    map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul,hf]

theorem bilinear_power_kernel_range_orthogonal (B : V →ₗ[K] V →ₗ[K] K)
    (f : Module.End K V) (hf : ∀ x y, B (f x) y=B x (f y)) (k : ℕ)
    (x y : V) (hx : x ∈ LinearMap.ker (f^k)) (hy : y ∈ LinearMap.range (f^k)) :
    B x y=0 := by
  obtain ⟨z,rfl⟩ := hy
  rw [← bilinear_self_adjoint_pow B f hf k,LinearMap.mem_ker.mp hx]
  simp

theorem fitting_kernel_range_isCompl [FiniteDimensional K V] (f : Module.End K V) (a : K) :
    IsCompl (LinearMap.ker ((f-a•1)^Module.finrank K V))
      (LinearMap.range ((f-a•1)^Module.finrank K V)) := by
  have hd := Module.End.generalized_eigenvec_disjoint_range_ker f a
  rw [Module.End.genEigenrange_nat,Module.End.genEigenspace_nat] at hd
  have hr := ((f-a•1)^Module.finrank K V).finrank_range_add_finrank_ker
  have ht := Submodule.eq_top_of_disjoint _ _ hr.ge hd
  exact (isCompl_iff.mpr ⟨hd,codisjoint_iff.mpr ht⟩).symm

theorem bilinear_restriction_nondegenerate_of_orthogonal_complement
    (B : V →ₗ[K] V →ₗ[K] K) (U W : Submodule K V) (hc : IsCompl U W)
    (hn : ∀ x, (∀ y, B x y=0) → x=0)
    (ho : ∀ x ∈ U, ∀ y ∈ W, B x y=0) :
    ∀ x ∈ U, (∀ y ∈ U, B x y=0) → x=0 := by
  intro x hx hz
  apply hn x
  intro y
  have hy : y ∈ U ⊔ W := by rw [hc.sup_eq_top]; trivial
  obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp hy
  rw [map_add,hz u hu,ho x hx w hw,add_zero]

theorem bilinear_self_adjoint_fitting_orthogonal [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] K) (f : Module.End K V)
    (hf : ∀ x y, B (f x) y=B x (f y)) (a : K) :
    let U := LinearMap.ker ((f-a•1)^Module.finrank K V)
    let W := LinearMap.range ((f-a•1)^Module.finrank K V)
    IsCompl U W ∧ ∀ x ∈ U, ∀ y ∈ W, B x y=0 := by
  exact ⟨fitting_kernel_range_isCompl f a,
    fun x hx y hy => bilinear_power_kernel_range_orthogonal B (f-a•1)
      (bilinear_self_adjoint_shift B f hf a) _ x y hx hy⟩

end FD56
