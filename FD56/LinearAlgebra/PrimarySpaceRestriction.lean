/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PrimarySpaceDimension

/-! The nilpotent primary restriction preserves the kernel of the shifted operator. -/

noncomputable section
namespace FD56
open Polynomial
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def restrictionKernelEquiv (f : Module.End K V) (U : Submodule K V)
    (hU : ∀ x ∈ U, f x ∈ U) (hk : LinearMap.ker f ≤ U) :
    LinearMap.ker (f.restrict hU) ≃ₗ[K] LinearMap.ker f where
  toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
  invFun x := ⟨⟨x.val,hk x.property⟩,Subtype.ext x.property⟩
  left_inv _ := by rfl
  right_inv _ := by rfl
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

def primaryShift (f : Module.End K V) (a : K) : Module.End K (f.maxGenEigenspace a) :=
  (f-algebraMap K (Module.End K V) a).restrict
    (Module.End.mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f a) a)

theorem primaryShift_nilpotent [FiniteDimensional K V] (f : Module.End K V) (a : K) :
    IsNilpotent (primaryShift f a) :=
  Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap f a

theorem primaryShift_kernel_finrank [FiniteDimensional K V] (f : Module.End K V) (a : K) :
    Module.finrank K (LinearMap.ker (primaryShift f a))=
      Module.finrank K (LinearMap.ker (f-a•1)) := by
  have hk : LinearMap.ker (f-algebraMap K (Module.End K V) a) ≤ f.maxGenEigenspace a := by
    intro v hv
    rw [Module.End.mem_maxGenEigenspace]
    refine ⟨1,?_⟩
    simpa only [pow_one,Module.algebraMap_end_eq_smul_id] using hv
  exact (restrictionKernelEquiv _ _ _ hk).finrank_eq

theorem primaryShift_range_finrank [FiniteDimensional K V] (f : Module.End K V) (a : K) :
    Module.finrank K (LinearMap.range (primaryShift f a))=
      rootMultiplicity a f.charpoly-Module.finrank K (LinearMap.ker (f-a•1)) := by
  have h := (primaryShift f a).finrank_range_add_finrank_ker
  rw [primaryShift_kernel_finrank,primary_space_finrank_eq_rootMultiplicity] at h
  omega

theorem primaryShift_range_finrank_two [FiniteDimensional K V] (f : Module.End K V)
    (a : K) (m : ℕ) (hm : 1≤m)
    (hmult : rootMultiplicity a f.charpoly=2*m)
    (hker : Module.finrank K (LinearMap.ker (f-a•1))=2*m-2) :
    Module.finrank K (LinearMap.range (primaryShift f a))=2 := by
  rw [primaryShift_range_finrank,hmult,hker]
  omega

end FD56
