/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericKernelExtension
import FD56.Hilbert.MinimalProfile

/-! Minimal degree lists of affine pencils are invariant under coefficient field extension. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K L a b : Type*} [Field K] [Field L]
  [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

theorem affine_kernel_hilbert_field_extension (φ : K →+* L)
    (A : Matrix a b K[X]) (hA : DegreeBound A 1) (d : ℕ) :
    Module.finrank L (polynomialKernelAtDegree (A.map (Polynomial.mapRingHom φ)) d)=
      Module.finrank K (polynomialKernelAtDegree A d) := by
  have hid : A.map (Polynomial.mapRingHom (RingHom.id K))=A := by
    funext i j
    simp
  have hmap : DegreeBound (A.map (Polynomial.mapRingHom φ)) 1 :=
    fun i j => Polynomial.natDegree_map_le.trans (hA i j)
  apply Nat.le_antisymm
  · have h := polynomial_kernel_finrank_le_of_field_specialization (RingHom.id K) φ φ.injective A d
      (by rw [hid]; exact hA) hmap
    convert h using 1
    exact congrArg (fun B : Matrix a b K[X] => Module.finrank K (polynomialKernelAtDegree B d)) hid.symm
  · have h := polynomial_kernel_finrank_le_of_field_specialization φ (RingHom.id K)
      (Function.injective_id) A d hmap (by rw [hid]; exact hA)
    convert h using 1
    exact congrArg (fun B : Matrix a b K[X] => Module.finrank K (polynomialKernelAtDegree B d)) hid.symm

theorem affine_minimal_degrees_field_extension (φ : K →+* L)
    (A : Matrix a b K[X]) (hA : DegreeBound A 1) (xs : List ℕ)
    (hm : HasMinimalKernelDegrees A xs) :
    HasMinimalKernelDegrees (A.map (Polynomial.mapRingHom φ)) xs := by
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [affine_kernel_hilbert_field_extension φ A hA d]
  exact (hasMinimalKernelDegrees_iff_hilbert _ _).mp hm d

end FD56
