/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.FractionRing

/-! Coordinate generators for fraction fields of polynomial quotients. -/

namespace FD56

variable {K F σ : Type*} [Field K] [Field F] [Algebra K F]

theorem polynomial_image_mem_field_adjoin (φ : MvPolynomial σ K →ₐ[K] F)
    (p : MvPolynomial σ K) :
    φ p ∈ IntermediateField.adjoin K (Set.range fun i : σ => φ (MvPolynomial.X i)) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      change φ (algebraMap K (MvPolynomial σ K) c) ∈ _
      rw [φ.commutes]
      exact IntermediateField.algebraMap_mem _ c
  | add p q hp hq =>
      rw [map_add]
      exact IntermediateField.add_mem _ hp hq
  | mul_X p i hp =>
      rw [map_mul]
      exact IntermediateField.mul_mem _ hp
        (IntermediateField.subset_adjoin K _ (Set.mem_range_self i))

theorem field_adjoin_polynomial_coordinates_eq_top (φ : MvPolynomial σ K →ₐ[K] F)
    (hφ : ∀ z : F, ∃ p q : MvPolynomial σ K, z = φ p / φ q) :
    IntermediateField.adjoin K (Set.range fun i : σ => φ (MvPolynomial.X i)) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨p, q, rfl⟩ := hφ z
  exact IntermediateField.div_mem _ (polynomial_image_mem_field_adjoin φ p)
    (polynomial_image_mem_field_adjoin φ q)

/-- Quotient coordinates generate every compatible fraction field.
Primality is not needed separately for this generation statement. -/
theorem quotient_fraction_field_coordinates_generate
    (I : Ideal (MvPolynomial σ K))
    [Algebra (MvPolynomial σ K ⧸ I) F]
    [IsFractionRing (MvPolynomial σ K ⧸ I) F]
    [IsScalarTower K (MvPolynomial σ K ⧸ I) F] :
    IntermediateField.adjoin K (Set.range fun i : σ =>
      algebraMap (MvPolynomial σ K ⧸ I) F (Ideal.Quotient.mk I (MvPolynomial.X i))) = ⊤ := by
  let φ : MvPolynomial σ K →ₐ[K] F :=
    (IsScalarTower.toAlgHom K (MvPolynomial σ K ⧸ I) F).comp (Ideal.Quotient.mkₐ K I)
  apply field_adjoin_polynomial_coordinates_eq_top (φ := φ)
  intro z
  obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ K ⧸ I) z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨p, q, hab.symm⟩

end FD56
