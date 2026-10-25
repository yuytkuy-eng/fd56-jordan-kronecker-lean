/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PrincipalKernelCoordinates
import FD56.LinearAlgebra.QuotientFieldGenerators
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! Coordinates in the fraction field of a principal polynomial quotient. -/

noncomputable section
namespace FD56

variable {K σ : Type*} [Field K]

abbrev PrincipalQuotientField (g : MvPolynomial σ K) :=
  FractionRing (MvPolynomial σ K ⧸ Ideal.span ({g} : Set (MvPolynomial σ K)))

def principalQuotientFieldMap (g : MvPolynomial σ K) :
    MvPolynomial σ K →ₐ[K] PrincipalQuotientField g :=
  (IsScalarTower.toAlgHom K
    (MvPolynomial σ K ⧸ Ideal.span ({g} : Set (MvPolynomial σ K)))
    (PrincipalQuotientField g)).comp (Ideal.Quotient.mkₐ K (Ideal.span {g}))

theorem principalQuotientFieldMap_eq_zero_iff (g p : MvPolynomial σ K) :
    principalQuotientFieldMap g p = 0 ↔ g ∣ p := by
  change algebraMap (MvPolynomial σ K ⧸ Ideal.span ({g} : Set (MvPolynomial σ K)))
    (PrincipalQuotientField g) (Ideal.Quotient.mk (Ideal.span {g}) p) = 0 ↔ g ∣ p
  rw [map_eq_zero_iff _ (IsFractionRing.injective _ _),
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

theorem principal_quotient_field_coordinates_generate (g : MvPolynomial σ K)
    [(Ideal.span ({g} : Set (MvPolynomial σ K))).IsPrime] :
    IntermediateField.adjoin K
      (Set.range fun i : σ => principalQuotientFieldMap g (MvPolynomial.X i)) = ⊤ := by
  exact quotient_fraction_field_coordinates_generate
    (F := PrincipalQuotientField g) (Ideal.span {g})

theorem principal_quotient_field_remaining_coordinates_independent
    (g : MvPolynomial σ K) [(Ideal.span ({g} : Set (MvPolynomial σ K))).IsPrime]
    (hg : g ≠ 0) (hu : ¬IsUnit g) :
    ∃ i : σ, AlgebraicIndependent K (fun j : {j : σ // j ≠ i} =>
      principalQuotientFieldMap g (MvPolynomial.X j.val)) := by
  exact exists_remaining_coordinates_independent_of_principal_kernel
    (principalQuotientFieldMap g) g hg hu (principalQuotientFieldMap_eq_zero_iff g)

theorem principal_quotient_field_generator_lower_bound
    [Fintype σ] {ι : Type*} [Fintype ι]
    (g : MvPolynomial σ K) [(Ideal.span ({g} : Set (MvPolynomial σ K))).IsPrime]
    (hg : g ≠ 0) (hu : ¬IsUnit g) (y : ι → PrincipalQuotientField g)
    (hy : IntermediateField.adjoin K (Set.range y) = ⊤) :
    Fintype.card σ - 1 ≤ Fintype.card ι := by
  exact card_sub_one_le_card_of_principal_kernel_field_generators
    (principalQuotientFieldMap g) g hg hu (principalQuotientFieldMap_eq_zero_iff g) y hy

end FD56
