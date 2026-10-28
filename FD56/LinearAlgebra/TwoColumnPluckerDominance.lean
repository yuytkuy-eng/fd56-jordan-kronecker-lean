/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.TwoColumnPluckerTranscendence
import FD56.LinearAlgebra.TwoColumnUniversalSpecialization
import FD56.LinearAlgebra.PolynomialDerivationCoordinates

/-! Faithful specialization of the universal two-column minor coefficient
algebra from a sharp actual coefficient differential rank. -/

noncomputable section
namespace FD56
open Polynomial

variable {K L n ι : Type*} [Field K] [Field L] [Algebra K L]
  [CharZero K] [Fintype n] [Fintype ι]

def twoColumnMinorSpecialization (a b : ℕ)
    (φ : TwoColumnCoefficientRing K n a b →ₐ[K] L) :
    twoColumnMinorCoefficientAlgebra K
      (twoColumnUniversalU K n a b) (twoColumnUniversalV K n a b) →ₐ[K] L :=
  φ.comp (twoColumnMinorCoefficientAlgebra K
    (twoColumnUniversalU K n a b) (twoColumnUniversalV K n a b)).val

theorem two_column_minor_specialization_injective_of_derivation_rank
    (a b : ℕ) (hbalanced : b=a ∨ b=a+1) (i₀ i₁ : n) (hi : i₀≠i₁)
    (φ : TwoColumnCoefficientRing K n a b →ₐ[K] L) (row : ι → n × n)
    (hrank : Fintype.card n*(a+b+2)-3 ≤ Module.finrank L
      (LinearMap.range (polynomialDerivationImageMap (K:=K) (fun z =>
        ((twoColumnUniversalU K n a b (row z).1)*
          (twoColumnUniversalV K n a b (row z).2)-
          (twoColumnUniversalU K n a b (row z).2)*
          (twoColumnUniversalV K n a b (row z).1)).map φ.toRingHom)))) :
    Function.Injective (twoColumnMinorSpecialization a b φ) := by
  let U := twoColumnUniversalU K n a b
  let V := twoColumnUniversalV K n a b
  let A := twoColumnMinorCoefficientAlgebra K U V
  let p : ι → (TwoColumnCoefficientRing K n a b)[X] :=
    fun z => U (row z).1*V (row z).2-U (row z).2*V (row z).1
  let x : ι × Fin (a+b+1) → A := fun z =>
    ⟨(p z.1).coeff z.2,Algebra.subset_adjoin
      (show (p z.1).coeff z.2 ∈ Set.range
        (fun w : n × n × ℕ => (U w.1*V w.2.1-U w.2.1*V w.1).coeff w.2.2) from
        ⟨((row z.1).1,(row z.1).2,z.2.val),rfl⟩)⟩
  have hdegree : ∀ z, ((p z).map φ.toRingHom).natDegree ≤ a+b := by
    intro z
    apply natDegree_map_le.trans
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact natDegree_mul_le.trans (Nat.add_le_add
        (twoColumnUniversalU_degree K n a b _) (twoColumnUniversalV_degree K n a b _))
    · exact natDegree_mul_le.trans (Nat.add_le_add
        (twoColumnUniversalU_degree K n a b _) (twoColumnUniversalV_degree K n a b _))
  have htr : Algebra.trdeg K A ≤ (Fintype.card n*(a+b+2)-3 : ℕ) := by
    rcases hbalanced with he | he
    · subst b
      simpa only [two_mul] using two_column_universal_equal_trdeg K n a i₀ i₁ hi
    · subst b
      have he : a+(a+1)+2=2*a+3 := by omega
      simpa only [he] using two_column_universal_adjacent_trdeg K n a i₀ i₁ hi
  apply injective_of_derivation_rank_bound (twoColumnMinorSpecialization a b φ) x
  have he : (twoColumnMinorSpecialization a b φ) ∘ x =
      (fun z : ι × Fin (a+b+1) => ((p z.1).map φ.toRingHom).coeff z.2) := by
    funext z
    exact (Polynomial.coeff_map φ.toRingHom z.2).symm
  rw [he,← polynomial_derivation_finrank_eq_coefficient_finrank (a+b) _ hdegree]
  exact htr.trans (by exact_mod_cast hrank)

theorem two_column_coefficient_evaluation_faithful
    (a b : ℕ) (hbalanced : b=a ∨ b=a+1) (i₀ i₁ : n) (hi : i₀≠i₁)
    (u v : n → L[X]) (hu : ∀ i, (u i).natDegree≤a) (hv : ∀ i, (v i).natDegree≤b)
    (row : ι → n × n)
    (hrank : Fintype.card n*(a+b+2)-3 ≤ Module.finrank L
      (LinearMap.range (polynomialDerivationImageMap (K:=K)
        (fun z => u (row z).1*v (row z).2-u (row z).2*v (row z).1)))) :
    Function.Injective (twoColumnMinorSpecialization a b
      (twoColumnCoefficientEvaluation (K:=K) a b u v)) := by
  apply two_column_minor_specialization_injective_of_derivation_rank a b hbalanced i₀ i₁ hi
    (twoColumnCoefficientEvaluation (K:=K) a b u v) row
  have he : (fun z =>
      (twoColumnUniversalU K n a b (row z).1*twoColumnUniversalV K n a b (row z).2-
        twoColumnUniversalU K n a b (row z).2*twoColumnUniversalV K n a b (row z).1).map
          (twoColumnCoefficientEvaluation (K:=K) a b u v).toRingHom) =
      (fun z => u (row z).1*v (row z).2-u (row z).2*v (row z).1) :=
    funext (fun z => twoColumnCoefficientEvaluation_minor (K:=K) a b u v hu hv _ _)
  rw [he]
  exact hrank

end FD56
