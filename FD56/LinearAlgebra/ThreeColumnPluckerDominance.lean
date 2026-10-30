/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.ThreeColumnPluckerTranscendence
import FD56.LinearAlgebra.ThreeColumnUniversalSpecialization
import FD56.LinearAlgebra.PolynomialDerivationCoordinates
import FD56.LinearAlgebra.WeightedDeterminantDegree

/-! A sharp coefficient differential lower bound makes evaluation of the
equal-degree three-column minor coefficient algebra faithful. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false

theorem three_column_minor_degree {R n : Type*} [CommRing R]
    (G : Matrix n (Fin 3) R[X]) (h : ℕ)
    (hG : ∀ i j, (G i j).natDegree≤h) (row : Fin 3 → n) :
    (pluckerMinorVector G row).natDegree≤3*h := by
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using
    polynomial_det_natDegree_le_row_sum (G.submatrix row id) (fun _ => h)
      (fun i j => hG (row i) j)

variable {K L n ι : Type*} [Field K] [Field L] [Algebra K L]
  [CharZero K] [Fintype n] [Fintype ι]

def threeColumnMinorSpecialization (h : ℕ)
    (φ : ThreeColumnCoefficientRing K n h →ₐ[K] L) :
    threeColumnMinorCoefficientAlgebra K (threeColumnUniversalFrame K n h) →ₐ[K] L :=
  φ.comp (threeColumnMinorCoefficientAlgebra K (threeColumnUniversalFrame K n h)).val

theorem three_column_minor_specialization_injective_of_derivation_rank
    (h : ℕ) (pivot : Fin 3 ↪ n)
    (φ : ThreeColumnCoefficientRing K n h →ₐ[K] L) (row : ι → Fin 3 → n)
    (hrank : 3*Fintype.card n*(h+1)-8 ≤ Module.finrank L
      (LinearMap.range (polynomialDerivationImageMap (K:=K) (fun z =>
        (pluckerMinorVector (threeColumnUniversalFrame K n h) (row z)).map φ.toRingHom)))) :
    Function.Injective (threeColumnMinorSpecialization h φ) := by
  let U := threeColumnUniversalFrame K n h
  let A := threeColumnMinorCoefficientAlgebra K U
  let p : ι → (ThreeColumnCoefficientRing K n h)[X] := fun z => pluckerMinorVector U (row z)
  let x : ι × Fin (3*h+1) → A := fun z =>
    ⟨(p z.1).coeff z.2,Algebra.subset_adjoin (show (p z.1).coeff z.2 ∈ Set.range
      (fun w : (Fin 3 → n) × ℕ => (pluckerMinorVector U w.1).coeff w.2) from
      ⟨(row z.1,z.2.val),rfl⟩)⟩
  have hdegree : ∀ z, ((p z).map φ.toRingHom).natDegree≤3*h := by
    intro z
    exact natDegree_map_le.trans (three_column_minor_degree U h
      (threeColumnUniversalFrame_degree K n h) (row z))
  have htr : Algebra.trdeg K A≤(3*Fintype.card n*(h+1)-8 : ℕ) :=
    three_column_universal_equal_trdeg K n h pivot
  apply injective_of_derivation_rank_bound (threeColumnMinorSpecialization h φ) x
  have he : (threeColumnMinorSpecialization h φ) ∘ x=
      (fun z : ι × Fin (3*h+1) => ((p z.1).map φ.toRingHom).coeff z.2) := by
    funext z
    exact (Polynomial.coeff_map φ.toRingHom z.2).symm
  rw [he,← polynomial_derivation_finrank_eq_coefficient_finrank (3*h) _ hdegree]
  exact htr.trans (by exact_mod_cast hrank)

theorem three_column_coefficient_evaluation_faithful
    (h : ℕ) (pivot : Fin 3 ↪ n) (G : Matrix n (Fin 3) L[X])
    (hG : ∀ i j, (G i j).natDegree≤h) (row : ι → Fin 3 → n)
    (hrank : 3*Fintype.card n*(h+1)-8 ≤ Module.finrank L
      (LinearMap.range (polynomialDerivationImageMap (K:=K)
        (fun z => pluckerMinorVector G (row z))))) :
    Function.Injective (threeColumnMinorSpecialization h
      (threeColumnCoefficientEvaluation (K:=K) h G)) := by
  apply three_column_minor_specialization_injective_of_derivation_rank h pivot
    (threeColumnCoefficientEvaluation (K:=K) h G) row
  have he : (fun z => (pluckerMinorVector (threeColumnUniversalFrame K n h) (row z)).map
      (threeColumnCoefficientEvaluation (K:=K) h G).toRingHom)=
      (fun z => pluckerMinorVector G (row z)) :=
    funext (fun z => threeColumnCoefficientEvaluation_minor h G hG (row z))
  rw [he]
  exact hrank

end FD56
