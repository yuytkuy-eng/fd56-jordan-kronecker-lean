/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.TwoColumnPluckerDominance
import FD56.LinearAlgebra.FiveOutputPluckerTangent
import FD56.LinearAlgebra.SelectedPolynomialCoefficients
import Mathlib.Algebra.Polynomial.Lifts

/-! Selected tangent coefficient ranks transfer through faithful evaluation
of the universal minor coefficient algebra. -/

noncomputable section
namespace FD56
open Matrix Polynomial

private abbrev MinorAlgebra (K : Type*) [Field K] (a b : ℕ) :=
  twoColumnMinorCoefficientAlgebra K
    (twoColumnUniversalU K (Fin 5) a b) (twoColumnUniversalV K (Fin 5) a b)

private theorem exists_minor_lift (K : Type*) [Field K] (a b : ℕ) (i j : Fin 5) :
    ∃ p : (MinorAlgebra K a b)[X],
      p.map (MinorAlgebra K a b).val.toRingHom =
        twoColumnUniversalU K (Fin 5) a b i*twoColumnUniversalV K (Fin 5) a b j-
        twoColumnUniversalU K (Fin 5) a b j*twoColumnUniversalV K (Fin 5) a b i := by
  apply (Polynomial.mem_lifts _).mp
  apply (Polynomial.lifts_iff_coeff_lifts _).mpr
  intro k
  refine ⟨⟨_,Algebra.subset_adjoin (Set.mem_range_self (i,j,k))⟩,rfl⟩

private def universalMinorLift (K : Type*) [Field K] (a b : ℕ) :
    Matrix (Fin 5) (Fin 5) (MinorAlgebra K a b)[X] :=
  fun i j => (exists_minor_lift K a b i j).choose

private theorem universalMinorLift_map (K : Type*) [Field K] (a b : ℕ) (i j : Fin 5) :
    (universalMinorLift K a b i j).map (MinorAlgebra K a b).val.toRingHom =
      twoColumnUniversalU K (Fin 5) a b i*twoColumnUniversalV K (Fin 5) a b j-
      twoColumnUniversalU K (Fin 5) a b j*twoColumnUniversalV K (Fin 5) a b i :=
  (exists_minor_lift K a b i j).choose_spec

private theorem universalMinorLift_evaluate {K L : Type*}
    [Field K] [Field L] [Algebra K L] (a b : ℕ) (u v : Fin 5 → L[X])
    (hu : ∀ i, (u i).natDegree≤a) (hv : ∀ i, (v i).natDegree≤b) (i j : Fin 5) :
    (universalMinorLift K a b i j).map
      (twoColumnMinorSpecialization a b (twoColumnCoefficientEvaluation (K:=K) a b u v)).toRingHom =
      u i*v j-u j*v i := by
  change (universalMinorLift K a b i j).map
    ((twoColumnCoefficientEvaluation (K:=K) a b u v).toRingHom.comp
      (MinorAlgebra K a b).val.toRingHom)=_
  rw [← Polynomial.map_map,universalMinorLift_map,
    twoColumnCoefficientEvaluation_minor a b u v hu hv]

private theorem tangent_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (F : Matrix (Fin 5) (Fin 5) R[X]) (i : Fin 5) (j : Fin 10) :
    (fiveOutputPluckerTangent F i j).map φ =
      fiveOutputPluckerTangent (fun k l => (F k l).map φ) i j := by
  fin_cases i <;> fin_cases j <;> simp [fiveOutputPluckerTangent]

private def universalTangentCoefficients (K : Type*) [Field K]
    (a b d : ℕ) {t : Type*} (rows : t → Fin 5 × ℕ) :
    Matrix t (Fin 10 × Fin (d+1)) (MinorAlgebra K a b) := fun i jk =>
  (fiveOutputPluckerTangent (universalMinorLift K a b) (rows i).1 jk.1*X^jk.2.val).coeff (rows i).2

private theorem universalTangentCoefficients_evaluate {K L t : Type*}
    [Field K] [Field L] [Algebra K L] (a b d : ℕ) (rows : t → Fin 5 × ℕ)
    (u v : Fin 5 → L[X]) (hu : ∀ i, (u i).natDegree≤a) (hv : ∀ i, (v i).natDegree≤b) :
    (universalTangentCoefficients K a b d rows).map
      (twoColumnMinorSpecialization a b (twoColumnCoefficientEvaluation (K:=K) a b u v)) =
      selectedPolynomialCoefficientMatrix (fiveOutputPluckerTangent (twoColumnWedge u v)) d rows := by
  funext i jk
  change (twoColumnMinorSpecialization a b (twoColumnCoefficientEvaluation (K:=K) a b u v))
    ((fiveOutputPluckerTangent (universalMinorLift K a b) (rows i).1 jk.1*X^jk.2.val).coeff (rows i).2)=_
  change (twoColumnMinorSpecialization a b (twoColumnCoefficientEvaluation (K:=K) a b u v)).toRingHom
    ((fiveOutputPluckerTangent (universalMinorLift K a b) (rows i).1 jk.1*X^jk.2.val).coeff (rows i).2)=_
  rw [← Polynomial.coeff_map,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X,tangent_map]
  have he : (fun k l => (universalMinorLift K a b k l).map
      (twoColumnMinorSpecialization a b (twoColumnCoefficientEvaluation (K:=K) a b u v)).toRingHom)=
      twoColumnWedge u v := funext (fun k => funext (fun l =>
        universalMinorLift_evaluate a b u v hu hv k l))
  rw [he]
  rfl

theorem five_output_tangent_coefficients_injective_of_faithful
    {K L t : Type*} [Field K] [Field L] [Algebra K L] [Fintype t]
    (a b d : ℕ) (rows : t → Fin 5 × ℕ)
    (u v : Fin 5 → L[X]) (hu : ∀ i, (u i).natDegree≤a) (hv : ∀ i, (v i).natDegree≤b)
    (hfaithful : Function.Injective (twoColumnMinorSpecialization a b
      (twoColumnCoefficientEvaluation (K:=K) a b u v)))
    (u₀ v₀ : Fin 5 → K[X]) (hu₀ : ∀ i, (u₀ i).natDegree≤a) (hv₀ : ∀ i, (v₀ i).natDegree≤b)
    (hcertificate : Function.Injective
      (selectedPolynomialCoefficientMatrix (fiveOutputPluckerTangent (twoColumnWedge u₀ v₀)) d rows).mulVec) :
    Function.Injective
      (selectedPolynomialCoefficientMatrix (fiveOutputPluckerTangent (twoColumnWedge u v)) d rows).mulVec := by
  classical
  let ψ := twoColumnMinorSpecialization a b (twoColumnCoefficientEvaluation (K:=K) a b u₀ v₀)
  let φ := twoColumnMinorSpecialization a b (twoColumnCoefficientEvaluation (K:=K) a b u v)
  have hs : Function.Injective ((universalTangentCoefficients K a b d rows).map ψ.toRingHom).mulVec := by
    change Function.Injective ((universalTangentCoefficients K a b d rows).map
      (twoColumnMinorSpecialization a b (twoColumnCoefficientEvaluation (K:=K) a b u₀ v₀))).mulVec
    rw [universalTangentCoefficients_evaluate a b d rows u₀ v₀ hu₀ hv₀]
    exact hcertificate
  have h := matrix_injective_of_field_specialization ψ.toRingHom φ.toRingHom hfaithful
    (universalTangentCoefficients K a b d rows) hs
  change Function.Injective ((universalTangentCoefficients K a b d rows).map
    (twoColumnMinorSpecialization a b (twoColumnCoefficientEvaluation (K:=K) a b u v))).mulVec at h
  rw [universalTangentCoefficients_evaluate a b d rows u v hu hv] at h
  exact h

end FD56
