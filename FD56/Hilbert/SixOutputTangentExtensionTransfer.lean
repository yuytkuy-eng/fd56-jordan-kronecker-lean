/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.TwoColumnPluckerDominance
import FD56.LinearAlgebra.SixOutputPluckerTangent
import FD56.LinearAlgebra.SelectedPolynomialCoefficients
import Mathlib.Algebra.Polynomial.Lifts
import FD56.Hilbert.FullPolynomialCoefficientDimension

/-! Witnesses over arbitrary extension fields bound the actual tangent kernel
through faithful evaluation of the universal minor coefficient algebra. -/

noncomputable section
namespace FD56
open Matrix Polynomial

private abbrev MinorAlgebra (K : Type*) [Field K] (a b : ℕ) :=
  twoColumnMinorCoefficientAlgebra K
    (twoColumnUniversalU K (Fin 6) a b) (twoColumnUniversalV K (Fin 6) a b)

private theorem exists_minor_lift (K : Type*) [Field K] (a b : ℕ) (i j : Fin 6) :
    ∃ p : (MinorAlgebra K a b)[X],
      p.map (MinorAlgebra K a b).val.toRingHom =
        twoColumnUniversalU K (Fin 6) a b i*twoColumnUniversalV K (Fin 6) a b j-
        twoColumnUniversalU K (Fin 6) a b j*twoColumnUniversalV K (Fin 6) a b i := by
  apply (Polynomial.mem_lifts _).mp
  apply (Polynomial.lifts_iff_coeff_lifts _).mpr
  intro k
  refine ⟨⟨_,Algebra.subset_adjoin (Set.mem_range_self (i,j,k))⟩,rfl⟩

private def universalMinorLift (K : Type*) [Field K] (a b : ℕ) :
    Matrix (Fin 6) (Fin 6) (MinorAlgebra K a b)[X] :=
  fun i j => (exists_minor_lift K a b i j).choose

private theorem universalMinorLift_map (K : Type*) [Field K] (a b : ℕ) (i j : Fin 6) :
    (universalMinorLift K a b i j).map (MinorAlgebra K a b).val.toRingHom =
      twoColumnUniversalU K (Fin 6) a b i*twoColumnUniversalV K (Fin 6) a b j-
      twoColumnUniversalU K (Fin 6) a b j*twoColumnUniversalV K (Fin 6) a b i :=
  (exists_minor_lift K a b i j).choose_spec

private theorem universalMinorLift_evaluate {K L : Type*}
    [Field K] [Field L] [Algebra K L] (a b : ℕ) (u v : Fin 6 → L[X])
    (hu : ∀ i, (u i).natDegree≤a) (hv : ∀ i, (v i).natDegree≤b) (i j : Fin 6) :
    (universalMinorLift K a b i j).map
      (twoColumnMinorSpecialization a b (twoColumnCoefficientEvaluation (K:=K) a b u v)).toRingHom =
      u i*v j-u j*v i := by
  change (universalMinorLift K a b i j).map
    ((twoColumnCoefficientEvaluation (K:=K) a b u v).toRingHom.comp
      (MinorAlgebra K a b).val.toRingHom)=_
  rw [← Polynomial.map_map,universalMinorLift_map,
    twoColumnCoefficientEvaluation_minor a b u v hu hv]

private theorem tangent_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (F : Matrix (Fin 6) (Fin 6) R[X]) (i : Fin 15) (j : Fin 15) :
    (sixOutputPluckerTangent F i j).map φ =
      sixOutputPluckerTangent (fun k l => (F k l).map φ) i j := by
  exact (congrFun (congrFun
    (sixOutputPluckerTangent_map (Polynomial.mapRingHom φ) F) i) j).symm

private def universalTangentCoefficients (K : Type*) [Field K]
    (a b d : ℕ) {t : Type*} (rows : t → Fin 15 × ℕ) :
    Matrix t (Fin 15 × Fin (d+1)) (MinorAlgebra K a b) := fun i jk =>
  (sixOutputPluckerTangent (universalMinorLift K a b) (rows i).1 jk.1*X^jk.2.val).coeff (rows i).2

private theorem universalTangentCoefficients_evaluate {K L t : Type*}
    [Field K] [Field L] [Algebra K L] (a b d : ℕ) (rows : t → Fin 15 × ℕ)
    (u v : Fin 6 → L[X]) (hu : ∀ i, (u i).natDegree≤a) (hv : ∀ i, (v i).natDegree≤b) :
    (universalTangentCoefficients K a b d rows).map
      (twoColumnMinorSpecialization a b (twoColumnCoefficientEvaluation (K:=K) a b u v)) =
      selectedPolynomialCoefficientMatrix (sixOutputPluckerTangent (twoColumnWedge u v)) d rows := by
  funext i jk
  change (twoColumnMinorSpecialization a b (twoColumnCoefficientEvaluation (K:=K) a b u v))
    ((sixOutputPluckerTangent (universalMinorLift K a b) (rows i).1 jk.1*X^jk.2.val).coeff (rows i).2)=_
  change (twoColumnMinorSpecialization a b (twoColumnCoefficientEvaluation (K:=K) a b u v)).toRingHom
    ((sixOutputPluckerTangent (universalMinorLift K a b) (rows i).1 jk.1*X^jk.2.val).coeff (rows i).2)=_
  rw [← Polynomial.coeff_map,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X,tangent_map]
  have he : (fun k l => (universalMinorLift K a b k l).map
      (twoColumnMinorSpecialization a b (twoColumnCoefficientEvaluation (K:=K) a b u v)).toRingHom)=
      twoColumnWedge u v := funext (fun k => funext (fun l =>
        universalMinorLift_evaluate a b u v hu hv k l))
  rw [he]
  rfl


theorem six_output_tangent_coefficients_injective_of_faithful_extension
    {K L E t : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Fintype t]
    (a b d : ℕ) (rows : t → Fin 15 × ℕ)
    (u v : Fin 6 → L[X]) (hu : ∀ i, (u i).natDegree≤a) (hv : ∀ i, (v i).natDegree≤b)
    (hfaithful : Function.Injective (twoColumnMinorSpecialization a b
      (twoColumnCoefficientEvaluation (K:=K) a b u v)))
    (u₀ v₀ : Fin 6 → E[X]) (hu₀ : ∀ i, (u₀ i).natDegree≤a) (hv₀ : ∀ i, (v₀ i).natDegree≤b)
    (hcertificate : Function.Injective
      (selectedPolynomialCoefficientMatrix (sixOutputPluckerTangent (twoColumnWedge u₀ v₀)) d rows).mulVec) :
    Function.Injective
      (selectedPolynomialCoefficientMatrix (sixOutputPluckerTangent (twoColumnWedge u v)) d rows).mulVec := by
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

theorem six_output_tangent_coefficient_nullity_le_of_faithful_extension
    {K L E t : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Fintype t]
    (a b d : ℕ) (rows : t → Fin 15 × ℕ)
    (u v : Fin 6 → L[X]) (hu : ∀ i, (u i).natDegree≤a) (hv : ∀ i, (v i).natDegree≤b)
    (hfaithful : Function.Injective (twoColumnMinorSpecialization a b
      (twoColumnCoefficientEvaluation (K:=K) a b u v)))
    (u₀ v₀ : Fin 6 → E[X]) (hu₀ : ∀ i, (u₀ i).natDegree≤a) (hv₀ : ∀ i, (v₀ i).natDegree≤b) :
    Module.finrank L (LinearMap.ker (Matrix.toLin'
      (selectedPolynomialCoefficientMatrix (sixOutputPluckerTangent (twoColumnWedge u v)) d rows))) ≤
      Module.finrank E (LinearMap.ker (Matrix.toLin'
        (selectedPolynomialCoefficientMatrix (sixOutputPluckerTangent (twoColumnWedge u₀ v₀)) d rows))) := by
  classical
  let ψ := twoColumnMinorSpecialization a b (twoColumnCoefficientEvaluation (K:=K) a b u₀ v₀)
  let φ := twoColumnMinorSpecialization a b (twoColumnCoefficientEvaluation (K:=K) a b u v)
  have h := matrix_kernel_finrank_le_of_field_specialization ψ.toRingHom φ.toRingHom hfaithful
    (universalTangentCoefficients K a b d rows)
  change Module.finrank L (LinearMap.ker (Matrix.toLin'
    ((universalTangentCoefficients K a b d rows).map
      (twoColumnMinorSpecialization a b (twoColumnCoefficientEvaluation (K:=K) a b u v))))) ≤
    Module.finrank E (LinearMap.ker (Matrix.toLin'
    ((universalTangentCoefficients K a b d rows).map
      (twoColumnMinorSpecialization a b (twoColumnCoefficientEvaluation (K:=K) a b u₀ v₀))))) at h
  rw [universalTangentCoefficients_evaluate a b d rows u v hu hv,
      universalTangentCoefficients_evaluate a b d rows u₀ v₀ hu₀ hv₀] at h
  exact h

private theorem tangent_degree {F : Type*} [Field F]
    (a b : ℕ) (u v : Fin 6 → F[X])
    (hu : ∀ i, (u i).natDegree≤a) (hv : ∀ i, (v i).natDegree≤b) :
    DegreeBound (sixOutputPluckerTangent (twoColumnWedge u v)) (a+b) := by
  have hF (i j : Fin 6) : (twoColumnWedge u v i j).natDegree≤a+b := by
    change (u i*v j-u j*v i).natDegree≤a+b
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · exact (Polynomial.natDegree_mul_le).trans (Nat.add_le_add (hu i) (hv j))
    · exact (Polynomial.natDegree_mul_le).trans (Nat.add_le_add (hu j) (hv i))
  intro i j
  dsimp only [sixOutputPluckerTangent]
  split_ifs <;> simp [hF]

theorem six_output_tangent_kernel_finrank_le_of_faithful_extension
    {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E]
    (a b d : ℕ)
    (u v : Fin 6 → L[X]) (hu : ∀ i, (u i).natDegree≤a) (hv : ∀ i, (v i).natDegree≤b)
    (hfaithful : Function.Injective (twoColumnMinorSpecialization a b
      (twoColumnCoefficientEvaluation (K:=K) a b u v)))
    (u₀ v₀ : Fin 6 → E[X]) (hu₀ : ∀ i, (u₀ i).natDegree≤a) (hv₀ : ∀ i, (v₀ i).natDegree≤b) :
    Module.finrank L (polynomialKernelAtDegree
      (sixOutputPluckerTangent (twoColumnWedge u v)) d) ≤
      Module.finrank E (polynomialKernelAtDegree
        (sixOutputPluckerTangent (twoColumnWedge u₀ v₀)) d) := by
  classical
  rw [← full_selected_coefficient_kernel_finrank _ (a+b) d (tangent_degree a b u v hu hv),
      ← full_selected_coefficient_kernel_finrank _ (a+b) d (tangent_degree a b u₀ v₀ hu₀ hv₀)]
  exact six_output_tangent_coefficient_nullity_le_of_faithful_extension
    a b d (fun ik : Fin 15 × Fin (a+b+d+1) => (ik.1,ik.2.val))
    u v hu hv hfaithful u₀ v₀ hu₀ hv₀

end FD56
