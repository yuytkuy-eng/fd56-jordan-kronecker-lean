/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.ThreeColumnPluckerDominance
import FD56.LinearAlgebra.SixOutputTriplePluckerTangent
import FD56.LinearAlgebra.SelectedPolynomialCoefficients
import Mathlib.Algebra.Polynomial.Lifts
import FD56.Hilbert.FullPolynomialCoefficientDimension

/-! Faithful evaluation transfers extension-valued three-column tangent
coefficient bounds to actual minors. No map from characteristic zero to a
finite field is used. -/

noncomputable section
namespace FD56
open Matrix Polynomial

private abbrev TripleAlgebra (K : Type*) [Field K] (h : ℕ) :=
  threeColumnMinorCoefficientAlgebra K (threeColumnUniversalFrame K (Fin 6) h)

private theorem exists_triple_lift (K : Type*) [Field K] (h : ℕ) (i : Fin 20) :
    ∃ p : (TripleAlgebra K h)[X],
      p.map (TripleAlgebra K h).val.toRingHom=
        pluckerMinorVector (threeColumnUniversalFrame K (Fin 6) h) (sixOutputTriple i) := by
  apply (Polynomial.mem_lifts _).mp
  apply (Polynomial.lifts_iff_coeff_lifts _).mpr
  intro k
  refine ⟨⟨_,Algebra.subset_adjoin (Set.mem_range_self (sixOutputTriple i,k))⟩,rfl⟩

private def universalTripleLift (K : Type*) [Field K] (h : ℕ) :
    Fin 20 → (TripleAlgebra K h)[X] :=
  fun i => (exists_triple_lift K h i).choose

private theorem universalTripleLift_evaluate {K L : Type*}
    [Field K] [Field L] [Algebra K L] (h : ℕ) (G : Matrix (Fin 6) (Fin 3) L[X])
    (hG : ∀ i j, (G i j).natDegree≤h) (i : Fin 20) :
    (universalTripleLift K h i).map
      (threeColumnMinorSpecialization h (threeColumnCoefficientEvaluation (K:=K) h G)).toRingHom=
      sixOutputTriplePluckerMinors G i := by
  change (universalTripleLift K h i).map
    ((threeColumnCoefficientEvaluation (K:=K) h G).toRingHom.comp
      (TripleAlgebra K h).val.toRingHom)=_
  rw [←Polynomial.map_map]
  have hlift : (universalTripleLift K h i).map (TripleAlgebra K h).val.toRingHom=
      pluckerMinorVector (threeColumnUniversalFrame K (Fin 6) h) (sixOutputTriple i) :=
    (exists_triple_lift K h i).choose_spec
  rw [hlift]
  exact threeColumnCoefficientEvaluation_minor h G hG (sixOutputTriple i)

private theorem triple_tangent_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (p : Fin 20 → R[X]) (i j : Fin 20) :
    (sixOutputTriplePluckerTangent p i j).map φ=
      sixOutputTriplePluckerTangent (fun k => (p k).map φ) i j := by
  have hl (l : List (ℤ × (Fin 20 × Fin 20))) :
      ((l.map fun t => (t.1 : R[X])*((if j=t.2.1 then p t.2.2 else 0)+
        (if j=t.2.2 then p t.2.1 else 0))).sum).map φ=
      (l.map fun t => (t.1 : S[X])*((if j=t.2.1 then (p t.2.2).map φ else 0)+
        (if j=t.2.2 then (p t.2.1).map φ else 0))).sum := by
    induction l with
    | nil => simp
    | cons t l ih =>
      simp only [List.map_cons,List.sum_cons,Polynomial.map_add,ih]
      congr 1
      split_ifs <;> simp
  exact hl (sixOutputTriplePluckerTerms i)

private def universalTripleCoefficients (K : Type*) [Field K]
    (h d : ℕ) {t : Type*} (rows : t → Fin 20 × ℕ) :
    Matrix t (Fin 20 × Fin (d+1)) (TripleAlgebra K h) := fun i jk =>
  (sixOutputTriplePluckerTangent (universalTripleLift K h) (rows i).1 jk.1*X^jk.2.val).coeff (rows i).2

private theorem universalTripleCoefficients_evaluate {K L t : Type*}
    [Field K] [Field L] [Algebra K L] (h d : ℕ) (rows : t → Fin 20 × ℕ)
    (G : Matrix (Fin 6) (Fin 3) L[X]) (hG : ∀ i j, (G i j).natDegree≤h) :
    (universalTripleCoefficients K h d rows).map
      (threeColumnMinorSpecialization h (threeColumnCoefficientEvaluation (K:=K) h G))=
      selectedPolynomialCoefficientMatrix (sixOutputTriplePluckerTangent
        (sixOutputTriplePluckerMinors G)) d rows := by
  funext i jk
  change (threeColumnMinorSpecialization h (threeColumnCoefficientEvaluation (K:=K) h G)).toRingHom
    ((sixOutputTriplePluckerTangent (universalTripleLift K h) (rows i).1 jk.1*X^jk.2.val).coeff (rows i).2)=_
  rw [←Polynomial.coeff_map,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X,triple_tangent_map]
  have he : (fun k => (universalTripleLift K h k).map
      (threeColumnMinorSpecialization h (threeColumnCoefficientEvaluation (K:=K) h G)).toRingHom)=
      sixOutputTriplePluckerMinors G := funext (universalTripleLift_evaluate h G hG)
  rw [he]
  rfl

theorem six_output_triple_tangent_coefficient_nullity_le_of_faithful_extension
    {K L E t : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Fintype t]
    (h d : ℕ) (rows : t → Fin 20 × ℕ)
    (G : Matrix (Fin 6) (Fin 3) L[X]) (hG : ∀ i j, (G i j).natDegree≤h)
    (hfaithful : Function.Injective (threeColumnMinorSpecialization h
      (threeColumnCoefficientEvaluation (K:=K) h G)))
    (G₀ : Matrix (Fin 6) (Fin 3) E[X]) (hG₀ : ∀ i j, (G₀ i j).natDegree≤h) :
    Module.finrank L (LinearMap.ker (Matrix.toLin'
      (selectedPolynomialCoefficientMatrix (sixOutputTriplePluckerTangent
        (sixOutputTriplePluckerMinors G)) d rows))) ≤
      Module.finrank E (LinearMap.ker (Matrix.toLin'
        (selectedPolynomialCoefficientMatrix (sixOutputTriplePluckerTangent
          (sixOutputTriplePluckerMinors G₀)) d rows))) := by
  classical
  let ψ := threeColumnMinorSpecialization h (threeColumnCoefficientEvaluation (K:=K) h G₀)
  let φ := threeColumnMinorSpecialization h (threeColumnCoefficientEvaluation (K:=K) h G)
  have hbound := matrix_kernel_finrank_le_of_field_specialization ψ.toRingHom φ.toRingHom
    hfaithful (universalTripleCoefficients K h d rows)
  change Module.finrank L (LinearMap.ker (Matrix.toLin'
    ((universalTripleCoefficients K h d rows).map
      (threeColumnMinorSpecialization h (threeColumnCoefficientEvaluation (K:=K) h G))))) ≤
    Module.finrank E (LinearMap.ker (Matrix.toLin'
    ((universalTripleCoefficients K h d rows).map
      (threeColumnMinorSpecialization h (threeColumnCoefficientEvaluation (K:=K) h G₀))))) at hbound
  rw [universalTripleCoefficients_evaluate h d rows G hG,
    universalTripleCoefficients_evaluate h d rows G₀ hG₀] at hbound
  exact hbound

private theorem triple_tangent_degree {F : Type*} [Field F]
    (h : ℕ) (G : Matrix (Fin 6) (Fin 3) F[X])
    (hG : ∀ i j, (G i j).natDegree≤h) :
    DegreeBound (sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G)) (3*h) := by
  have hp (i : Fin 20) : (sixOutputTriplePluckerMinors G i).natDegree≤3*h :=
    three_column_minor_degree G h hG (sixOutputTriple i)
  intro i j
  have ht (t : ℤ × (Fin 20 × Fin 20)) :
      ((t.1 : F[X])*((if j=t.2.1 then sixOutputTriplePluckerMinors G t.2.2 else 0)+
        (if j=t.2.2 then sixOutputTriplePluckerMinors G t.2.1 else 0))).natDegree≤3*h := by
    apply Polynomial.natDegree_mul_le.trans
    simp only [Polynomial.natDegree_intCast,zero_add]
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le <;> split_ifs <;> simp [hp]
  have hl (l : List (ℤ × (Fin 20 × Fin 20))) :
      ((l.map fun t => (t.1 : F[X])*((if j=t.2.1 then sixOutputTriplePluckerMinors G t.2.2 else 0)+
        (if j=t.2.2 then sixOutputTriplePluckerMinors G t.2.1 else 0))).sum).natDegree≤3*h := by
    induction l with
    | nil => simp
    | cons t l ih =>
      simp only [List.map_cons,List.sum_cons]
      exact (Polynomial.natDegree_add_le _ _).trans (max_le (ht t) ih)
  exact hl (sixOutputTriplePluckerTerms i)

theorem six_output_triple_tangent_kernel_finrank_le_of_faithful_extension
    {K L E : Type*} [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]
    (h d : ℕ) (G : Matrix (Fin 6) (Fin 3) L[X]) (hG : ∀ i j, (G i j).natDegree≤h)
    (hfaithful : Function.Injective (threeColumnMinorSpecialization h
      (threeColumnCoefficientEvaluation (K:=K) h G)))
    (G₀ : Matrix (Fin 6) (Fin 3) E[X]) (hG₀ : ∀ i j, (G₀ i j).natDegree≤h) :
    Module.finrank L (polynomialKernelAtDegree
      (sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G)) d) ≤
      Module.finrank E (polynomialKernelAtDegree
        (sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G₀)) d) := by
  classical
  rw [←full_selected_coefficient_kernel_finrank _ (3*h) d (triple_tangent_degree h G hG),
    ←full_selected_coefficient_kernel_finrank _ (3*h) d (triple_tangent_degree h G₀ hG₀)]
  exact six_output_triple_tangent_coefficient_nullity_le_of_faithful_extension
    h d (fun ik : Fin 20 × Fin (3*h+d+1) => (ik.1,ik.2.val)) G hG hfaithful G₀ hG₀

end FD56
