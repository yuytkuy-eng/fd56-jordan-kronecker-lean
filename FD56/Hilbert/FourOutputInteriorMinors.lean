/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericInteriorDifferentialRank
import FD56.Hilbert.GenericObservabilityDegreeBudget
import FD56.Stabilizer.InteriorSelectedMinorFactorization

/-! Six terminal Plucker coordinates for the four-output interior range.
Their signed five-coordinate projection is the established independent
selected-minor family. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 1000000

def fourOutputPluckerRows : Fin 6 → Fin 2 → Fin 4 :=
  ![![0,1],![0,2],![0,3],![1,2],![1,3],![2,3]]

def fourOutputPluckerVector {R : Type*} [CommRing R]
    (G : Matrix (Fin 4) (Fin 2) R) : Fin 6 → R :=
  fun i => pluckerMinorVector G (fourOutputPluckerRows i)

theorem fourOutputPluckerVector_relation {R : Type*} [CommRing R]
    (G : Matrix (Fin 4) (Fin 2) R) :
    fourOutputPluckerVector G 0*fourOutputPluckerVector G 5-
      fourOutputPluckerVector G 1*fourOutputPluckerVector G 4+
      fourOutputPluckerVector G 2*fourOutputPluckerVector G 3=0 := by
  simp [fourOutputPluckerVector,pluckerMinorVector,Matrix.det_fin_two,
    fourOutputPluckerRows]
  ring

def fourOutputMinorProjection {R : Type*} [CommRing R] :
    (Fin 6 → R) →ₗ[R] (Option (Fin 2 × Fin 2) → R) where
  toFun F z := match z with
    | none => F 0
    | some ab => if ab.1=0 then (if ab.2=0 then -F 3 else -F 4)
      else if ab.2=0 then F 1 else F 2
  map_add' F H := by
    funext z
    cases z with
    | none => rfl
    | some ab =>
      dsimp only [Pi.add_apply]
      split_ifs <;> ring
  map_smul' c F := by
    funext z
    cases z with
    | none => rfl
    | some ab =>
      dsimp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
      split_ifs <;> ring

theorem fourOutputMinorProjection_plucker {R : Type*} [CommRing R]
    (G : Matrix (Fin 4) (Fin 2) R) :
    fourOutputMinorProjection (fourOutputPluckerVector G)=
      fun z => pluckerMinorVector G (interiorTerminalRow 2 2 z) := by
  funext z
  cases z with
  | none =>
    simp [fourOutputMinorProjection,fourOutputPluckerVector,pluckerMinorVector,
      interiorTerminalRow,fourOutputPluckerRows,Matrix.det_fin_two]
  | some ab =>
    rcases ab with ⟨a,b⟩
    fin_cases a <;> fin_cases b <;>
      simp [fourOutputMinorProjection,fourOutputPluckerVector,pluckerMinorVector,
        interiorTerminalRow,fourOutputPluckerRows,Matrix.det_fin_two] <;> ring

def fourOutputInteriorMinors {R : Type*} [CommRing R] (q : ℕ)
    (M : Matrix (Fin (4*q+2)) (Fin (4*q+2)) R)
    (P : Matrix (Fin 4) (Fin (4*q+2)) R) : Fin 6 → R :=
  fun i => ((Matrix.fromRows (observabilityMatrix M P q)
    ((P*M^q).submatrix (fourOutputPluckerRows i) id)).submatrix
      (interiorPrefixEquiv 2 2 q) id).det

theorem fourOutputInteriorMinors_common_scalar {K : Type*} [Field K] (q : ℕ)
    (M : Matrix (Fin (4*q+2)) (Fin (4*q+2)) K[X])
    (P : Matrix (Fin 4) (Fin (4*q+2)) K[X])
    (R : Matrix (Fin (4*q+2)) (Fin q × Fin 4) K[X])
    (hR : observabilityMatrix M P q*R=1)
    (B : Basis (Fin 2) K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q)))) :
    ∃ c : K, c≠0 ∧ ∀ i,
      fourOutputInteriorMinors q M P i=C c*fourOutputPluckerVector
        (P*M^q*polynomialKernelBasisMatrix (observabilityMatrix M P q) B) i := by
  obtain ⟨c,hc,h⟩ := selected_augmented_minors_common_scalar_equiv
    (interiorPrefixEquiv 2 2 q) (observabilityMatrix M P q) R hR B (P*M^q)
  exact ⟨c,hc,fun i => h (fourOutputPluckerRows i)⟩

theorem fourOutputInteriorMinors_selected_projection {K : Type*} [Field K] (q : ℕ)
    (M : Matrix (Fin (4*q+2)) (Fin (4*q+2)) K[X])
    (P : Matrix (Fin 4) (Fin (4*q+2)) K[X])
    (R : Matrix (Fin (4*q+2)) (Fin q × Fin 4) K[X])
    (hR : observabilityMatrix M P q*R=1)
    (B : Basis (Fin 2) K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q)))) :
    fourOutputMinorProjection (fourOutputInteriorMinors q M P)=fun z =>
      (observabilitySelectedMatrix M P (interiorLevel 2 2 q)
        (interiorSelectorRow 2 2 q z)).det := by
  obtain ⟨c,_,h⟩ := selected_augmented_minors_common_scalar_equiv
    (interiorPrefixEquiv 2 2 q) (observabilityMatrix M P q) R hR B (P*M^q)
  let G := P*M^q*polynomialKernelBasisMatrix (observabilityMatrix M P q) B
  have h6 : fourOutputInteriorMinors q M P=C c • fourOutputPluckerVector G := by
    funext i
    exact h (fourOutputPluckerRows i)
  rw [h6,map_smul,fourOutputMinorProjection_plucker]
  funext z
  rw [interior_selected_matrix_fromRows 2 2 q M P z]
  exact (h (interiorTerminalRow 2 2 z)).symm

theorem fourOutputInteriorMinors_relation {K : Type*} [Field K] (q : ℕ)
    (M : Matrix (Fin (4*q+2)) (Fin (4*q+2)) K[X])
    (P : Matrix (Fin 4) (Fin (4*q+2)) K[X])
    (R : Matrix (Fin (4*q+2)) (Fin q × Fin 4) K[X])
    (hR : observabilityMatrix M P q*R=1)
    (B : Basis (Fin 2) K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q)))) :
    fourOutputInteriorMinors q M P 0*fourOutputInteriorMinors q M P 5-
      fourOutputInteriorMinors q M P 1*fourOutputInteriorMinors q M P 4+
      fourOutputInteriorMinors q M P 2*fourOutputInteriorMinors q M P 3=0 := by
  obtain ⟨c,_,hc⟩ := fourOutputInteriorMinors_common_scalar q M P R hR B
  simp_rw [hc]
  have h := fourOutputPluckerVector_relation
    (P*M^q*polynomialKernelBasisMatrix (observabilityMatrix M P q) B)
  linear_combination (C c)^2*h

variable {K : Type*} [Field K]

def genericFourOutputInteriorMinors (q : ℕ) : Fin 6 →
    (AffineCoefficientField K (MatrixParameters (Fin (4*q+2)) (Fin 4)))[X] :=
  fourOutputInteriorMinors q (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
    (genericAffineRows K (Fin (4*q+2)) (Fin 4))

private theorem generic_four_output_observability_basis (q : ℕ) :
    Nonempty (Basis (Fin 2)
      (AffineCoefficientField K (MatrixParameters (Fin (4*q+2)) (Fin 4)))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
        (genericAffineRows K (Fin (4*q+2)) (Fin 4)) q)))) := by
  let O := observabilityMatrix (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
    (genericAffineRows K (Fin (4*q+2)) (Fin 4)) q
  obtain ⟨k,B,a,hV,hVL,_,_⟩ := polynomial_kernel_has_minimal_basis O
  have hmin : HasMinimalKernelDegrees O (List.ofFn a) :=
    ⟨k,B,a,hV,hVL,List.Perm.refl _⟩
  have hk := (generic_observability_kernel_degree_budget (K:=K) q
    (by simp only [Fintype.card_fin]; omega) (List.ofFn a) hmin).1
  simp only [List.length_ofFn,Fintype.card_fin] at hk
  have h : k=2 := by omega
  subst k
  exact ⟨B⟩

theorem generic_four_output_minors_selected_projection (q : ℕ) :
    fourOutputMinorProjection (genericFourOutputInteriorMinors (K:=K) q)=
      genericInteriorMinorVector (K:=K) 2 2 q := by
  obtain ⟨B⟩ := generic_four_output_observability_basis (K:=K) q
  obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse
    (K:=K) (n:=Fin (4*q+2)) (m:=Fin 4) q
    (by simp only [Fintype.card_fin]; omega)
  exact fourOutputInteriorMinors_selected_projection q _ _ R hR B

theorem generic_four_output_minors_relation (q : ℕ) :
    genericFourOutputInteriorMinors (K:=K) q 0*genericFourOutputInteriorMinors (K:=K) q 5-
      genericFourOutputInteriorMinors (K:=K) q 1*genericFourOutputInteriorMinors (K:=K) q 4+
      genericFourOutputInteriorMinors (K:=K) q 2*genericFourOutputInteriorMinors (K:=K) q 3=0 := by
  obtain ⟨B⟩ := generic_four_output_observability_basis (K:=K) q
  obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse
    (K:=K) (n:=Fin (4*q+2)) (m:=Fin 4) q
    (by simp only [Fintype.card_fin]; omega)
  exact fourOutputInteriorMinors_relation q _ _ R hR B

private theorem fourOutputMinorProjection_derivation_image
    {L : Type*} [Field L] [Algebra K L] (F : Fin 6 → L[X]) :
    polynomialDerivationImageMap (K:=K) (fourOutputMinorProjection F)=
      ((fourOutputMinorProjection (R:=L[X])).restrictScalars L).comp
        (polynomialDerivationImageMap (K:=K) F) := by
  apply LinearMap.ext
  intro D
  funext z
  change polynomialCoefficientDerivation D (fourOutputMinorProjection F z)=
    fourOutputMinorProjection (fun i => polynomialCoefficientDerivation D (F i)) z
  cases z with
  | none => rfl
  | some ab =>
    simp only [fourOutputMinorProjection,LinearMap.coe_mk,AddHom.coe_mk]
    split_ifs <;> simp only [map_neg]

private theorem four_output_derivation_image_finite
    {L : Type*} [Field L] [Algebra K L] (F : Fin 6 → L[X]) :
    Module.Finite L (LinearMap.range (polynomialDerivationImageMap (K:=K) F)) := by
  let E : (∀ i, BoundedPoly L (F i).natDegree) →ₗ[L] (Fin 6 → L[X]) :=
    { toFun := fun z i => (z i).val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : LinearMap.range (polynomialDerivationImageMap (K:=K) F) ≤ LinearMap.range E := by
    rintro y ⟨D,rfl⟩
    refine ⟨fun i => boundedPolyOf (polynomialCoefficientDerivation D (F i))
      (polynomialCoefficientDerivation_natDegree_le D (F i)),rfl⟩
  exact Submodule.finiteDimensional_of_le hle

theorem generic_four_output_minors_derivation_rank_lower (q : ℕ) (hq : 0<q) :
    4*(2*(q+1)^2)+5 ≤
      Module.finrank (AffineCoefficientField K (MatrixParameters (Fin (4*q+2)) (Fin 4)))
        (LinearMap.range (polynomialDerivationImageMap (K:=K)
          (genericFourOutputInteriorMinors (K:=K) q))) := by
  let L := AffineCoefficientField K (MatrixParameters (Fin (4*q+2)) (Fin 4))
  let f := polynomialDerivationImageMap (K:=K) (genericFourOutputInteriorMinors (K:=K) q)
  let T := (fourOutputMinorProjection (R:=L[X])).restrictScalars L
  have he : polynomialDerivationImageMap (K:=K) (genericInteriorMinorVector (K:=K) 2 2 q)=
      T.comp f := by
    rw [← generic_four_output_minors_selected_projection (K:=K) q]
    exact fourOutputMinorProjection_derivation_image _
  letI : Module.Finite L (LinearMap.range f) := four_output_derivation_image_finite _
  have hdim := Submodule.finrank_map_le T (LinearMap.range f)
  rw [← LinearMap.range_comp,← he] at hdim
  have hlower := generic_interior_minor_derivation_rank_lower_of_weight
    (K:=K) 2 2 q hq (2*(q+1)^2) (by ring)
  simpa only [Nat.reduceAdd,Nat.reduceMul,Nat.add_assoc] using hlower.trans hdim

end FD56
