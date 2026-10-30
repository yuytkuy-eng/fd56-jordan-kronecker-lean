/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.TwoColumnInteriorGradientBounds
import FD56.Hilbert.TwoColumnGradientAlternation
import FD56.Hilbert.GenericNondivisibleSLStructure
import FD56.LinearAlgebra.AffineKernelFrameRank
import FD56.LinearAlgebra.SixOutputSelectedFrameTranspose
import FD56.LinearAlgebra.MatrixFactorRelations
import FD56.Hilbert.ReducedFactorHilbertTests
import FD56.Hilbert.BalancedDegreeProfile

/-! The actual six-output, remainder-two SL kernel factors its Plucker
gradients through a reduced basis. Two explicit tangent Hilbert tests
then determine the complete balanced SL profile. These tests remain
premises; the module does not establish them at every depth. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 3000000

theorem six_output_two_column_weight (q : ℕ) :
    twoColumnInteriorWeight 4 q=3*q^2+5*q+2 := by
  have hn : 6*q*(q+1)+4*(q+1)=2*(3*q^2+5*q+2) := by ring
  unfold twoColumnInteriorWeight
  norm_num only [Nat.reduceAdd]
  rw [hn]
  omega

variable {K : Type*} [Field K]

private abbrev SixOutputField (q : ℕ) :=
  AffineCoefficientField K (MatrixParameters (Fin (6*q+2)) (Fin 6))

theorem generic_six_output_sl_tangent_factor (q : ℕ) (hq : 0<q)
    (i₀ : Fin (6*q+2)) :
    ∃ (B : Basis (Fin 9) (SixOutputField (K:=K) q)[X]
        (LinearMap.ker (Matrix.toLin' (slEquationMatrix
          (genericAffineSquare K (Fin (6*q+2)) (Fin 6))
          (genericAffineRows K (Fin (6*q+2)) (Fin 6)) i₀))))
      (e : Fin 9 → ℕ) (C : Matrix (Fin 9) (Fin 15) (SixOutputField (K:=K) q)[X]),
      (∀ i j, (polynomialKernelBasisMatrix _ B i j).natDegree≤e j) ∧
      Function.Injective (Matrix.mulVec
        (fun i j => (polynomialKernelBasisMatrix _ B i j).coeff (e j))) ∧
      polynomialKernelBasisMatrix _ B*C=
        (genericTwoColumnInteriorScalarGradients (K:=K) 4 q).submatrix id sixOutputPair ∧
      Function.Injective C.transpose.mulVec ∧
      DegreeBound (polynomialKernelBasisMatrix _ B*C) (twoColumnInteriorWeight 4 q-1) ∧
      sixOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 4 q)*C.transpose=0 ∧
      (∑ i, e i)+3*twoColumnInteriorWeight 4 q=9*(twoColumnInteriorWeight 4 q-1) := by
  classical
  let L := SixOutputField (K:=K) q
  let M := genericAffineSquare K (Fin (6*q+2)) (Fin 6)
  let P := genericAffineRows K (Fin (6*q+2)) (Fin 6)
  let S := slEquationMatrix M P i₀
  have hlo : q*Fintype.card (Fin 6)<Fintype.card (Fin (6*q+2)) := by
    simp only [Fintype.card_fin]; omega
  have hhi : Fintype.card (Fin (6*q+2))<(q+1)*Fintype.card (Fin 6) := by
    simp only [Fintype.card_fin]; omega
  obtain ⟨xs,hlen,hsum,hmin,_⟩ := generic_nondivisible_sl_kronecker_structure
    (K:=K) (n:=Fin (6*q+2)) (m:=Fin 6) q hq i₀ hlo hhi
  simp only [Fintype.card_fin] at hlen hsum
  have hlen9 : xs.length=9 := by
    have h₁ : 6*q+2-q*6=2 := by omega
    have h₂ : (q+1)*6-(6*q+2)=4 := by omega
    simpa only [h₁,h₂] using hlen
  obtain ⟨r,B,e,hV,hlead,hperm⟩ := hmin
  have hr : r=9 := by simpa only [List.length_ofFn,hlen9] using hperm.length_eq
  subst r
  have heSum : (∑ i, e i)+3*twoColumnInteriorWeight 4 q=9*(twoColumnInteriorWeight 4 q-1) := by
    have h := hperm.sum_eq
    rw [List.sum_ofFn] at h
    have hW := six_output_two_column_weight q
    have hWp := twoColumnInteriorWeight_pos 4 q
    have hsub := Nat.sub_add_cancel hWp
    rw [hlen9] at hsum
    nlinarith
  let V := polynomialKernelBasisMatrix S B
  let Z := genericTwoColumnInteriorScalarGradients (K:=K) 4 q
  let A := sixOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 4 q)
  have hVinj : Function.Injective V.mulVec := polynomialKernelBasisMatrix_injective S B
  obtain ⟨C,hVC⟩ := polynomialKernelFrame_factor S B Z
    (twoColumnInteriorScalarGradients_kernel 4 q M P i₀)
  change V*C=Z at hVC
  let select : Option (Fin 2 × Fin 4) → Fin 6 × Fin 6 :=
    fun z => (interiorTerminalRow 2 4 z 0,interiorTerminalRow 2 4 z 1)
  let φ : L[X] →+* RatFunc L := algebraMap L[X] (RatFunc L)
  have hφ : Function.Injective φ := IsFractionRing.injective L[X] (RatFunc L)
  have hCinj : Function.Injective C.transpose.mulVec := by
    apply factor_transpose_injective_of_selected_field_frame V C φ hφ select (by decide)
    rw [hVC]
    change Function.Injective (((twoColumnInteriorScalarGradients 4 q M P).submatrix id
      (fun z => (interiorTerminalRow 2 4 z 0,interiorTerminalRow 2 4 z 1))).map φ).mulVec
    rw [twoColumnInteriorScalarGradients_selected]
    exact generic_interior_scalar_lifts_field_injective 2 4 q φ hφ
  have hCalt := factor_columns_alternating V C hVinj
    (by
      intro t i
      rw [hVC]
      exact (generic_two_column_gradients_alternating (K:=K) 4 q t).1 i)
    (by
      intro t i j
      rw [hVC]
      exact (generic_two_column_gradients_alternating (K:=K) 4 q t).2 i j)
  let C₁ := C.submatrix id sixOutputPair
  have hC₁ : Function.Injective C₁.transpose.mulVec :=
    sixOutput_transpose_upper_pairs_injective C hCinj hCalt.1 hCalt.2
  have hVC₁ : V*C₁=Z.submatrix id sixOutputPair := by rw [←hVC]; rfl
  have hVCdegree : DegreeBound (V*C₁) (twoColumnInteriorWeight 4 q-1) := by
    rw [hVC₁]
    intro i j
    exact generic_two_column_scalar_gradients_degree (K:=K) 4 q i (sixOutputPair j)
  have hAZ : A*(V*C₁).transpose=0 := by
    rw [hVC₁]
    funext i t
    change (sixOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 4 q)*ᵥ
      (fun j => genericTwoColumnInteriorScalarGradients (K:=K) 4 q t (sixOutputPair j))) i=0
    rw [sixOutputPluckerTangent_mulVec _
      (fun a b => genericTwoColumnInteriorScalarGradients (K:=K) 4 q t (a,b))]
    exact generic_two_column_gradient_plucker_relation (K:=K) 4 q t
      (sixOutputQuad i 0) (sixOutputQuad i 1) (sixOutputQuad i 2) (sixOutputQuad i 3)
  exact ⟨B,e,C₁,hV,hlead,hVC₁,hC₁,hVCdegree,
    factor_transpose_kernel_of_product V C₁ A hVinj hAZ,heSum⟩

theorem generic_six_output_sl_degrees_of_tangent_tests (q : ℕ) (hq : 0<q)
    (i₀ : Fin (6*q+2))
    (hzero : Module.finrank (SixOutputField (K:=K) q)
      (polynomialKernelAtDegree
        (sixOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 4 q))
        (3*twoColumnInteriorWeight 4 q/9-1))=0)
    (hcritical : Module.finrank (SixOutputField (K:=K) q)
      (polynomialKernelAtDegree
        (sixOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 4 q))
        (3*twoColumnInteriorWeight 4 q/9))≤9-(3*twoColumnInteriorWeight 4 q)%9) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (6*q+2)) (Fin 6))
      (genericAffineRows K (Fin (6*q+2)) (Fin 6)) i₀)
      (balancedDegreeList (9*(twoColumnInteriorWeight 4 q-1)-3*twoColumnInteriorWeight 4 q) 9) := by
  obtain ⟨B,e,C,hV,hlead,_,hC,hVC,hAC,hsum⟩ :=
    generic_six_output_sl_tangent_factor (K:=K) q hq i₀
  have hk : 0<3*twoColumnInteriorWeight 4 q/9 := by
    have hW := six_output_two_column_weight q
    have hlarge : 30≤3*twoColumnInteriorWeight 4 q := by nlinarith
    omega
  have hbalance := reduced_factor_balanced_of_two_kernel_tests
    (polynomialKernelBasisMatrix _ B) C e (twoColumnInteriorWeight 4 q-1)
    (3*twoColumnInteriorWeight 4 q/9) ((3*twoColumnInteriorWeight 4 q)%9)
    hV hlead hC hVC _ hAC hk
    (by simp only [Fintype.card_fin]; omega)
    (by
      simp only [Fintype.card_fin]
      have hdiv := Nat.mod_add_div (3*twoColumnInteriorWeight 4 q) 9
      omega)
    hzero hcritical
  have hesum : (∑ i, e i)=9*(twoColumnInteriorWeight 4 q-1)-3*twoColumnInteriorWeight 4 q := by
    omega
  rw [←hesum]
  exact reduced_kernel_basis_balanced_minimal_degrees _ (by decide) B e hV hlead hbalance

theorem generic_six_output_sl_classification_of_tangent_tests (q : ℕ) (hq : 0<q)
    (i₀ : Fin (6*q+2))
    (hzero : Module.finrank (SixOutputField (K:=K) q)
      (polynomialKernelAtDegree
        (sixOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 4 q))
        (3*twoColumnInteriorWeight 4 q/9-1))=0)
    (hcritical : Module.finrank (SixOutputField (K:=K) q)
      (polynomialKernelAtDegree
        (sixOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 4 q))
        (3*twoColumnInteriorWeight 4 q/9))≤9-(3*twoColumnInteriorWeight 4 q)%9) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (6*q+2)) (Fin 6))
      (genericAffineRows K (Fin (6*q+2)) (Fin 6)) i₀)
      (balancedDegreeList (9*(twoColumnInteriorWeight 4 q-1)-3*twoColumnInteriorWeight 4 q) 9) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (6*q+2)) (Fin 6))
      (genericAffineRows K (Fin (6*q+2)) (Fin 6)) i₀)
      (balancedDegreeList (9*(twoColumnInteriorWeight 4 q-1)-3*twoColumnInteriorWeight 4 q) 9) := by
  let ys := balancedDegreeList
    (9*(twoColumnInteriorWeight 4 q-1)-3*twoColumnInteriorWeight 4 q) 9
  have hmin := generic_six_output_sl_degrees_of_tangent_tests (K:=K) q hq i₀ hzero hcritical
  refine ⟨hmin,?_⟩
  obtain ⟨xs,_,_,hxs,hcanon⟩ := generic_nondivisible_sl_kronecker_structure
    (K:=K) (n:=Fin (6*q+2)) (m:=Fin 6) q hq i₀
    (by simp only [Fintype.card_fin]; omega) (by simp only [Fintype.card_fin]; omega)
  have hp : xs.Perm ys := by
    apply listHilbert_determines_indices
    intro d
    rw [listHilbert_nat,listHilbert_nat]
    exact_mod_cast ((hasMinimalKernelDegrees_iff_hilbert _ xs).mp hxs d).symm.trans
      ((hasMinimalKernelDegrees_iff_hilbert _ ys).mp hmin d)
  obtain ⟨k,e,he,T,U,hTU,hUT,hcanonical⟩ := hcanon
  exact ⟨k,e,he.trans hp,T,U,hTU,hUT,hcanonical⟩

end FD56
