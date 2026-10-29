/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.TwoColumnInteriorGradientBounds
import FD56.Hilbert.TwoColumnGradientAlternation
import FD56.Hilbert.GenericNondivisibleSLStructure
import FD56.LinearAlgebra.AffineKernelFrameRank
import FD56.LinearAlgebra.SelectedFrameTranspose
import FD56.LinearAlgebra.MatrixFactorRelations
import FD56.Hilbert.ReducedFactorHilbertTests
import FD56.Hilbert.BalancedDegreeProfile

/-! The actual five-output, remainder-two SL kernel factors its Plucker
gradients through a reduced basis. Two explicit tangent Hilbert tests
then determine the complete balanced SL profile. These tests remain
premises; the module does not establish them at every depth. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 3000000

private theorem five_output_weight_twice (q : ℕ) :
    2*twoColumnInteriorWeight 3 q=5*q^2+9*q+4 := by
  obtain ⟨h,hh⟩ := Nat.even_mul_succ_self q
  have hn : 5*q*(q+1)+4*(q+1)=2*(5*h+2*(q+1)) := by nlinarith
  unfold twoColumnInteriorWeight
  norm_num only [Nat.reduceAdd]
  have hd : (5*q*(q+1)+4*(q+1))/2=5*h+2*(q+1) := by omega
  rw [hd]
  nlinarith

variable {K : Type*} [Field K]

private abbrev FiveOutputField (q : ℕ) :=
  AffineCoefficientField K (MatrixParameters (Fin (5*q+2)) (Fin 5))

theorem generic_five_output_sl_tangent_factor (q : ℕ) (hq : 0<q)
    (i₀ : Fin (5*q+2)) :
    ∃ (B : Basis (Fin 7) (FiveOutputField (K:=K) q)[X]
        (LinearMap.ker (Matrix.toLin' (slEquationMatrix
          (genericAffineSquare K (Fin (5*q+2)) (Fin 5))
          (genericAffineRows K (Fin (5*q+2)) (Fin 5)) i₀))))
      (e : Fin 7 → ℕ) (C : Matrix (Fin 7) (Fin 10) (FiveOutputField (K:=K) q)[X]),
      (∀ i j, (polynomialKernelBasisMatrix _ B i j).natDegree≤e j) ∧
      Function.Injective (Matrix.mulVec
        (fun i j => (polynomialKernelBasisMatrix _ B i j).coeff (e j))) ∧
      polynomialKernelBasisMatrix _ B*C=
        (genericTwoColumnInteriorScalarGradients (K:=K) 3 q).submatrix id fiveOutputPair ∧
      Function.Injective C.transpose.mulVec ∧
      DegreeBound (polynomialKernelBasisMatrix _ B*C) (twoColumnInteriorWeight 3 q-1) ∧
      fiveOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 3 q)*C.transpose=0 ∧
      (∑ i, e i)+2*twoColumnInteriorWeight 3 q=7*(twoColumnInteriorWeight 3 q-1) := by
  classical
  let L := FiveOutputField (K:=K) q
  let M := genericAffineSquare K (Fin (5*q+2)) (Fin 5)
  let P := genericAffineRows K (Fin (5*q+2)) (Fin 5)
  let S := slEquationMatrix M P i₀
  have hlo : q*Fintype.card (Fin 5)<Fintype.card (Fin (5*q+2)) := by
    simp only [Fintype.card_fin]; omega
  have hhi : Fintype.card (Fin (5*q+2))<(q+1)*Fintype.card (Fin 5) := by
    simp only [Fintype.card_fin]; omega
  obtain ⟨xs,hlen,hsum,hmin,_⟩ := generic_nondivisible_sl_kronecker_structure
    (K:=K) (n:=Fin (5*q+2)) (m:=Fin 5) q hq i₀ hlo hhi
  simp only [Fintype.card_fin] at hlen hsum
  have hlen7 : xs.length=7 := by
    have h₁ : 5*q+2-q*5=2 := by omega
    have h₂ : (q+1)*5-(5*q+2)=3 := by omega
    simpa only [h₁,h₂] using hlen
  obtain ⟨r,B,e,hV,hlead,hperm⟩ := hmin
  have hr : r=7 := by simpa only [List.length_ofFn,hlen7] using hperm.length_eq
  subst r
  have heSum : (∑ i, e i)+2*twoColumnInteriorWeight 3 q=7*(twoColumnInteriorWeight 3 q-1) := by
    have h := hperm.sum_eq
    rw [List.sum_ofFn] at h
    have hW := five_output_weight_twice q
    have hWp := twoColumnInteriorWeight_pos 3 q
    have hsub := Nat.sub_add_cancel hWp
    rw [hlen7] at hsum
    nlinarith
  let V := polynomialKernelBasisMatrix S B
  let Z := genericTwoColumnInteriorScalarGradients (K:=K) 3 q
  let A := fiveOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 3 q)
  have hVinj : Function.Injective V.mulVec := polynomialKernelBasisMatrix_injective S B
  obtain ⟨C,hVC⟩ := polynomialKernelFrame_factor S B Z
    (twoColumnInteriorScalarGradients_kernel 3 q M P i₀)
  change V*C=Z at hVC
  let select : Option (Fin 2 × Fin 3) → Fin 5 × Fin 5 :=
    fun z => (interiorTerminalRow 2 3 z 0,interiorTerminalRow 2 3 z 1)
  let φ : L[X] →+* RatFunc L := algebraMap L[X] (RatFunc L)
  have hφ : Function.Injective φ := IsFractionRing.injective L[X] (RatFunc L)
  have hCinj : Function.Injective C.transpose.mulVec := by
    apply factor_transpose_injective_of_selected_field_frame V C φ hφ select (by decide)
    rw [hVC]
    change Function.Injective (((twoColumnInteriorScalarGradients 3 q M P).submatrix id
      (fun z => (interiorTerminalRow 2 3 z 0,interiorTerminalRow 2 3 z 1))).map φ).mulVec
    rw [twoColumnInteriorScalarGradients_selected]
    exact generic_interior_scalar_lifts_field_injective 2 3 q φ hφ
  have hCalt := factor_columns_alternating V C hVinj
    (by
      intro t i
      rw [hVC]
      exact (generic_two_column_gradients_alternating (K:=K) 3 q t).1 i)
    (by
      intro t i j
      rw [hVC]
      exact (generic_two_column_gradients_alternating (K:=K) 3 q t).2 i j)
  let C₁ := C.submatrix id fiveOutputPair
  have hC₁ : Function.Injective C₁.transpose.mulVec :=
    transpose_upper_pairs_injective C hCinj hCalt.1 hCalt.2
  have hVC₁ : V*C₁=Z.submatrix id fiveOutputPair := by rw [←hVC]; rfl
  have hVCdegree : DegreeBound (V*C₁) (twoColumnInteriorWeight 3 q-1) := by
    rw [hVC₁]
    intro i j
    exact generic_two_column_scalar_gradients_degree (K:=K) 3 q i (fiveOutputPair j)
  have hAZ : A*(V*C₁).transpose=0 := by
    rw [hVC₁]
    funext i t
    change (fiveOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 3 q)*ᵥ
      (fun j => genericTwoColumnInteriorScalarGradients (K:=K) 3 q t (fiveOutputPair j))) i=0
    rw [fiveOutputPluckerTangent_mulVec _
      (fun a b => genericTwoColumnInteriorScalarGradients (K:=K) 3 q t (a,b))]
    exact generic_two_column_gradient_plucker_relation (K:=K) 3 q t
      (fiveOutputQuad i 0) (fiveOutputQuad i 1) (fiveOutputQuad i 2) (fiveOutputQuad i 3)
  exact ⟨B,e,C₁,hV,hlead,hVC₁,hC₁,hVCdegree,
    factor_transpose_kernel_of_product V C₁ A hVinj hAZ,heSum⟩

theorem generic_five_output_sl_degrees_of_tangent_tests (q : ℕ) (hq : 0<q)
    (i₀ : Fin (5*q+2))
    (hzero : Module.finrank (FiveOutputField (K:=K) q)
      (polynomialKernelAtDegree
        (fiveOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 3 q))
        (2*twoColumnInteriorWeight 3 q/7-1))=0)
    (hcritical : Module.finrank (FiveOutputField (K:=K) q)
      (polynomialKernelAtDegree
        (fiveOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 3 q))
        (2*twoColumnInteriorWeight 3 q/7))≤7-(2*twoColumnInteriorWeight 3 q)%7) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (5*q+2)) (Fin 5))
      (genericAffineRows K (Fin (5*q+2)) (Fin 5)) i₀)
      (balancedDegreeList (7*(twoColumnInteriorWeight 3 q-1)-2*twoColumnInteriorWeight 3 q) 7) := by
  obtain ⟨B,e,C,hV,hlead,_,hC,hVC,hAC,hsum⟩ :=
    generic_five_output_sl_tangent_factor (K:=K) q hq i₀
  have hk : 0<2*twoColumnInteriorWeight 3 q/7 := by
    have hW := five_output_weight_twice q
    have hlarge : 18≤2*twoColumnInteriorWeight 3 q := by nlinarith
    omega
  have hbalance := reduced_factor_balanced_of_two_kernel_tests
    (polynomialKernelBasisMatrix _ B) C e (twoColumnInteriorWeight 3 q-1)
    (2*twoColumnInteriorWeight 3 q/7) ((2*twoColumnInteriorWeight 3 q)%7)
    hV hlead hC hVC _ hAC hk
    (by simp only [Fintype.card_fin]; omega)
    (by
      simp only [Fintype.card_fin]
      have hdiv := Nat.mod_add_div (2*twoColumnInteriorWeight 3 q) 7
      omega)
    hzero hcritical
  have hesum : (∑ i, e i)=7*(twoColumnInteriorWeight 3 q-1)-2*twoColumnInteriorWeight 3 q := by
    omega
  rw [←hesum]
  exact reduced_kernel_basis_balanced_minimal_degrees _ (by decide) B e hV hlead hbalance

theorem generic_five_output_sl_classification_of_tangent_tests (q : ℕ) (hq : 0<q)
    (i₀ : Fin (5*q+2))
    (hzero : Module.finrank (FiveOutputField (K:=K) q)
      (polynomialKernelAtDegree
        (fiveOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 3 q))
        (2*twoColumnInteriorWeight 3 q/7-1))=0)
    (hcritical : Module.finrank (FiveOutputField (K:=K) q)
      (polynomialKernelAtDegree
        (fiveOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 3 q))
        (2*twoColumnInteriorWeight 3 q/7))≤7-(2*twoColumnInteriorWeight 3 q)%7) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (5*q+2)) (Fin 5))
      (genericAffineRows K (Fin (5*q+2)) (Fin 5)) i₀)
      (balancedDegreeList (7*(twoColumnInteriorWeight 3 q-1)-2*twoColumnInteriorWeight 3 q) 7) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (5*q+2)) (Fin 5))
      (genericAffineRows K (Fin (5*q+2)) (Fin 5)) i₀)
      (balancedDegreeList (7*(twoColumnInteriorWeight 3 q-1)-2*twoColumnInteriorWeight 3 q) 7) := by
  let ys := balancedDegreeList
    (7*(twoColumnInteriorWeight 3 q-1)-2*twoColumnInteriorWeight 3 q) 7
  have hmin := generic_five_output_sl_degrees_of_tangent_tests (K:=K) q hq i₀ hzero hcritical
  refine ⟨hmin,?_⟩
  obtain ⟨xs,_,_,hxs,hcanon⟩ := generic_nondivisible_sl_kronecker_structure
    (K:=K) (n:=Fin (5*q+2)) (m:=Fin 5) q hq i₀
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
