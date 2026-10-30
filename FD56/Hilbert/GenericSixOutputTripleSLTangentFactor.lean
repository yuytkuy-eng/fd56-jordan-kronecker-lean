/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputTripleGradients
import FD56.Hilbert.GenericNondivisibleSLStructure
import FD56.LinearAlgebra.AffineKernelFrameRank
import FD56.LinearAlgebra.SelectedFrameTranspose
import FD56.LinearAlgebra.MatrixFactorRelations

/-! The actual six-output middle-remainder gradients factor through the reduced
SL kernel, with an injective transpose and the exact degree budget. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 3000000

private theorem injective_of_signed_columns {R n j : Type*} [CommRing R] [Fintype j]
    (A B : Matrix n j R) (s : j → R) (hs : ∀ i, s i*s i=1)
    (hAB : ∀ i j, A i j=s j*B i j) (hA : Function.Injective A.mulVec) :
    Function.Injective B.mulVec := by
  have he (x : j → R) : A*ᵥ(fun j => s j*x j)=B*ᵥx := by
    funext i
    simp only [Matrix.mulVec,dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    rw [hAB]
    calc
      s j*B i j*(s j*x j)=(s j*s j)*(B i j*x j) := by ring
      _=B i j*x j := by rw [hs,one_mul]
  intro x y hxy
  have h := hA ((he x).trans (hxy.trans (he y).symm))
  funext j
  have hj := congrArg (fun z => s j*z) (congrFun h j)
  simpa only [← mul_assoc,hs,one_mul] using hj

private theorem triple_selected_sign_sq (z : Option (Fin 3 × Fin 3)) :
    sixOutputTripleSelectedSign z*sixOutputTripleSelectedSign z=1 := by
  cases z with
  | none => rfl
  | some z => simp only [sixOutputTripleSelectedSign]; split_ifs <;> norm_num

theorem six_output_triple_weight (q : ℕ) :
    interiorFullWeight 3 3 q=3*(q+1)^2 := by
  have hn : 6*q*(q+1)+2*3*(q+1)=2*(3*(q+1)^2) := by ring
  unfold interiorFullWeight
  norm_num only [Nat.reduceAdd]
  rw [hn]
  omega

variable {K : Type*} [Field K]

private abbrev TripleSLField (q : ℕ) :=
  AffineCoefficientField K (MatrixParameters (Fin (6*q+3)) (Fin 6))

theorem generic_six_output_triple_sl_tangent_factor (q : ℕ) (hq : 0<q)
    (i₀ : Fin (6*q+3)) :
    ∃ (B : Basis (Fin 10) (TripleSLField (K:=K) q)[X]
        (LinearMap.ker (Matrix.toLin' (slEquationMatrix
          (genericAffineSquare K (Fin (6*q+3)) (Fin 6))
          (genericAffineRows K (Fin (6*q+3)) (Fin 6)) i₀))))
      (e : Fin 10 → ℕ) (C : Matrix (Fin 10) (Fin 20) (TripleSLField (K:=K) q)[X]),
      (∀ i j, (polynomialKernelBasisMatrix _ B i j).natDegree≤e j) ∧
      Function.Injective (Matrix.mulVec
        (fun i j => (polynomialKernelBasisMatrix _ B i j).coeff (e j))) ∧
      polynomialKernelBasisMatrix _ B*C=genericSixOutputTripleGradients (K:=K) q ∧
      Function.Injective C.transpose.mulVec ∧
      DegreeBound (polynomialKernelBasisMatrix _ B*C) (interiorFullWeight 3 3 q-1) ∧
      sixOutputTriplePluckerTangent (genericSixOutputTripleMinors (K:=K) q)*C.transpose=0 ∧
      (∑ i, e i)+4*interiorFullWeight 3 3 q=10*(interiorFullWeight 3 3 q-1) := by
  classical
  let L := TripleSLField (K:=K) q
  let M := genericAffineSquare K (Fin (6*q+3)) (Fin 6)
  let P := genericAffineRows K (Fin (6*q+3)) (Fin 6)
  let S := slEquationMatrix M P i₀
  have hlo : q*Fintype.card (Fin 6)<Fintype.card (Fin (6*q+3)) := by
    simp only [Fintype.card_fin]; omega
  have hhi : Fintype.card (Fin (6*q+3))<(q+1)*Fintype.card (Fin 6) := by
    simp only [Fintype.card_fin]; omega
  obtain ⟨xs,hlen,hsum,hmin,_⟩ := generic_nondivisible_sl_kronecker_structure
    (K:=K) (n:=Fin (6*q+3)) (m:=Fin 6) q hq i₀ hlo hhi
  simp only [Fintype.card_fin] at hlen hsum
  have hlen10 : xs.length=10 := by
    have h₁ : 6*q+3-q*6=3 := by omega
    have h₂ : (q+1)*6-(6*q+3)=3 := by omega
    simpa only [h₁,h₂] using hlen
  obtain ⟨r,B,e,hV,hlead,hperm⟩ := hmin
  have hr : r=10 := by simpa only [List.length_ofFn,hlen10] using hperm.length_eq
  subst r
  have heSum : (∑ i, e i)+4*interiorFullWeight 3 3 q=10*(interiorFullWeight 3 3 q-1) := by
    have h := hperm.sum_eq
    rw [List.sum_ofFn] at h
    have hW := six_output_triple_weight q
    have hWp := interiorFullWeight_pos 3 3 q
    have hsub := Nat.sub_add_cancel hWp
    rw [hlen10] at hsum
    nlinarith
  let V := polynomialKernelBasisMatrix S B
  let Z := genericSixOutputTripleGradients (K:=K) q
  let A := sixOutputTriplePluckerTangent (genericSixOutputTripleMinors (K:=K) q)
  have hVinj : Function.Injective V.mulVec := polynomialKernelBasisMatrix_injective S B
  obtain ⟨C,hVC⟩ := polynomialKernelFrame_factor S B Z
    (sixOutputTripleGradients_kernel q M P i₀)
  change V*C=Z at hVC
  let φ : L[X] →+* RatFunc L := algebraMap L[X] (RatFunc L)
  have hφ : Function.Injective φ := IsFractionRing.injective L[X] (RatFunc L)
  have hCinj : Function.Injective C.transpose.mulVec := by
    apply factor_transpose_injective_of_selected_field_frame V C φ hφ
      sixOutputTripleSelectedIndex (by decide)
    rw [hVC]
    apply injective_of_signed_columns
      ((interiorScalarLiftMatrix 3 3 q M P).map φ)
      ((Z.submatrix id sixOutputTripleSelectedIndex).map φ)
      (fun z => φ (sixOutputTripleSelectedSign z))
    · intro z
      rw [← map_mul,← Int.cast_mul,triple_selected_sign_sq,Int.cast_one,map_one]
    · intro t z
      change φ (interiorScalarLiftMatrix 3 3 q M P t z)=_
      rw [generic_six_output_triple_gradients_selected q hq,map_mul]
      rfl
    · exact generic_interior_scalar_lifts_field_injective 3 3 q φ hφ
  have hVCdegree : DegreeBound (V*C) (interiorFullWeight 3 3 q-1) := by
    rw [hVC]
    exact sixOutputTripleGradients_degree q M P
      (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
  have hAZ : A*(V*C).transpose=0 := by
    rw [hVC]
    exact generic_six_output_triple_gradient_tangent (K:=K) q hq
  exact ⟨B,e,C,hV,hlead,hVC,hCinj,hVCdegree,
    factor_transpose_kernel_of_product V C A hVinj hAZ,heSum⟩

end FD56
