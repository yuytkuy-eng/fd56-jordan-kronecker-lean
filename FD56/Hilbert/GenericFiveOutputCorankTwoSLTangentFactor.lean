/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.FiveOutputCorankTwoTangentRelations
import FD56.Hilbert.GenericNondivisibleSLStructure
import FD56.LinearAlgebra.AffineKernelFrameRank
import FD56.LinearAlgebra.SelectedFrameTranspose
import FD56.LinearAlgebra.MatrixFactorRelations

/-! The actual five-output corank-two gradients factor through the reduced
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

theorem five_output_corank_two_weight_twice (q : ℕ) :
    2*interiorFullWeight 3 2 q=5*q^2+11*q+6 := by
  obtain ⟨h,hh⟩ := Nat.even_mul_succ_self q
  have hn : 5*q*(q+1)+2*3*(q+1)=2*(5*h+3*(q+1)) := by nlinarith
  unfold interiorFullWeight
  norm_num only [Nat.reduceAdd]
  have hd : (5*q*(q+1)+2*3*(q+1))/2=5*h+3*(q+1) := by omega
  rw [hd]
  nlinarith

variable {K : Type*} [Field K] [CharZero K]

private abbrev CorankTwoSLField (q : ℕ) :=
  AffineCoefficientField K (MatrixParameters (Fin (5*q+3)) (Fin 5))

theorem generic_five_output_corank_two_sl_tangent_factor (q : ℕ) (hq : 0<q)
    (i₀ : Fin (5*q+3)) :
    ∃ (B : Basis (Fin 7) (CorankTwoSLField (K:=K) q)[X]
        (LinearMap.ker (Matrix.toLin' (slEquationMatrix
          (genericAffineSquare K (Fin (5*q+3)) (Fin 5))
          (genericAffineRows K (Fin (5*q+3)) (Fin 5)) i₀))))
      (e : Fin 7 → ℕ) (C : Matrix (Fin 7) (Fin 10) (CorankTwoSLField (K:=K) q)[X]),
      (∀ i j, (polynomialKernelBasisMatrix _ B i j).natDegree≤e j) ∧
      Function.Injective (Matrix.mulVec
        (fun i j => (polynomialKernelBasisMatrix _ B i j).coeff (e j))) ∧
      polynomialKernelBasisMatrix _ B*C=genericFiveOutputCorankTwoGradients (K:=K) q ∧
      Function.Injective C.transpose.mulVec ∧
      DegreeBound (polynomialKernelBasisMatrix _ B*C) (interiorFullWeight 3 2 q-1) ∧
      fiveOutputPluckerTangent (genericFiveOutputCorankTwoMinors (K:=K) q)*C.transpose=0 ∧
      (∑ i, e i)+2*interiorFullWeight 3 2 q=7*(interiorFullWeight 3 2 q-1) := by
  classical
  let L := CorankTwoSLField (K:=K) q
  let M := genericAffineSquare K (Fin (5*q+3)) (Fin 5)
  let P := genericAffineRows K (Fin (5*q+3)) (Fin 5)
  let S := slEquationMatrix M P i₀
  have hlo : q*Fintype.card (Fin 5)<Fintype.card (Fin (5*q+3)) := by
    simp only [Fintype.card_fin]; omega
  have hhi : Fintype.card (Fin (5*q+3))<(q+1)*Fintype.card (Fin 5) := by
    simp only [Fintype.card_fin]; omega
  obtain ⟨xs,hlen,hsum,hmin,_⟩ := generic_nondivisible_sl_kronecker_structure
    (K:=K) (n:=Fin (5*q+3)) (m:=Fin 5) q hq i₀ hlo hhi
  simp only [Fintype.card_fin] at hlen hsum
  have hlen7 : xs.length=7 := by
    have h₁ : 5*q+3-q*5=3 := by omega
    have h₂ : (q+1)*5-(5*q+3)=2 := by omega
    simpa only [h₁,h₂] using hlen
  obtain ⟨r,B,e,hV,hlead,hperm⟩ := hmin
  have hr : r=7 := by simpa only [List.length_ofFn,hlen7] using hperm.length_eq
  subst r
  have heSum : (∑ i, e i)+2*interiorFullWeight 3 2 q=7*(interiorFullWeight 3 2 q-1) := by
    have h := hperm.sum_eq
    rw [List.sum_ofFn] at h
    have hW := five_output_corank_two_weight_twice q
    have hWp := interiorFullWeight_pos 3 2 q
    have hsub := Nat.sub_add_cancel hWp
    rw [hlen7] at hsum
    nlinarith
  let V := polynomialKernelBasisMatrix S B
  let Z := genericFiveOutputCorankTwoGradients (K:=K) q
  let A := fiveOutputPluckerTangent (genericFiveOutputCorankTwoMinors (K:=K) q)
  have hVinj : Function.Injective V.mulVec := polynomialKernelBasisMatrix_injective S B
  obtain ⟨C,hVC⟩ := polynomialKernelFrame_factor S B Z
    (fiveOutputCorankTwoGradients_kernel q M P i₀)
  change V*C=Z at hVC
  let φ : L[X] →+* RatFunc L := algebraMap L[X] (RatFunc L)
  have hφ : Function.Injective φ := IsFractionRing.injective L[X] (RatFunc L)
  have hCinj : Function.Injective C.transpose.mulVec := by
    apply factor_transpose_injective_of_selected_field_frame V C φ hφ
      fiveOutputCorankTwoSelectedPair (by decide)
    rw [hVC]
    apply injective_of_signed_columns
      ((interiorScalarLiftMatrix 3 2 q M P).map φ)
      ((Z.submatrix id fiveOutputCorankTwoSelectedPair).map φ)
      (fun z => φ (fiveOutputCorankTwoSelectedSign z))
    · intro z
      rw [← map_mul,← Int.cast_mul,fiveOutputCorankTwoSelectedSign_sq,Int.cast_one,map_one]
    · intro t z
      change φ (interiorScalarLiftMatrix 3 2 q M P t z)=_
      rw [generic_five_output_corank_two_gradients_selected,map_mul]
      rfl
    · exact generic_interior_scalar_lifts_field_injective 3 2 q φ hφ
  have hVCdegree : DegreeBound (V*C) (interiorFullWeight 3 2 q-1) := by
    rw [hVC]
    exact fiveOutputCorankTwoGradients_degree q M P
      (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
  have hAZ : A*(V*C).transpose=0 := by
    rw [hVC]
    exact generic_five_output_corank_two_gradient_tangent (K:=K) q hq
  exact ⟨B,e,C,hV,hlead,hVC,hCinj,hVCdegree,
    factor_transpose_kernel_of_product V C A hVinj hAZ,heSum⟩

end FD56
