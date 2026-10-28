/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.TwoColumnInteriorGradients
import FD56.LinearAlgebra.FiveOutputPluckerTangent

/-! The actual ordered-pair gradients are alternating. Their upper entries
therefore retain every linear relation between their rows. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 2000000

private theorem scaled_wedge_alternating {R n : Type*} [CommRing R]
    (c : R) (u v : n → R) (i j : n) :
    (c • twoColumnWedge u v) j i= -(c • twoColumnWedge u v) i j := by
  change c*(u j*v i-u i*v j)= -(c*(u i*v j-u j*v i))
  ring

variable (s q : ℕ) [NeZero s] {K : Type*} [Field K]

theorem generic_two_column_minors_alternating :
    (∀ i, genericTwoColumnInteriorMinors (K:=K) s q i i=0) ∧
    (∀ i j, genericTwoColumnInteriorMinors (K:=K) s q j i=
      -genericTwoColumnInteriorMinors (K:=K) s q i j) := by
  let M := genericAffineSquare K (Fin ((2+s)*q+2)) (Fin (2+s))
  let P := genericAffineRows K (Fin ((2+s)*q+2)) (Fin (2+s))
  let O := observabilityMatrix M P q
  have hlo : q*Fintype.card (Fin (2+s))<Fintype.card (Fin ((2+s)*q+2)) := by
    simp only [Fintype.card_fin]; nlinarith
  obtain ⟨r,B,e,hV,hVL,_,_⟩ := polynomial_kernel_has_minimal_basis O
  have hmin : HasMinimalKernelDegrees O (List.ofFn e) := ⟨r,B,e,hV,hVL,List.Perm.refl _⟩
  have hr := (generic_observability_kernel_degree_budget (K:=K) q hlo _ hmin).1
  simp only [List.length_ofFn,Fintype.card_fin] at hr
  have hr' : r=2 := by nlinarith
  subst r
  obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse (K:=K) q hlo
  obtain ⟨c,_,hc⟩ := twoColumnInteriorMinors_common_scalar s q M P R hR B
  change (∀ i, twoColumnInteriorMinors s q M P i i=0) ∧
    (∀ i j, twoColumnInteriorMinors s q M P j i= -twoColumnInteriorMinors s q M P i j)
  rw [hc]
  constructor
  · intro i; simp [twoColumnWedge]
  · intro i j
    exact scaled_wedge_alternating _ _ _ i j

theorem generic_two_column_gradients_alternating
    (t : SLInput (Fin ((2+s)*q+2)) (Fin (2+s))) :
    (∀ i, genericTwoColumnInteriorScalarGradients (K:=K) s q t (i,i)=0) ∧
    (∀ i j, genericTwoColumnInteriorScalarGradients (K:=K) s q t (j,i)=
      -genericTwoColumnInteriorScalarGradients (K:=K) s q t (i,j)) := by
  classical
  let L := AffineCoefficientField K (MatrixParameters (Fin ((2+s)*q+2)) (Fin (2+s)))
  obtain ⟨D,hD⟩ := generic_minor_derivation_realizes_affine_pairing (K:=K)
    (fun _ : Fin (2+s) × Fin (2+s) => interiorLevel 2 s q)
    (twoColumnInteriorRow s q) (Pi.single t (1:L)) 0
  have he (a b : Fin (2+s)) : polynomialCoefficientDerivation D
      (genericTwoColumnInteriorMinors (K:=K) s q a b)=
        genericTwoColumnInteriorScalarGradients (K:=K) s q t (a,b) := by
    have h := hD (a,b)
    simpa [genericTwoColumnInteriorMinors,twoColumnInteriorMinors,
      genericTwoColumnInteriorScalarGradients,twoColumnInteriorScalarGradients,
      Pi.single_apply,dotProduct] using h
  obtain ⟨hd,hs⟩ := generic_two_column_minors_alternating (K:=K) s q
  constructor
  · intro i
    have h := congrArg (polynomialCoefficientDerivation D) (hd i)
    simpa only [map_zero,he] using h
  · intro i j
    have h := congrArg (polynomialCoefficientDerivation D) (hs i j)
    simpa only [map_neg,he] using h

theorem fiveOutput_upper_entries_determine {R : Type*} [AddGroup R]
    (H J : Matrix (Fin 5) (Fin 5) R)
    (hHd : ∀ i, H i i=0) (hHs : ∀ i j, H j i= -H i j)
    (hJd : ∀ i, J i i=0) (hJs : ∀ i j, J j i= -J i j)
    (hupper : ∀ k, H (fiveOutputPair k).1 (fiveOutputPair k).2=
      J (fiveOutputPair k).1 (fiveOutputPair k).2) : H=J := by
  have hlt (i j : Fin 5) (hij : i<j) : H i j=J i j := by
    fin_cases i <;> fin_cases j <;> norm_num at hij ⊢
    all_goals first
      | exact hupper 0 | exact hupper 1 | exact hupper 2 | exact hupper 3
      | exact hupper 4 | exact hupper 5 | exact hupper 6 | exact hupper 7
      | exact hupper 8 | exact hupper 9
  funext i j
  rcases lt_trichotomy i j with hij|hij|hij
  · exact hlt i j hij
  · subst j; rw [hHd,hJd]
  · rw [hHs j i,hJs j i,hlt j i hij]

theorem factor_columns_alternating {R a b n : Type*} [CommRing R] [Fintype b]
    (V : Matrix a b R) (C : Matrix b (n × n) R)
    (hV : Function.Injective V.mulVec)
    (hd : ∀ t i, (V*C) t (i,i)=0)
    (hs : ∀ t i j, (V*C) t (j,i)= -(V*C) t (i,j)) :
    (∀ t i, C t (i,i)=0) ∧ (∀ t i j, C t (j,i)= -C t (i,j)) := by
  constructor
  · intro t i
    have h : V *ᵥ (fun t => C t (i,i))=V *ᵥ 0 := by
      ext t
      simpa only [Matrix.mul_apply,Matrix.mulVec, dotProduct,Pi.zero_apply,mul_zero,
        Finset.sum_const_zero] using hd t i
    exact congrFun (hV h) t
  · intro t i j
    have h : V *ᵥ (fun t => C t (j,i))=V *ᵥ (-(fun t => C t (i,j))) := by
      rw [Matrix.mulVec_neg]
      ext t
      exact hs t i j
    exact congrFun (hV h) t

theorem transpose_upper_pairs_injective {R b : Type*} [CommRing R] [Fintype b]
    (C : Matrix b (Fin 5 × Fin 5) R)
    (hC : Function.Injective C.transpose.mulVec)
    (hd : ∀ t i, C t (i,i)=0)
    (hs : ∀ t i j, C t (j,i)= -C t (i,j)) :
    Function.Injective (C.submatrix id fiveOutputPair).transpose.mulVec := by
  intro x y hxy
  apply hC
  have hd' (v : b → R) (i : Fin 5) : (C.transpose *ᵥ v) (i,i)=0 := by
    simp only [Matrix.mulVec,Matrix.transpose_apply,dotProduct,hd,zero_mul,Finset.sum_const_zero]
  have hs' (v : b → R) (i j : Fin 5) :
      (C.transpose *ᵥ v) (j,i)= -(C.transpose *ᵥ v) (i,j) := by
    change (∑ t, C t (j,i)*v t)= -(∑ t, C t (i,j)*v t)
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [hs t i j,neg_mul]
  have h := fiveOutput_upper_entries_determine
    (fun i j => (C.transpose *ᵥ x) (i,j)) (fun i j => (C.transpose *ᵥ y) (i,j))
    (hd' x) (hs' x) (hd' y) (hs' y) (fun k => congrFun hxy k)
  funext ij
  exact congrFun (congrFun h ij.1) ij.2

end FD56
