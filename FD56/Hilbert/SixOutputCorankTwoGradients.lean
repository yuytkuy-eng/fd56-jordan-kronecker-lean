/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.InteriorFullGradients
import FD56.Hilbert.GenericObservabilityDegreeBudget
import FD56.Hilbert.GenericInteriorScalarFrame
import FD56.Stabilizer.SixOutputComplementaryRows

/-! Signed complementary observability minors for six outputs and
remainder four, with their actual SL kernel gradients. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 2000000

def sixOutputAlternatingMatrix {R : Type*} [CommRing R] (f : Fin 15 → R) :
    Matrix (Fin 6) (Fin 6) R :=
  ![![0,f 0,f 1,f 2,f 3,f 4],![-f 0,0,f 5,f 6,f 7,f 8],![-f 1,-f 5,0,f 9,f 10,f 11],![-f 2,-f 6,-f 9,0,f 12,f 13],![-f 3,-f 7,-f 10,-f 12,0,f 14],![-f 4,-f 8,-f 11,-f 13,-f 14,0]]

theorem sixOutputAlternatingMatrix_upper {R : Type*} [CommRing R]
    (f : Fin 15 → R) (i : Fin 15) :
    sixOutputAlternatingMatrix f (sixOutputPair i).1 (sixOutputPair i).2=f i := by
  fin_cases i <;> rfl

theorem sixOutputAlternatingMatrix_wedge {R : Type*} [CommRing R]
    (u v : Fin 6 → R) :
    sixOutputAlternatingMatrix (fun i => twoColumnWedge u v
      (sixOutputPair i).1 (sixOutputPair i).2)=twoColumnWedge u v := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [sixOutputAlternatingMatrix,sixOutputPair,twoColumnWedge] <;> ring

variable (q : ℕ)

def sixOutputCorankTwoMinor {R : Type*} [CommRing R]
    (M : Matrix (Fin (6*q+4)) (Fin (6*q+4)) R)
    (P : Matrix (Fin 6) (Fin (6*q+4)) R) (i : Fin 15) : R :=
  (sixOutputComplementarySign i : R)*
    interiorFullMinor 4 2 q M P (sixOutputComplementaryQuad i)

def sixOutputCorankTwoMinors {R : Type*} [CommRing R]
    (M : Matrix (Fin (6*q+4)) (Fin (6*q+4)) R)
    (P : Matrix (Fin 6) (Fin (6*q+4)) R) : Matrix (Fin 6) (Fin 6) R :=
  sixOutputAlternatingMatrix (sixOutputCorankTwoMinor q M P)

def sixOutputCorankTwoGradients {R : Type*} [CommRing R]
    (M : Matrix (Fin (6*q+4)) (Fin (6*q+4)) R)
    (P : Matrix (Fin 6) (Fin (6*q+4)) R) :
    Matrix (SLInput (Fin (6*q+4)) (Fin 6)) (Fin 15) R :=
  fun t i => (sixOutputComplementarySign i : R)*
    interiorFullGradient 4 2 q M P (sixOutputComplementaryQuad i) t

theorem sixOutputCorankTwoGradients_kernel {K : Type*} [Field K]
    (M : Matrix (Fin (6*q+4)) (Fin (6*q+4)) K[X])
    (P : Matrix (Fin 6) (Fin (6*q+4)) K[X]) (i₀ : Fin (6*q+4)) :
    slEquationMatrix M P i₀*sixOutputCorankTwoGradients q M P=0 := by
  funext t i
  change (slEquationMatrix M P i₀ *ᵥ
    ((sixOutputComplementarySign i : K[X]) •
      interiorFullGradient 4 2 q M P (sixOutputComplementaryQuad i))) t=0
  rw [Matrix.mulVec_smul_assoc,
    interiorFullGradient_kernel 4 2 q M P (sixOutputComplementaryQuad i) i₀,smul_zero]
  rfl

theorem sixOutputCorankTwoGradients_degree {K : Type*} [Field K]
    (M : Matrix (Fin (6*q+4)) (Fin (6*q+4)) K[X])
    (P : Matrix (Fin 6) (Fin (6*q+4)) K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) :
    DegreeBound (sixOutputCorankTwoGradients q M P) (interiorFullWeight 4 2 q-1) := by
  intro t i
  apply le_trans Polynomial.natDegree_mul_le
  simpa using interiorFullGradient_degree 4 2 q M P hM hP (sixOutputComplementaryQuad i) t

private theorem corank_two_minor_selected {K : Type*} [Field K]
    (M : Matrix (Fin (6*q+4)) (Fin (6*q+4)) K[X])
    (P : Matrix (Fin 6) (Fin (6*q+4)) K[X])
    (R : Matrix (Fin (6*q+4)) (Fin q × Fin 6) K[X])
    (hR : observabilityMatrix M P q*R=1)
    (B : Basis (Fin 4) K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q))))
    (z : Option (Fin 4 × Fin 2)) :
    interiorFullMinor 4 2 q M P (interiorTerminalRow 4 2 z)=
      (sixOutputCorankTwoSelectedSign z : K[X]) *
        sixOutputCorankTwoMinor q M P (sixOutputCorankTwoSelectedPair z) := by
  obtain ⟨c,_,hc⟩ := interiorFullMinor_common_scalar 4 2 q M P R hR B
  unfold sixOutputCorankTwoMinor
  rw [hc,hc]
  change C c*( (P*M^q*polynomialKernelBasisMatrix _ B).submatrix
    (interiorTerminalRow 4 2 z) id).det=_
  rw [six_output_corank_two_selected_det]
  unfold pluckerMinorVector
  ring

variable {K : Type*} [Field K]

def genericSixOutputCorankTwoMinors := sixOutputCorankTwoMinors q
  (genericAffineSquare K (Fin (6*q+4)) (Fin 6))
  (genericAffineRows K (Fin (6*q+4)) (Fin 6))

def genericSixOutputCorankTwoGradients := sixOutputCorankTwoGradients q
  (genericAffineSquare K (Fin (6*q+4)) (Fin 6))
  (genericAffineRows K (Fin (6*q+4)) (Fin 6))

private theorem generic_corank_two_minor_selected (z : Option (Fin 4 × Fin 2)) :
    interiorFullMinor 4 2 q (genericAffineSquare K _ _) (genericAffineRows K _ _)
        (interiorTerminalRow 4 2 z)=
      (sixOutputCorankTwoSelectedSign z :
        (AffineCoefficientField K (MatrixParameters (Fin (6*q+4)) (Fin 6)))[X]) *
      sixOutputCorankTwoMinor q (genericAffineSquare K _ _) (genericAffineRows K _ _)
        (sixOutputCorankTwoSelectedPair z) := by
  let M := genericAffineSquare K (Fin (6*q+4)) (Fin 6)
  let P := genericAffineRows K (Fin (6*q+4)) (Fin 6)
  let O := observabilityMatrix M P q
  have hlo : q*Fintype.card (Fin 6) < Fintype.card (Fin (6*q+4)) := by
    simp only [Fintype.card_fin]; omega
  obtain ⟨r,B,e,hV,hVL,_,_⟩ := polynomial_kernel_has_minimal_basis O
  have hmin : HasMinimalKernelDegrees O (List.ofFn e) := ⟨r,B,e,hV,hVL,List.Perm.refl _⟩
  have hr := (generic_observability_kernel_degree_budget (K:=K) q hlo _ hmin).1
  simp only [List.length_ofFn,Fintype.card_fin] at hr
  have hr' : r=4 := by omega
  subst r
  obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse (K:=K) q hlo
  exact corank_two_minor_selected q M P R hR B z

theorem generic_six_output_corank_two_gradient_derivation
    (t : SLInput (Fin (6*q+4)) (Fin 6)) :
    ∃ D : Derivation K (AffineCoefficientField K (MatrixParameters (Fin (6*q+4)) (Fin 6)))
        (AffineCoefficientField K (MatrixParameters (Fin (6*q+4)) (Fin 6))),
      ∀ i, polynomialCoefficientDerivation D
          (genericSixOutputCorankTwoMinors (K:=K) q (sixOutputPair i).1 (sixOutputPair i).2)=
        genericSixOutputCorankTwoGradients (K:=K) q t i := by
  obtain ⟨D,hD⟩ := generic_interior_full_gradient_derivation (K:=K) 4 2 q t
  refine ⟨D,?_⟩
  intro i
  change polynomialCoefficientDerivation D
    (sixOutputAlternatingMatrix _ (sixOutputPair i).1 (sixOutputPair i).2)=_
  rw [sixOutputAlternatingMatrix_upper]
  simp only [sixOutputCorankTwoMinor,Derivation.leibniz,Derivation.map_intCast,
    smul_zero,add_zero,smul_eq_mul,hD,mul_zero,add_zero]
  rfl

theorem generic_six_output_corank_two_gradients_selected
    (t : SLInput (Fin (6*q+4)) (Fin 6)) (z : Option (Fin 4 × Fin 2)) :
    interiorScalarLiftMatrix 4 2 q (genericAffineSquare K _ _) (genericAffineRows K _ _) t z=
      (sixOutputCorankTwoSelectedSign z :
        (AffineCoefficientField K (MatrixParameters (Fin (6*q+4)) (Fin 6)))[X]) *
        genericSixOutputCorankTwoGradients (K:=K) q t (sixOutputCorankTwoSelectedPair z) := by
  obtain ⟨D,hD⟩ := generic_interior_full_gradient_derivation (K:=K) 4 2 q t
  have h := congrArg (polynomialCoefficientDerivation D)
    (generic_corank_two_minor_selected (K:=K) q z)
  simp only [sixOutputCorankTwoMinor,Derivation.leibniz,Derivation.map_intCast,
    smul_zero,add_zero,smul_eq_mul,hD,mul_zero,add_zero] at h
  simpa only [interiorFullGradient,interiorFullRow_selected,interiorScalarLiftMatrix,
    genericSixOutputCorankTwoGradients,sixOutputCorankTwoGradients] using h

end FD56
