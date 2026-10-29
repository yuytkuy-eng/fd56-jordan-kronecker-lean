/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.InteriorFullGradients
import FD56.Hilbert.GenericObservabilityDegreeBudget
import FD56.Hilbert.GenericInteriorScalarFrame
import FD56.Stabilizer.FiveOutputComplementaryRows

/-! Signed complementary observability minors for five outputs and
remainder three, with their actual SL kernel gradients. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 2000000

def fiveOutputAlternatingMatrix {R : Type*} [CommRing R] (f : Fin 10 → R) :
    Matrix (Fin 5) (Fin 5) R :=
  ![![0,f 0,f 1,f 2,f 3],![-f 0,0,f 4,f 5,f 6],
    ![-f 1,-f 4,0,f 7,f 8],![-f 2,-f 5,-f 7,0,f 9],![-f 3,-f 6,-f 8,-f 9,0]]

theorem fiveOutputAlternatingMatrix_upper {R : Type*} [CommRing R]
    (f : Fin 10 → R) (i : Fin 10) :
    fiveOutputAlternatingMatrix f (fiveOutputPair i).1 (fiveOutputPair i).2=f i := by
  fin_cases i <;> rfl

theorem fiveOutputAlternatingMatrix_wedge {R : Type*} [CommRing R]
    (u v : Fin 5 → R) :
    fiveOutputAlternatingMatrix (fun i => twoColumnWedge u v
      (fiveOutputPair i).1 (fiveOutputPair i).2)=twoColumnWedge u v := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [fiveOutputAlternatingMatrix,fiveOutputPair,twoColumnWedge] <;> ring

variable (q : ℕ)

def fiveOutputCorankTwoMinor {R : Type*} [CommRing R]
    (M : Matrix (Fin (5*q+3)) (Fin (5*q+3)) R)
    (P : Matrix (Fin 5) (Fin (5*q+3)) R) (i : Fin 10) : R :=
  (fiveOutputComplementarySign i : R)*
    interiorFullMinor 3 2 q M P (fiveOutputComplementaryTriple i)

def fiveOutputCorankTwoMinors {R : Type*} [CommRing R]
    (M : Matrix (Fin (5*q+3)) (Fin (5*q+3)) R)
    (P : Matrix (Fin 5) (Fin (5*q+3)) R) : Matrix (Fin 5) (Fin 5) R :=
  fiveOutputAlternatingMatrix (fiveOutputCorankTwoMinor q M P)

def fiveOutputCorankTwoGradients {R : Type*} [CommRing R]
    (M : Matrix (Fin (5*q+3)) (Fin (5*q+3)) R)
    (P : Matrix (Fin 5) (Fin (5*q+3)) R) :
    Matrix (SLInput (Fin (5*q+3)) (Fin 5)) (Fin 10) R :=
  fun t i => (fiveOutputComplementarySign i : R)*
    interiorFullGradient 3 2 q M P (fiveOutputComplementaryTriple i) t

theorem fiveOutputCorankTwoGradients_kernel {K : Type*} [Field K]
    (M : Matrix (Fin (5*q+3)) (Fin (5*q+3)) K[X])
    (P : Matrix (Fin 5) (Fin (5*q+3)) K[X]) (i₀ : Fin (5*q+3)) :
    slEquationMatrix M P i₀*fiveOutputCorankTwoGradients q M P=0 := by
  funext t i
  change (slEquationMatrix M P i₀ *ᵥ
    ((fiveOutputComplementarySign i : K[X]) •
      interiorFullGradient 3 2 q M P (fiveOutputComplementaryTriple i))) t=0
  rw [Matrix.mulVec_smul_assoc,
    interiorFullGradient_kernel 3 2 q M P (fiveOutputComplementaryTriple i) i₀,smul_zero]
  rfl

theorem fiveOutputCorankTwoGradients_degree {K : Type*} [Field K]
    (M : Matrix (Fin (5*q+3)) (Fin (5*q+3)) K[X])
    (P : Matrix (Fin 5) (Fin (5*q+3)) K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) :
    DegreeBound (fiveOutputCorankTwoGradients q M P) (interiorFullWeight 3 2 q-1) := by
  intro t i
  apply le_trans Polynomial.natDegree_mul_le
  simpa using interiorFullGradient_degree 3 2 q M P hM hP (fiveOutputComplementaryTriple i) t

private theorem corank_two_minor_selected {K : Type*} [Field K]
    (M : Matrix (Fin (5*q+3)) (Fin (5*q+3)) K[X])
    (P : Matrix (Fin 5) (Fin (5*q+3)) K[X])
    (R : Matrix (Fin (5*q+3)) (Fin q × Fin 5) K[X])
    (hR : observabilityMatrix M P q*R=1)
    (B : Basis (Fin 3) K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q))))
    (z : Option (Fin 3 × Fin 2)) :
    interiorFullMinor 3 2 q M P (interiorTerminalRow 3 2 z)=
      (fiveOutputCorankTwoSelectedSign z : K[X]) *
        fiveOutputCorankTwoMinor q M P (fiveOutputCorankTwoSelectedPair z) := by
  obtain ⟨c,_,hc⟩ := interiorFullMinor_common_scalar 3 2 q M P R hR B
  unfold fiveOutputCorankTwoMinor
  rw [hc,hc]
  change C c*( (P*M^q*polynomialKernelBasisMatrix _ B).submatrix
    (interiorTerminalRow 3 2 z) id).det=_
  rw [five_output_corank_two_selected_det]
  unfold pluckerMinorVector
  ring

variable {K : Type*} [Field K]

def genericFiveOutputCorankTwoMinors := fiveOutputCorankTwoMinors q
  (genericAffineSquare K (Fin (5*q+3)) (Fin 5))
  (genericAffineRows K (Fin (5*q+3)) (Fin 5))

def genericFiveOutputCorankTwoGradients := fiveOutputCorankTwoGradients q
  (genericAffineSquare K (Fin (5*q+3)) (Fin 5))
  (genericAffineRows K (Fin (5*q+3)) (Fin 5))

private theorem generic_corank_two_minor_selected (z : Option (Fin 3 × Fin 2)) :
    interiorFullMinor 3 2 q (genericAffineSquare K _ _) (genericAffineRows K _ _)
        (interiorTerminalRow 3 2 z)=
      (fiveOutputCorankTwoSelectedSign z :
        (AffineCoefficientField K (MatrixParameters (Fin (5*q+3)) (Fin 5)))[X]) *
      fiveOutputCorankTwoMinor q (genericAffineSquare K _ _) (genericAffineRows K _ _)
        (fiveOutputCorankTwoSelectedPair z) := by
  let M := genericAffineSquare K (Fin (5*q+3)) (Fin 5)
  let P := genericAffineRows K (Fin (5*q+3)) (Fin 5)
  let O := observabilityMatrix M P q
  have hlo : q*Fintype.card (Fin 5) < Fintype.card (Fin (5*q+3)) := by
    simp only [Fintype.card_fin]; omega
  obtain ⟨r,B,e,hV,hVL,_,_⟩ := polynomial_kernel_has_minimal_basis O
  have hmin : HasMinimalKernelDegrees O (List.ofFn e) := ⟨r,B,e,hV,hVL,List.Perm.refl _⟩
  have hr := (generic_observability_kernel_degree_budget (K:=K) q hlo _ hmin).1
  simp only [List.length_ofFn,Fintype.card_fin] at hr
  have hr' : r=3 := by omega
  subst r
  obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse (K:=K) q hlo
  exact corank_two_minor_selected q M P R hR B z

theorem generic_five_output_corank_two_gradient_derivation
    (t : SLInput (Fin (5*q+3)) (Fin 5)) :
    ∃ D : Derivation K (AffineCoefficientField K (MatrixParameters (Fin (5*q+3)) (Fin 5)))
        (AffineCoefficientField K (MatrixParameters (Fin (5*q+3)) (Fin 5))),
      ∀ i, polynomialCoefficientDerivation D
          (genericFiveOutputCorankTwoMinors (K:=K) q (fiveOutputPair i).1 (fiveOutputPair i).2)=
        genericFiveOutputCorankTwoGradients (K:=K) q t i := by
  obtain ⟨D,hD⟩ := generic_interior_full_gradient_derivation (K:=K) 3 2 q t
  refine ⟨D,?_⟩
  intro i
  change polynomialCoefficientDerivation D
    (fiveOutputAlternatingMatrix _ (fiveOutputPair i).1 (fiveOutputPair i).2)=_
  rw [fiveOutputAlternatingMatrix_upper]
  simp only [fiveOutputCorankTwoMinor,Derivation.leibniz,Derivation.map_intCast,
    smul_zero,add_zero,smul_eq_mul,hD,mul_zero,add_zero]
  rfl

theorem generic_five_output_corank_two_gradients_selected
    (t : SLInput (Fin (5*q+3)) (Fin 5)) (z : Option (Fin 3 × Fin 2)) :
    interiorScalarLiftMatrix 3 2 q (genericAffineSquare K _ _) (genericAffineRows K _ _) t z=
      (fiveOutputCorankTwoSelectedSign z :
        (AffineCoefficientField K (MatrixParameters (Fin (5*q+3)) (Fin 5)))[X]) *
        genericFiveOutputCorankTwoGradients (K:=K) q t (fiveOutputCorankTwoSelectedPair z) := by
  obtain ⟨D,hD⟩ := generic_interior_full_gradient_derivation (K:=K) 3 2 q t
  have h := congrArg (polynomialCoefficientDerivation D)
    (generic_corank_two_minor_selected (K:=K) q z)
  simp only [fiveOutputCorankTwoMinor,Derivation.leibniz,Derivation.map_intCast,
    smul_zero,add_zero,smul_eq_mul,hD,mul_zero,add_zero] at h
  simpa only [interiorFullGradient,interiorFullRow_selected,interiorScalarLiftMatrix,
    genericFiveOutputCorankTwoGradients,fiveOutputCorankTwoGradients] using h

end FD56
