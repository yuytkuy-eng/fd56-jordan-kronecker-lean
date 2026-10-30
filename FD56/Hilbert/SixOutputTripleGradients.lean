/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericSixOutputTripleRepresentation
import FD56.Hilbert.GenericInteriorScalarFrame
import FD56.LinearAlgebra.SixOutputTriplePluckerRelations
import FD56.Stabilizer.SixOutputTripleRows

/-! Actual twenty-column observability gradients for the six-output middle
remainder, including the selected ten-dimensional frame and tangent relations. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxHeartbeats 2000000

variable (q : ℕ)

def sixOutputTripleGradients {R : Type*} [CommRing R]
    (M : Matrix (Fin (6*q+3)) (Fin (6*q+3)) R)
    (P : Matrix (Fin 6) (Fin (6*q+3)) R) :
    Matrix (SLInput (Fin (6*q+3)) (Fin 6)) (Fin 20) R :=
  fun t i => interiorFullGradient 3 3 q M P (sixOutputTriple i) t

theorem sixOutputTripleGradients_kernel {K : Type*} [Field K]
    (M : Matrix (Fin (6*q+3)) (Fin (6*q+3)) K[X])
    (P : Matrix (Fin 6) (Fin (6*q+3)) K[X]) (i₀ : Fin (6*q+3)) :
    slEquationMatrix M P i₀*sixOutputTripleGradients q M P=0 := by
  funext t i
  exact congrFun (interiorFullGradient_kernel 3 3 q M P (sixOutputTriple i) i₀) t

theorem sixOutputTripleGradients_degree {K : Type*} [Field K]
    (M : Matrix (Fin (6*q+3)) (Fin (6*q+3)) K[X])
    (P : Matrix (Fin 6) (Fin (6*q+3)) K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) :
    DegreeBound (sixOutputTripleGradients q M P) (interiorFullWeight 3 3 q-1) := by
  intro t i
  exact interiorFullGradient_degree 3 3 q M P hM hP (sixOutputTriple i) t

variable {K : Type*} [Field K]

def genericSixOutputTripleMinors : Fin 20 →
    (AffineCoefficientField K (MatrixParameters (Fin (6*q+3)) (Fin 6)))[X] :=
  fun i => interiorFullMinor 3 3 q (genericAffineSquare K _ _)
    (genericAffineRows K _ _) (sixOutputTriple i)

def genericSixOutputTripleGradients := sixOutputTripleGradients q
  (genericAffineSquare K (Fin (6*q+3)) (Fin 6))
  (genericAffineRows K (Fin (6*q+3)) (Fin 6))

theorem generic_six_output_triple_gradient_derivation
    (t : SLInput (Fin (6*q+3)) (Fin 6)) :
    ∃ D : Derivation K (AffineCoefficientField K (MatrixParameters (Fin (6*q+3)) (Fin 6)))
        (AffineCoefficientField K (MatrixParameters (Fin (6*q+3)) (Fin 6))),
      ∀ i, polynomialCoefficientDerivation D (genericSixOutputTripleMinors (K:=K) q i)=
        genericSixOutputTripleGradients (K:=K) q t i := by
  obtain ⟨D,hD⟩ := generic_interior_full_gradient_derivation (K:=K) 3 3 q t
  exact ⟨D,fun i => hD (sixOutputTriple i)⟩

theorem generic_six_output_triple_gradients_selected (hq : 0<q)
    (t : SLInput (Fin (6*q+3)) (Fin 6)) (z : Option (Fin 3 × Fin 3)) :
    interiorScalarLiftMatrix 3 3 q (genericAffineSquare K _ _) (genericAffineRows K _ _) t z=
      (sixOutputTripleSelectedSign z :
        (AffineCoefficientField K (MatrixParameters (Fin (6*q+3)) (Fin 6)))[X]) *
        genericSixOutputTripleGradients (K:=K) q t (sixOutputTripleSelectedIndex z) := by
  obtain ⟨G,_,hfull⟩ := generic_six_output_triple_minor_realization (K:=K) q hq
  have he : interiorFullMinor 3 3 q (genericAffineSquare K _ _) (genericAffineRows K _ _)
        (interiorTerminalRow 3 3 z)=
      (sixOutputTripleSelectedSign z :
        (AffineCoefficientField K (MatrixParameters (Fin (6*q+3)) (Fin 6)))[X]) *
        genericSixOutputTripleMinors (K:=K) q (sixOutputTripleSelectedIndex z) := by
    unfold genericSixOutputTripleMinors
    rw [hfull,hfull]
    exact six_output_triple_selected_det G z
  obtain ⟨D,hD⟩ := generic_interior_full_gradient_derivation (K:=K) 3 3 q t
  have h := congrArg (polynomialCoefficientDerivation D) he
  simp only [genericSixOutputTripleMinors,Derivation.leibniz,Derivation.map_intCast,
    smul_zero,smul_eq_mul,mul_zero,add_zero,hD] at h
  simpa only [interiorFullGradient,interiorFullRow_selected,interiorScalarLiftMatrix,
    genericSixOutputTripleGradients,sixOutputTripleGradients] using h

theorem generic_six_output_triple_gradient_tangent (hq : 0<q) :
    sixOutputTriplePluckerTangent (genericSixOutputTripleMinors (K:=K) q)*
      (genericSixOutputTripleGradients (K:=K) q).transpose=0 := by
  obtain ⟨G,_,hfull⟩ := generic_six_output_triple_minor_realization (K:=K) q hq
  have he : genericSixOutputTripleMinors (K:=K) q=sixOutputTriplePluckerMinors G := by
    funext i
    exact hfull (sixOutputTriple i)
  have hp (r : Fin 20) :
      sixOutputTriplePluckerQuadratic (genericSixOutputTripleMinors (K:=K) q) r=0 := by
    rw [he]
    exact sixOutputTriplePluckerMinors_quadratic G r
  funext r t
  obtain ⟨D,hD⟩ := generic_six_output_triple_gradient_derivation (K:=K) q t
  have h := sixOutputTriplePluckerTangent_derivation (polynomialCoefficientDerivation D)
    (genericSixOutputTripleMinors (K:=K) q) hp
  have hd : (fun j => polynomialCoefficientDerivation D
      (genericSixOutputTripleMinors (K:=K) q j))=genericSixOutputTripleGradients (K:=K) q t :=
    funext hD
  rw [hd] at h
  exact congrFun h r

end FD56
