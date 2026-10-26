/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.TwoOutputOddSLClosure
import FD56.Hilbert.SLScalarCrossVanishing
import FD56.Hilbert.TwoOutputOddGL

/-! An explicit scalar-lift criterion for the actual generic odd-state two-output SL pencil. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

theorem generic_two_output_odd_gl_critical_vanishing (q : ℕ) (hq : 0<q) :
    Module.finrank (AffineCoefficientField K (MatrixParameters (Fin (2*q+1)) (Fin 2)))
      (polynomialKernelAtDegree (glEquationMatrix
        (genericAffineSquare K (Fin (2*q+1)) (Fin 2))
        (genericAffineRows K (Fin (2*q+1)) (Fin 2))) (2*(q*(q+2)-1)+2))=0 := by
  have h := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
    (generic_two_output_odd_gl_minimal_degrees (K := K) (n := Fin (2*q+1))
      (m := Fin 2) q (by simp) (by simp)) (2*(q*(q+2)-1)+2)
  rw [h]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  have hp : 0<q*(q+2) := Nat.mul_pos hq (by omega)
  have he : 2*q^2+4*q+1=2*(q*(q+2))+1 := by ring
  rw [he]
  omega

theorem generic_two_output_odd_sl_scalar_criterion
    (q : ℕ) (hq : 0<q) (i₀ : Fin (2*q+1))
    (Z₀ Z₁ : SLInput (Fin (2*q+1)) (Fin 2) →
      (AffineCoefficientField K (MatrixParameters (Fin (2*q+1)) (Fin 2)))[X])
    (p₀ p₁ : (AffineCoefficientField K (MatrixParameters (Fin (2*q+1)) (Fin 2)))[X])
    (h₀ : glEquationMatrix (genericAffineSquare K (Fin (2*q+1)) (Fin 2))
      (genericAffineRows K (Fin (2*q+1)) (Fin 2)) *ᵥ Z₀ =
        p₀ • glScalarVector _ (Fin (2*q+1)) (Fin 2))
    (h₁ : glEquationMatrix (genericAffineSquare K (Fin (2*q+1)) (Fin 2))
      (genericAffineRows K (Fin (2*q+1)) (Fin 2)) *ᵥ Z₁ =
        p₁ • glScalarVector _ (Fin (2*q+1)) (Fin 2))
    (hZ₀ : ∀ j, (Z₀ j).natDegree ≤ q*(q+2))
    (hZ₁ : ∀ j, (Z₁ j).natDegree ≤ q*(q+2))
    (hp₀ : p₀.natDegree ≤ q*(q+2)+1) (hp₁ : p₁.natDegree ≤ q*(q+2)+1)
    (hcross : p₁ • Z₀-p₀ • Z₁ ≠ 0) :
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (2*q+1)) (Fin 2))
      (genericAffineRows K (Fin (2*q+1)) (Fin 2)) i₀) [q*(q+2),q*(q+2)] := by
  apply generic_two_output_odd_sl_kronecker_of_vanishing q hq i₀
  have hp : 0<q*(q+2) := Nat.mul_pos hq (by omega)
  have he : q*(q+2)-1+1=q*(q+2) := Nat.sub_add_cancel hp
  apply slHilbert_zero_of_scalar_lifts _ _ i₀ (q*(q+2)-1)
    (genericAffineSquare_degree _ _ _) (genericAffineRows_degree _ _ _)
    Z₀ Z₁ p₀ p₁ h₀ h₁
  · simpa only [he] using hZ₀
  · simpa only [he] using hZ₁
  · exact hp₀.trans (by omega)
  · exact hp₁.trans (by omega)
  · exact hcross
  · exact generic_two_output_odd_gl_critical_vanishing q hq

end FD56
