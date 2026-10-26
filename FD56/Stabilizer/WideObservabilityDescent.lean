/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.StateOnlyObservabilityDivisors
import FD56.LinearAlgebra.StateVariableDescent

/-! Descent of universal wide observability divisors from an injective coefficient extension. -/

noncomputable section
namespace FD56
open Matrix MvPolynomial
variable {K L : Type*} [Field K] [Field L] {n m : ℕ}

theorem universal_state_extension_pair
    (φ : MvPolynomial (Fin (n+1) × Fin (n+1)) K →+* L) :
    (universalSquare K (Fin (n+1)) (Fin m)).map (stateCoefficientMap φ) =
      (Matrix.of fun i j => φ (MvPolynomial.X (i,j))).map MvPolynomial.C ∧
    (universalRows K (Fin (n+1)) (Fin m)).map (stateCoefficientMap φ) =
      (Matrix.of fun a j => MvPolynomial.X (a,j)) := by
  constructor <;> funext i j
  · exact stateCoefficientMap_state φ (i,j)
  · exact stateCoefficientMap_output φ (i,j)

theorem universal_wide_common_divisor_isUnit_of_coefficient_image_unit
    (q : ℕ) (h : q*m ≤ n+1)
    (φ : MvPolynomial (Fin (n+1) × Fin (n+1)) K →+* L) (hφ : Function.Injective φ)
    (g : MvPolynomial (MatrixParameters (Fin (n+1)) (Fin m)) K)
    (hd : ∀ r : Fin q × Fin m → Fin (n+1),
      g ∣ ((observabilityMatrix (universalSquare K (Fin (n+1)) (Fin m))
        (universalRows K (Fin (n+1)) (Fin m)) q).submatrix id r).det)
    (hg : IsUnit (stateCoefficientMap φ g)) : IsUnit g := by
  obtain ⟨d,rfl⟩ := stateCoefficientMap_isUnit_implies_state_only φ hφ g hg
  exact (universal_observability_state_divisor_isUnit q h d hd).map
    (MvPolynomial.rename Sum.inl).toRingHom

end FD56
