/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.WideObservabilityDescent
import FD56.Stabilizer.DiagonalizableObservabilityMinors

/-! Universal wide coprimality from a diagonalization over an injective state extension. -/

noncomputable section
namespace FD56
open Matrix MvPolynomial
variable {K L : Type*} [Field K] [Field L] {n m : ℕ}

theorem universal_wide_coprime_of_diagonalization
    (q : ℕ) (h : q*m < n+1)
    (φ : MvPolynomial (Fin (n+1) × Fin (n+1)) K →+* L) (hφ : Function.Injective φ)
    (S T : Matrix (Fin (n+1)) (Fin (n+1)) L) (hST : S*T=1) (hTS : T*S=1)
    (ev : Fin (n+1) → L) (hev : Function.Injective ev)
    (hMS : (cyclicVariableMatrix id).map φ * S = S * Matrix.diagonal ev)
    (g : MvPolynomial (MatrixParameters (Fin (n+1)) (Fin m)) K)
    (hd : ∀ r : Fin q × Fin m → Fin (n+1),
      g ∣ ((observabilityMatrix (universalSquare K (Fin (n+1)) (Fin m))
        (universalRows K (Fin (n+1)) (Fin m)) q).submatrix id r).det) : IsUnit g := by
  apply universal_wide_common_divisor_isUnit_of_coefficient_image_unit q h.le φ hφ g hd
  apply diagonalizable_wide_observability_common_divisor_isUnit
    ((cyclicVariableMatrix id).map φ) S T hST hTS ev hev hMS q
    (by simpa using h) (stateCoefficientMap φ g)
  intro r
  have hh := map_dvd (stateCoefficientMap φ) (hd r)
  rw [RingHom.map_det] at hh
  have hp := universal_state_extension_pair (m := m) φ
  have he : (((observabilityMatrix (universalSquare K (Fin (n+1)) (Fin m))
      (universalRows K (Fin (n+1)) (Fin m)) q).submatrix id r).map
      (stateCoefficientMap φ)) =
      (observabilityMatrix (((cyclicVariableMatrix id).map φ).map MvPolynomial.C)
        (Matrix.of fun a j => MvPolynomial.X (a,j)) q).submatrix id r := by
    rw [← Matrix.submatrix_map,observabilityMatrix_map,hp.1,hp.2]
    rfl
  change _ ∣ (((observabilityMatrix (universalSquare K (Fin (n+1)) (Fin m))
    (universalRows K (Fin (n+1)) (Fin m)) q).submatrix id r).map
    (stateCoefficientMap φ)).det at hh
  rwa [he] at hh

end FD56
