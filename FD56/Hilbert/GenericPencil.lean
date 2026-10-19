/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericPencil

/-! The generic SL pencil satisfies the nullity hypothesis of the polynomial
kernel criterion, including after extension of its coefficient field. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem generic_slHilbert_of_polynomial_basis {K L F : Type*} {r s k : Type}
    [Field K] [Field L] [Field F] [IsAlgClosed L]
    [Fintype r] [Fintype s] [Nonempty (r ⊕ s)] [Fintype k] [DecidableEq k]
    (q : ℕ) [DecidableEq (blockIndex (r ⊕ s) r (q + 1))] [DecidableEq (r ⊕ s)]
    (i₀ : blockIndex (r ⊕ s) r (q + 1))
    (θ : AffineCoefficientField K (MatrixParameters (blockIndex (r ⊕ s) r (q + 1))
      (r ⊕ s)) →+* L)
    (φ : L[X] →+* F) (hφ : Function.Injective φ)
    (M : Matrix (blockIndex (r ⊕ s) r (q + 1)) (blockIndex (r ⊕ s) r (q + 1)) L[X])
    (P : Matrix (r ⊕ s) (blockIndex (r ⊕ s) r (q + 1)) L[X])
    (hM : M = (genericAffineSquare K _ _).map (Polynomial.mapRingHom θ))
    (hP : P = (genericAffineRows K _ _).map (Polynomial.mapRingHom θ))
    (Z : Matrix (SLInput (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s)) k L[X])
    (e : k → ℕ) (hk : Fintype.card k = Fintype.card r * Fintype.card s + 1)
    (hAZ : slEquationMatrix M P i₀ * Z = 0)
    (hZ : ∀ i j, (Z i j).natDegree ≤ e j)
    (hpoint : ∀ x : L, Function.Injective (Z.map (Polynomial.evalRingHom x)).mulVec)
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (Z i j).coeff (e j)))) :
    HasHilbertProfile M P e := by
  apply slHilbert_of_polynomial_basis φ hφ M P i₀ Z e hAZ hZ hpoint _ hlead
  subst M P
  rw [← slEquationMatrix_map, Matrix.map_map, hk]
  exact generic_affine_sl_matrix_nullity_extension q i₀
    (φ.comp (Polynomial.mapRingHom θ)) (hφ.comp (Polynomial.map_injective θ θ.injective))

end FD56
