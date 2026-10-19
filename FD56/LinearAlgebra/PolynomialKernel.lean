/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialBezout
import FD56.LinearAlgebra.PredictableDegree

/-! A complete bounded-degree kernel description from explicit matrix criteria.
Applications must verify pointwise rank, field nullity, and the leading matrix. -/

namespace FD56
open Polynomial Matrix

theorem bounded_polynomial_kernel_coordinates
    {K F a b k : Type*} [Field K] [IsAlgClosed K] [Field F]
    [Fintype a] [Fintype b] [Fintype k]
    [DecidableEq a] [DecidableEq b] [DecidableEq k]
    (φ : K[X] →+* F) (hφ : Function.Injective φ)
    (A : Matrix a b K[X]) (Z : Matrix b k K[X]) (e : k → ℕ)
    (hAZ : A * Z = 0)
    (hpoint : ∀ x : K, Function.Injective (Z.map (Polynomial.evalRingHom x)).mulVec)
    (hdim : Module.finrank F (LinearMap.ker (Matrix.toLin' (A.map φ))) = Fintype.card k)
    (hZ : ∀ i j, (Z i j).natDegree ≤ e j)
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (Z i j).coeff (e j))))
    (Y : Matrix b Unit K[X]) (d : ℕ) :
    (A * Y = 0 ∧ ∀ i, (Y i ()).natDegree ≤ d) ↔
      ∃! c : Matrix k Unit K[X], Y = Z * c ∧
        ∀ j, c j () = 0 ∨ (e j ≤ d ∧ (c j ()).natDegree ≤ d - e j) := by
  constructor
  · rintro ⟨hY, hdeg⟩
    obtain ⟨c, hc, huniq⟩ :=
      (polynomial_kernel_basis_of_pointwise_rank_and_nullity φ hφ A Z hAZ hpoint hdim Y).mp hY
    refine ⟨c, ⟨hc, ?_⟩, fun c' hc' => huniq c' hc'.1⟩
    apply (polynomial_combination_degree_iff Z e (fun j => c j ()) d hZ hlead).mp
    intro i
    change ((Z * c) i ()).natDegree ≤ d
    rw [← hc]
    exact hdeg i
  · rintro ⟨c, ⟨hc, hbound⟩, _⟩
    constructor
    · rw [hc, ← Matrix.mul_assoc, hAZ, Matrix.zero_mul]
    · have hb := (polynomial_combination_degree_iff Z e (fun j => c j ()) d hZ hlead).mpr hbound
      intro i
      rw [hc]
      exact hb i

end FD56
