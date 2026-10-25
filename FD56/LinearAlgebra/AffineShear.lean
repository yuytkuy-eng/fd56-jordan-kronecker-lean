/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.MvPolynomial.Equiv

/-! An invertible affine substitution on two independent sets of variables. -/

namespace FD56
open MvPolynomial

variable {R ι : Type*} [CommRing R]

noncomputable def affineShearHom (c : R) :
    MvPolynomial (ι ⊕ ι) R →ₐ[R] MvPolynomial (ι ⊕ ι) R :=
  aeval (Sum.elim (fun i => X (Sum.inl i) + C c * X (Sum.inr i))
    (fun i => X (Sum.inr i)))

theorem affineShearHom_comp_neg (c : R) :
    (affineShearHom (ι := ι) c).comp (affineShearHom (-c)) = AlgHom.id R _ := by
  ext i
  cases i <;> simp [affineShearHom, map_add, map_mul]

noncomputable def affineShear (c : R) :
    MvPolynomial (ι ⊕ ι) R ≃ₐ[R] MvPolynomial (ι ⊕ ι) R :=
  AlgEquiv.ofAlgHom (affineShearHom c) (affineShearHom (-c))
    (affineShearHom_comp_neg c)
    (by simpa using affineShearHom_comp_neg (ι := ι) (-c))

theorem affineShear_inl (c : R) (i : ι) :
    affineShear c (X (Sum.inl i)) = X (Sum.inl i) + C c * X (Sum.inr i) := by
  simp [affineShear, affineShearHom]

theorem affineShear_inr (c : R) (i : ι) :
    affineShear c (X (Sum.inr i)) = X (Sum.inr i) := by
  simp [affineShear, affineShearHom]

/-- A ring automorphism preserves the absence of a common nonunit divisor. -/
theorem common_divisor_isUnit_under_equiv {A B κ : Type*} [CommSemiring A] [CommSemiring B]
    (e : A ≃+* B) (f : κ → A)
    (h : ∀ d, (∀ i, d ∣ f i) → IsUnit d) :
    ∀ d, (∀ i, d ∣ e (f i)) → IsUnit d := by
  intro d hd
  have hu : IsUnit (e.symm d) := h _ (fun i => by
    simpa using map_dvd e.symm.toRingHom (hd i))
  simpa using hu.map e.toRingHom

theorem affineShear_common_divisor_isUnit {κ : Type*} (c : R)
    (f : κ → MvPolynomial (ι ⊕ ι) R)
    (h : ∀ d, (∀ i, d ∣ f i) → IsUnit d) :
    ∀ d, (∀ i, d ∣ affineShear c (f i)) → IsUnit d :=
  common_divisor_isUnit_under_equiv (affineShear c).toRingEquiv f h

end FD56
