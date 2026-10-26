/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic

/-! Weighted leading coefficients detect unit common divisors, allowing zero weights. -/

noncomputable section
namespace FD56

variable {K σ : Type*} [Field K]

def weightedVariableLift (w : σ → ℕ) :
    MvPolynomial σ K →+* Polynomial (MvPolynomial σ K) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ w i)

theorem weightedVariableLift_eval_one (w : σ → ℕ) (p : MvPolynomial σ K) :
    Polynomial.eval 1 (weightedVariableLift w p) = p := by
  have h : (Polynomial.evalRingHom (1 : MvPolynomial σ K)).comp (weightedVariableLift w) =
      RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [weightedVariableLift]
    · intro i
      simp [weightedVariableLift]
  exact RingHom.congr_fun h p

theorem weightedVariableLift_augmentation (w : σ → ℕ) (p : MvPolynomial σ K) :
    (weightedVariableLift w p).map (MvPolynomial.eval₂Hom (RingHom.id K) (fun _ => 0)) =
      Polynomial.C (MvPolynomial.eval₂Hom (RingHom.id K) (fun _ => 0) p) := by
  let ε : MvPolynomial σ K →+* K := MvPolynomial.eval₂Hom (RingHom.id K) (fun _ => 0)
  have h : (Polynomial.mapRingHom ε).comp (weightedVariableLift w) = Polynomial.C.comp ε := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [weightedVariableLift, ε]
    · intro i
      simp [weightedVariableLift, ε]
  exact RingHom.congr_fun h p

theorem isUnit_of_weightedVariableLift_leadingCoeff_isUnit (w : σ → ℕ)
    (p : MvPolynomial σ K) (h : IsUnit (weightedVariableLift w p).leadingCoeff) : IsUnit p := by
  let ε : MvPolynomial σ K →+* K := MvPolynomial.eval₂Hom (RingHom.id K) (fun _ => 0)
  have hz : ε (weightedVariableLift w p).leadingCoeff ≠ 0 := (h.map ε).ne_zero
  have hd : (weightedVariableLift w p).natDegree = 0 := by
    have he := Polynomial.natDegree_map_of_leadingCoeff_ne_zero ε hz
    rw [weightedVariableLift_augmentation, Polynomial.natDegree_C] at he
    exact he.symm
  have hc := Polynomial.eq_C_of_natDegree_eq_zero hd
  have he := congrArg (Polynomial.eval (1 : MvPolynomial σ K)) hc
  rw [weightedVariableLift_eval_one, Polynomial.eval_C] at he
  have hl : (weightedVariableLift w p).leadingCoeff = (weightedVariableLift w p).coeff 0 := by
    rw [Polynomial.leadingCoeff, hd]
  rw [he, ← hl]
  exact h

theorem weighted_leading_common_divisor_isUnit (w : σ → ℕ) (f g p : MvPolynomial σ K)
    (hc : ∀ a : MvPolynomial σ K,
      a ∣ (weightedVariableLift w f).leadingCoeff →
      a ∣ (weightedVariableLift w g).leadingCoeff → IsUnit a)
    (hf : p ∣ f) (hg : p ∣ g) : IsUnit p := by
  apply isUnit_of_weightedVariableLift_leadingCoeff_isUnit w p
  exact hc _ (Polynomial.leadingCoeff_dvd_leadingCoeff (map_dvd (weightedVariableLift w) hf))
    (Polynomial.leadingCoeff_dvd_leadingCoeff (map_dvd (weightedVariableLift w) hg))

end FD56
