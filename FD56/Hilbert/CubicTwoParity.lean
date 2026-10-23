/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.CubicTwoCompletion

/-! Scalar obstruction induction for the two parity classes. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K m r : Type*} [Field K] [CharZero K] [Fintype m] [Fintype r]
  [DecidableEq m] [DecidableEq r]

namespace CubicTwoCompletion
variable {alpha : r → ℕ} {b : ℕ} {W : Matrix (Fin 2) (Fin 2) K[X]}

private theorem scaled_coordinates (s c : K[X])
    (U Q B : Matrix (Fin 2) (Fin 2) K[X]) (hW : s • W=B)
    (hQ : Q=((X^3 : K[X]) • U+c • 1)*W) :
    s • Q=(X^3 : K[X]) • (U*B)+c • B := by
  rw [hQ]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, smul_add]
  rw [smul_comm s (X^3), smul_comm s c, ← Matrix.mul_smul, hW]

theorem even_zero_extend (C : CubicTwoCompletion (m := m) alpha b 0 W)
    (hW : (4 : K[X]) • W=mixedOneTwoEvenAdjugate)
    (hd : ∀ i, alpha i+1≤b) (hzero : C.ScalarZero b) :
    C.extend.ScalarZero (b+3) := by
  intro E c hE hc hrel
  obtain ⟨Q,hQ,hQdeg⟩ := C.new_coordinate_degree E c (b+1) hrel (by
    intro i x
    have hh := hE (Sum.inl i) (Sum.inr x)
    simpa only [Sum.elim_inl] using (show (E (Sum.inl i) (Sum.inr x)).natDegree≤b+1 from by
      simp only [Sum.elim_inl] at hh; omega))
  have hsmall : DegreeBound Q 1 := by
    intro i j
    rcases hQdeg i j with hz | ⟨_,hh⟩
    · simp [hz]
    · simpa using hh
  have hlow := mixedOneTwoEven_jet_zero Q (E.submatrix Sum.inl Sum.inl *
    mixedOneTwoEvenAdjugate) c hsmall (scaled_coordinates 4 c _ Q _ hW hQ)
  obtain ⟨c',hfactor⟩ := Polynomial.X_pow_dvd_iff.mpr hlow
  obtain ⟨F,hF,hc',hFG⟩ := C.scalar_descent b hd E c c' hE (by omega) hfactor hrel
  rw [hfactor, hzero F c' hF hc' hFG, mul_zero]

theorem odd_zero_extend (C : CubicTwoCompletion (m := m) alpha b 1 W)
    (hW : (8 : K[X]) • W=mixedOneTwoOddAdjugate)
    (hd : ∀ i, alpha i+1≤b) (hzero : C.ScalarZero b) :
    C.extend.ScalarZero (b+3) := by
  intro E c hE hc hrel
  obtain ⟨Q,hQ,hQdeg⟩ := C.new_coordinate_degree E c (b+1) hrel (by
    intro i x
    have hh := hE (Sum.inl i) (Sum.inr x)
    simp only [Sum.elim_inl] at hh
    exact hh.trans (by omega))
  have hsmall : ∀ i, (Q i 1).natDegree≤0 := by
    intro i
    rcases hQdeg i 1 with hz | ⟨_,hh⟩
    · simp [hz]
    · simpa using hh
  have hlow := mixedOneTwoOdd_jet_zero Q (E.submatrix Sum.inl Sum.inl *
    mixedOneTwoOddAdjugate) c hsmall (scaled_coordinates 8 c _ Q _ hW hQ)
  obtain ⟨c',hfactor⟩ := Polynomial.X_pow_dvd_iff.mpr hlow
  obtain ⟨F,hF,hc',hFG⟩ := C.scalar_descent b hd E c c' hE (by omega) hfactor hrel
  rw [hfactor, hzero F c' hF hc' hFG, mul_zero]

theorem even_selector_extend {t : Type*} (C : CubicTwoCompletion (m := m) alpha b 0 W)
    (hd : ∀ i, alpha i+1≤b+1) (f : t → ℕ) (hzero : C.ScalarSelector (b+1) f) :
    C.extend.ScalarSelector (b+4) (Sum.elim (fun j : Fin 3 => j.val) (fun j => f j+3)) := by
  intro E c hE hc hrel hsel
  have hlow : ∀ k<3, c.coeff k=0 := fun k hk => hsel (Sum.inl ⟨k,hk⟩)
  obtain ⟨c',hfactor⟩ := Polynomial.X_pow_dvd_iff.mpr hlow
  obtain ⟨F,hF,hc',hFG⟩ := C.scalar_descent (b+1) hd E c c'
    (by simpa [Nat.add_assoc] using hE) (by omega) hfactor hrel
  have hc'zero := hzero F c' hF hc' hFG (by
    intro j
    simpa only [Sum.elim_inr, hfactor, coeff_X_pow_mul] using hsel (Sum.inr j))
  rw [hfactor,hc'zero,mul_zero]

theorem odd_selector_extend {t : Type*} (C : CubicTwoCompletion (m := m) alpha b 1 W)
    (hW : (8 : K[X]) • W=mixedOneTwoOddAdjugate)
    (hd : ∀ i, alpha i+1≤b+1) (f : t → ℕ) (hzero : C.ScalarSelector (b+1) f) :
    C.extend.ScalarSelector (b+4) (Sum.elim (fun _ : Fin 1 => 0) (fun j => f j+3)) := by
  intro E c hE hc hrel hsel
  obtain ⟨Q,hQ,hQdeg⟩ := C.new_coordinate_degree E c (b+2) hrel (by
    intro i x
    have hh := hE (Sum.inl i) (Sum.inr x)
    simp only [Sum.elim_inl] at hh
    exact hh.trans (by omega))
  have hsmall : ∀ i, (Q i 1).natDegree≤1 := by
    intro i
    rcases hQdeg i 1 with hz | ⟨_,hh⟩
    · simp [hz]
    · simpa using hh
  have hlow := mixedOneTwoOdd_jet_zero_of_constant Q (E.submatrix Sum.inl Sum.inl *
    mixedOneTwoOddAdjugate) c hsmall (hsel (Sum.inl 0))
    (scaled_coordinates 8 c _ Q _ hW hQ)
  obtain ⟨c',hfactor⟩ := Polynomial.X_pow_dvd_iff.mpr hlow
  obtain ⟨F,hF,hc',hFG⟩ := C.scalar_descent (b+1) hd E c c'
    (by simpa [Nat.add_assoc] using hE) (by omega) hfactor hrel
  have hc'zero := hzero F c' hF hc' hFG (by
    intro j
    simpa only [Sum.elim_inr, hfactor, coeff_X_pow_mul] using hsel (Sum.inr j))
  rw [hfactor,hc'zero,mul_zero]

end CubicTwoCompletion
end FD56
