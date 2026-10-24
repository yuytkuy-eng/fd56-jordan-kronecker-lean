/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.HankelFrameCoordinates
import Mathlib.Algebra.Polynomial.Div

/-! Division at an evaluation point turns the truncated relations into a geometric recurrence. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {R : Type*} [CommRing R] [Nontrivial R] {b c : ℕ}

def hankelDividedVector (p : Fin c → R[X]) (z : R) : Fin c → R[X] :=
  fun i => p i /ₘ (X-C z)

omit [Nontrivial R] in
theorem hankelDividedVector_factor (p : Fin c → R[X]) (z : R)
    (hr : ∀ i, (p i).eval z=0) (i : Fin c) :
    (X-C z)*hankelDividedVector p z i=p i :=
  mul_divByMonic_eq_iff_isRoot.mpr (hr i)

theorem hankelDividedVector_degree (g : Fin c → ℕ)
    (p : Fin c → R[X]) (z : R) (hg : ∀ i, 0 < g i)
    (hp : ∀ i, (p i).natDegree ≤ g i) (i : Fin c) :
    (hankelDividedVector p z i).natDegree < g i := by
  rw [hankelDividedVector,natDegree_divByMonic _ (monic_X_sub_C z),natDegree_X_sub_C]
  have := hp i
  have := hg i
  omega

theorem hankelDividedVector_geometric (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R) (p : Fin c → R[X]) (z : R)
    (hg : ∀ i, 0 < g i) (hp : ∀ i, (p i).natDegree ≤ g i)
    (hr : ∀ i, (p i).eval z=0)
    (hz : ∀ j r, r+1 < h j → polynomialHankelAction (fun i => g i+1) a p j r=0)
    (j : Fin b) (r : ℕ) (hrange : r < h j) :
    polynomialHankelAction g a (hankelDividedVector p z) j r =
      z^r * polynomialHankelAction g a (hankelDividedVector p z) j 0 := by
  have hrec (s : ℕ) (hs : s+1 < h j) :
      polynomialHankelAction g a (hankelDividedVector p z) j (s+1) =
        z * polynomialHankelAction g a (hankelDividedVector p z) j s := by
    have he := polynomialHankelAction_shift g a (hankelDividedVector p z) z
      (fun i => coeff_eq_zero_of_natDegree_lt (hankelDividedVector_degree g p z hg hp i)) j s
    simp_rw [hankelDividedVector_factor p z hr] at he
    rw [hz j s hs] at he
    exact sub_eq_zero.mp he.symm
  induction r with
  | zero => simp
  | succ r ih =>
    rw [hrec r hrange,ih (by omega),pow_succ]
    ring

theorem hankelDividedVector_coordinates (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (hB : B * blockHankel h g a=1)
    (p : Fin c → R[X]) (z : R)
    (hg : ∀ i, 0 < g i) (hp : ∀ i, (p i).natDegree ≤ g i)
    (hr : ∀ i, (p i).eval z=0)
    (hz : ∀ j r, r+1 < h j → polynomialHankelAction (fun i => g i+1) a p j r=0) :
    hankelDividedVector p z = hankelCoefficientPolynomial g
      (B *ᵥ fun jr => z^jr.2.val *
        polynomialHankelAction g a (hankelDividedVector p z) jr.1 0) := by
  let q := hankelDividedVector p z
  let low : (Σ i, Fin (g i)) → R := fun is => (q is.1).coeff is.2.val
  have he : blockHankel h g a *ᵥ low = fun jr =>
      z^jr.2.val * polynomialHankelAction g a q jr.1 0 := by
    funext jr
    simpa only [Matrix.mulVec,dotProduct,Fintype.sum_sigma,blockHankel,low,q,
      polynomialHankelAction] using
      hankelDividedVector_geometric h g a p z hg hp hr hz jr.1 jr.2.val jr.2.isLt
  have hb : B *ᵥ (fun jr => z^jr.2.val * polynomialHankelAction g a q jr.1 0)=low := by
    rw [← he,Matrix.mulVec_mulVec,hB,Matrix.one_mulVec]
  change q=hankelCoefficientPolynomial g _
  rw [hb]
  funext i
  ext k
  by_cases hk : k < g i
  · exact (hankelCoefficientPolynomial_coeff g low i ⟨k,hk⟩).symm
  · rw [hankelCoefficientPolynomial_high_coeff g low i k (by omega)]
    exact coeff_eq_zero_of_natDegree_lt
      (lt_of_lt_of_le (hankelDividedVector_degree g p z hg hp i) (by omega))

def hankelKernelPolynomial (h : Fin b → ℕ) (g : Fin c → ℕ)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (z : R) (v : Fin b → R) : Fin c → R[X] :=
  hankelCoefficientPolynomial g (B *ᵥ fun jr => z^jr.2.val*v jr.1)

omit [Nontrivial R] in
theorem hankelKernelPolynomial_action (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (hB : blockHankel h g a*B=1) (z : R) (v : Fin b → R)
    (j : Fin b) (r : Fin (h j)) :
    polynomialHankelAction g a (hankelKernelPolynomial h g B z v) j r.val =
      z^r.val*v j := by
  rw [hankelKernelPolynomial,hankelCoefficientPolynomial_action,
    Matrix.mulVec_mulVec,hB,Matrix.one_mulVec]

theorem hankelKernelPolynomial_shift_zero (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (hB : blockHankel h g a*B=1) (z : R) (v : Fin b → R)
    (j : Fin b) (r : ℕ) (hr : r+1 < h j) :
    polynomialHankelAction (fun i => g i+1) a
      (fun i => (X-C z)*hankelKernelPolynomial h g B z v i) j r=0 := by
  rw [polynomialHankelAction_shift g a (hankelKernelPolynomial h g B z v) z
    (hankelCoefficientPolynomial_top_coeff g _) j r]
  have h0 := hankelKernelPolynomial_action h g a B hB z v j (⟨r,by omega⟩ : Fin (h j))
  have h1 := hankelKernelPolynomial_action h g a B hB z v j (⟨r+1,hr⟩ : Fin (h j))
  dsimp only at h0 h1
  rw [h0,h1,pow_succ]
  ring

theorem hankelKernelPolynomial_shift_injective (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (hB : blockHankel h g a*B=1) (hh : ∀ j, 0<h j) (z : R) :
    Function.Injective (fun v : Fin b → R =>
      fun i => (X-C z)*hankelKernelPolynomial h g B z v i) := by
  intro v w hvw
  have hq : hankelKernelPolynomial h g B z v=hankelKernelPolynomial h g B z w := by
    funext i
    have he := congrArg (fun f : R[X] => f /ₘ (X-C z)) (congrFun hvw i)
    simpa only [mul_divByMonic_cancel_left _ (monic_X_sub_C z)] using he
  funext j
  have he := congrArg (fun q => polynomialHankelAction g a q j 0) hq
  have hv := hankelKernelPolynomial_action h g a B hB z v j (⟨0,hh j⟩ : Fin (h j))
  have hw := hankelKernelPolynomial_action h g a B hB z w j (⟨0,hh j⟩ : Fin (h j))
  simpa only [Fin.val_zero,pow_zero,one_mul] using hv.symm.trans (he.trans hw)

theorem hankelFrame_evaluation_zero_iff (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (hBH : B*blockHankel h g a=1) (hHB : blockHankel h g a*B=1)
    (hh : ∀ j, 0<h j) (hg : ∀ i, 0<g i)
    (p : Fin c → R[X]) (z : R) (hp : ∀ i, (p i).natDegree ≤ g i)
    (hz : ∀ j r, r+1 < h j → polynomialHankelAction (fun i => g i+1) a p j r=0) :
    (∀ i, (p i).eval z=0) ↔ ∃! v : Fin b → R,
      p=fun i => (X-C z)*hankelKernelPolynomial h g B z v i := by
  constructor
  · intro hr
    let v := fun j => polynomialHankelAction g a (hankelDividedVector p z) j 0
    have he : p=fun i => (X-C z)*hankelKernelPolynomial h g B z v i := by
      funext i
      rw [← hankelDividedVector_factor p z hr i,
        hankelDividedVector_coordinates h g a B hBH p z hg hp hr hz]
      rfl
    refine ⟨v,he,?_⟩
    intro w hw
    exact hankelKernelPolynomial_shift_injective h g a B hHB hh z (hw.symm.trans he)
  · rintro ⟨v,hv,_⟩ i
    rw [hv]
    simp

end FD56
