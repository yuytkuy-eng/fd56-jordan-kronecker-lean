/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.HankelScalarObstruction
import FD56.LinearAlgebra.HankelScalarSelector

/-! A coefficient selector for scalar lifts through the universal Hankel frame. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable (K : Type*) [Field K] {b c t : ℕ}

def hankelScalarHeights (h : Fin b → ℕ) (g : Fin c → ℕ)
    (e : Fin t ≃ Fin b × Fin c) (d : ℕ) : Fin t → ℕ :=
  fun l => h (e l).1+g (e l).2-(d+2)

theorem universalHankel_scalar_selector (h : Fin b → ℕ) (g : Fin c → ℕ)
    (e : Fin t ≃ Fin b × Fin c)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) (HankelCoefficientField K b c))
    (hBH : B*blockHankel h g (universalHankelCoefficients K b c)=1)
    (hHB : blockHankel h g (universalHankelCoefficients K b c)*B=1)
    (hh : ∀ j, 0<h j) (hg : ∀ i, 0<g i) (hsum : ∑ i, g i=∑ j, h j)
    (d : ℕ) (hd : ∀ i, g i≤d+1) (p : (HankelCoefficientField K b c)[X])
    (hp : p.natDegree≤d+1)
    (hlift : ∀ i, ∃ x : Fin c ⊕ Fin b → (HankelCoefficientField K b c)[X],
      (∀ w, (x w).natDegree≤d+1-g i) ∧
      hankelFrame h g (universalHankelCoefficients K b c) B *ᵥ x=Pi.single i p)
    (hselect : ∀ q : Fin (d+2-∑ l, hankelScalarHeights h g e d l),
      p.coeff ((∑ l, hankelScalarHeights h g e d l)+q.val)=0) : p=0 := by
  let f := hankelScalarHeights h g e d
  let v : Fin (d+2) → HankelCoefficientField K b c := fun s => p.coeff s.val
  have hz := (hankelFrame_scalar_lift_iff h g (universalHankelCoefficients K b c) B
    hBH hHB hh hg hsum d hd p hp).mp hlift
  have he : Matrix.fromRows
      ((universalHankelStackPolynomial K e f (d+2)).map (algebraMap _ (HankelCoefficientField K b c)))
      (hankelTailSelector (∑ l, f l) (d+2)) *ᵥ v=0 := by
    funext w
    cases w with
    | inl lr =>
      exact hz (e lr.1).2 (e lr.1).1 lr.2.val lr.2.isLt
    | inr q =>
      change (hankelTailSelector (∑ l, f l) (d+2) *ᵥ v) q=0
      rw [hankelTailSelector_mulVec]
      exact hselect q
  have hv : v=0 := (universalHankelStack_with_tail_injective (K := K) e f (d+2))
    (he.trans (Matrix.mulVec_zero _).symm)
  ext s
  rw [coeff_zero]
  by_cases hs : s<d+2
  · exact congrFun hv ⟨s,hs⟩
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

end FD56
