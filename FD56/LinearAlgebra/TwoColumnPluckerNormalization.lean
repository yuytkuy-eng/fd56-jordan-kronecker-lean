/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic

/-! Four coefficient constraints for balanced two-column polynomial frames.
The common minor scale is retained; no independence of normalized entries is assumed. -/

noncomputable section
namespace FD56
open Polynomial
variable {K n : Type*} [Field K]

private theorem sub_degree {p q : K[X]} {d : ℕ}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) :
    (p-q).natDegree ≤ d := (natDegree_sub_le p q).trans (max_le hp hq)

theorem two_column_equal_normalization (u v : n → K[X]) (a : ℕ) (i₀ i₁ : n)
    (hu : ∀ i, (u i).natDegree ≤ a) (hv : ∀ i, (v i).natDegree ≤ a)
    (hdet : (u i₀).coeff a*(v i₁).coeff a-(v i₀).coeff a*(u i₁).coeff a ≠ 0) :
    ∃ (u' v' : n → K[X]) (c : K), c ≠ 0 ∧
      (∀ i, (u' i).natDegree ≤ a) ∧ (∀ i, (v' i).natDegree ≤ a) ∧
      (u' i₀).coeff a=1 ∧ (u' i₁).coeff a=0 ∧
      (v' i₀).coeff a=0 ∧ (v' i₁).coeff a=1 ∧
      ∀ i j, u i*v j-u j*v i=C c*(u' i*v' j-u' j*v' i) := by
  let α := (u i₀).coeff a
  let β := (v i₀).coeff a
  let γ := (u i₁).coeff a
  let δ := (v i₁).coeff a
  let c := α*δ-β*γ
  have hc : c ≠ 0 := hdet
  let p : n → K[X] := fun i => C δ*u i-C γ*v i
  let q : n → K[X] := fun i => C α*v i-C β*u i
  let u' : n → K[X] := fun i => C c⁻¹*p i
  let v' : n → K[X] := fun i => C c⁻¹*q i
  refine ⟨u',v',c,hc,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    exact (natDegree_C_mul_le _ _).trans
      (sub_degree ((natDegree_C_mul_le _ _).trans (hu i))
        ((natDegree_C_mul_le _ _).trans (hv i)))
  · intro i
    exact (natDegree_C_mul_le _ _).trans
      (sub_degree ((natDegree_C_mul_le _ _).trans (hv i))
        ((natDegree_C_mul_le _ _).trans (hu i)))
  · change (C c⁻¹*(C δ*u i₀-C γ*v i₀)).coeff a=1
    simp only [coeff_C_mul,coeff_sub]
    change c⁻¹*(δ*α-γ*β)=1
    rw [show δ*α-γ*β=c by dsimp [c]; ring]
    exact inv_mul_cancel₀ hc
  · change (C c⁻¹*(C δ*u i₁-C γ*v i₁)).coeff a=0
    simp only [coeff_C_mul,coeff_sub]
    change c⁻¹*(δ*γ-γ*δ)=0
    ring
  · change (C c⁻¹*(C α*v i₀-C β*u i₀)).coeff a=0
    simp only [coeff_C_mul,coeff_sub]
    change c⁻¹*(α*β-β*α)=0
    ring
  · change (C c⁻¹*(C α*v i₁-C β*u i₁)).coeff a=1
    simp only [coeff_C_mul,coeff_sub]
    exact inv_mul_cancel₀ hc
  · intro i j
    have hpq : p i*q j-p j*q i=C c*(u i*v j-u j*v i) := by
      dsimp [p,q,c]
      simp only [map_sub,map_mul]
      ring
    change _=C c*((C c⁻¹*p i)*(C c⁻¹*q j)-(C c⁻¹*p j)*(C c⁻¹*q i))
    rw [show (C c⁻¹*p i)*(C c⁻¹*q j)-(C c⁻¹*p j)*(C c⁻¹*q i)=
      C c⁻¹*C c⁻¹*(p i*q j-p j*q i) by ring,hpq]
    simp [← mul_assoc,← map_mul,hc]

theorem two_column_adjacent_normalization (u v : n → K[X]) (a : ℕ) (i₀ i₁ : n)
    (hu : ∀ i, (u i).natDegree ≤ a) (hv : ∀ i, (v i).natDegree ≤ a+1)
    (hα : (u i₀).coeff a ≠ 0)
    (hdet : (u i₀).coeff a*(v i₁).coeff (a+1)-
      (v i₀).coeff (a+1)*(u i₁).coeff a ≠ 0) :
    ∃ (u' v' : n → K[X]) (c : K), c ≠ 0 ∧
      (∀ i, (u' i).natDegree ≤ a) ∧ (∀ i, (v' i).natDegree ≤ a+1) ∧
      (u' i₀).coeff a=1 ∧ (v' i₀).coeff (a+1)=0 ∧
      (v' i₀).coeff a=0 ∧ (v' i₁).coeff (a+1)=1 ∧
      ∀ i j, u i*v j-u j*v i=C c*(u' i*v' j-u' j*v' i) := by
  let α := (u i₀).coeff a
  have hα' : α ≠ 0 := hα
  let β := (v i₀).coeff (a+1)/α
  let w : n → K[X] := fun i => v i-C β*(X*u i)
  let γ := (w i₀).coeff a/α
  let z : n → K[X] := fun i => w i-C γ*u i
  let δ := (z i₁).coeff (a+1)
  have huhigh (i : n) : (u i).coeff (a+1)=0 :=
    coeff_eq_zero_of_natDegree_lt ((hu i).trans_lt (by omega))
  have hzTop (i : n) : (z i).coeff (a+1)=
      (v i).coeff (a+1)-β*(u i).coeff a := by
    simp [z,w,coeff_sub,coeff_C_mul,coeff_X_mul,huhigh]
  have hδ : δ ≠ 0 := by
    intro hzero
    have hd : α*δ=(u i₀).coeff a*(v i₁).coeff (a+1)-
        (v i₀).coeff (a+1)*(u i₁).coeff a := by
      dsimp [δ]
      rw [hzTop]
      dsimp [β,α]
      field_simp
      ring
    rw [hzero,mul_zero] at hd
    exact hdet hd.symm
  let u' : n → K[X] := fun i => C α⁻¹*u i
  let v' : n → K[X] := fun i => C δ⁻¹*z i
  refine ⟨u',v',α*δ,mul_ne_zero hα' hδ,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    exact (natDegree_C_mul_le _ _).trans (hu i)
  · intro i
    apply (natDegree_C_mul_le _ _).trans
    apply sub_degree
    · apply sub_degree (hv i)
      apply (natDegree_C_mul_le _ _).trans
      exact natDegree_mul_le.trans (by have := hu i; simp only [natDegree_X]; omega)
    · exact (natDegree_C_mul_le _ _).trans ((hu i).trans (by omega))
  · simpa only [u',coeff_C_mul] using inv_mul_cancel₀ hα'
  · change (C δ⁻¹*z i₀).coeff (a+1)=0
    rw [coeff_C_mul,hzTop]
    change δ⁻¹*((v i₀).coeff (a+1)-((v i₀).coeff (a+1)/α)*α)=0
    simp [hα']
  · change (C δ⁻¹*(w i₀-C γ*u i₀)).coeff a=0
    simp only [coeff_C_mul,coeff_sub]
    change δ⁻¹*((w i₀).coeff a-((w i₀).coeff a/α)*α)=0
    simp [hα']
  · change (C δ⁻¹*z i₁).coeff (a+1)=1
    simpa only [coeff_C_mul] using inv_mul_cancel₀ hδ
  · intro i j
    have hz : u i*z j-u j*z i=u i*v j-u j*v i := by
      dsimp [z,w]
      ring
    change _=C (α*δ)*((C α⁻¹*u i)*(C δ⁻¹*z j)-(C α⁻¹*u j)*(C δ⁻¹*z i))
    rw [show (C α⁻¹*u i)*(C δ⁻¹*z j)-(C α⁻¹*u j)*(C δ⁻¹*z i)=
      C α⁻¹*C δ⁻¹*(u i*z j-u j*z i) by ring,hz]
    rw [← mul_assoc,← mul_assoc,← map_mul,← map_mul,
      show α*δ*α⁻¹*δ⁻¹=1 by field_simp]
    simp

end FD56
