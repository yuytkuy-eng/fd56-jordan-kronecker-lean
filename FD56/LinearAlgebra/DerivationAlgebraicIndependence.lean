/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.Tactic

/-! Coordinate-separating derivations certify algebraic independence in characteristic zero. -/

noncomputable section
namespace FD56
open MvPolynomial
open scoped BigOperators
variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]

private theorem pderiv_totalDegree_lt (p : MvPolynomial ι K) (i : ι)
    (hp : 0<p.totalDegree) : (pderiv i p).totalDegree<p.totalDegree := by
  classical
  have he : pderiv i p = ∑ s ∈ p.support,
      monomial (s-Finsupp.single i 1) (p.coeff s * s i) := by
    calc
      pderiv i p = pderiv i (∑ s ∈ p.support,monomial s (p.coeff s)) :=
        congrArg (pderiv i) p.as_sum
      _ = _ := by simp only [map_sum,pderiv_monomial]
  rw [he]
  have hb : (∑ s ∈ p.support,
      monomial (s-Finsupp.single i 1) (p.coeff s * s i)).totalDegree≤p.totalDegree-1 := by
    apply totalDegree_finsetSum_le
    intro s hs
    by_cases hi : s i=0
    · simp [hi]
    have hsum : (s-Finsupp.single i 1).sum (fun _ e => e)+1=s.sum (fun _ e => e) := by
      calc
        _ = ((s-Finsupp.single i 1)+Finsupp.single i 1).sum (fun _ e => e) := by
          simp [Finsupp.sum_add_index']
        _ = _ := by rw [Finsupp.sub_add_single_one_cancel hi]
    have hd := le_totalDegree hs
    exact (totalDegree_monomial_le _ _).trans (by simpa only [Function.id_def] using (show
      (s-Finsupp.single i 1).sum (fun _ e => e)≤p.totalDegree-1 by omega))
  omega

private theorem coefficient_X_pderiv (p : MvPolynomial ι K) (i : ι) (d : ι →₀ ℕ) :
    (X i*pderiv i p).coeff d=(d i : K)*p.coeff d := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial s r =>
      rw [X_mul_pderiv_monomial,coeff_smul]
      by_cases hs : s=d
      · subst s
        simp [coeff_smul,nsmul_eq_mul]
      · simp [coeff_smul,coeff_monomial,hs,Ne.symm hs]
  | add p q hp hq =>
      simp only [map_add,mul_add,coeff_add,hp,hq]

private theorem eq_constant_of_pderiv_zero [CharZero K] (p : MvPolynomial ι K)
    (hp : ∀ i,pderiv i p=0) : p=C (p.coeff 0) := by
  classical
  ext d
  by_cases hd : d=0
  · subst d
    simp
  obtain ⟨i,hi⟩ : ∃ i,d i≠0 := by
    by_contra! h
    apply hd
    ext i
    exact h i
  have hh := coefficient_X_pderiv p i d
  rw [hp i,mul_zero,coeff_zero] at hh
  have hc : p.coeff d=0 := (mul_eq_zero.mp hh.symm).resolve_left (Nat.cast_ne_zero.mpr hi)
  simp [coeff_C,hc,hd,Ne.symm hd]

private theorem coordinate_derivation_aeval (f : ι → L) (D : Derivation K L L) (i : ι)
    (hself : D (f i)=1) (hother : ∀ j,j≠i → D (f j)=0) (p : MvPolynomial ι K) :
    D (aeval f p)=aeval f (pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p j hp =>
      by_cases hj : j=i
      · subst j
        simp [Derivation.leibniz,pderiv_mul,hp,hself,smul_eq_mul,mul_comm,add_comm]
      · simp [Derivation.leibniz,pderiv_mul,hp,hother j hj,
          pderiv_X_of_ne hj,smul_eq_mul,mul_comm]

theorem algebraicIndependent_of_coordinate_derivations [CharZero K] (f : ι → L)
    (h : ∀ i,∃ D : Derivation K L L,D (f i)=1 ∧ ∀ j,j≠i → D (f j)=0) :
    AlgebraicIndependent K f := by
  classical
  have hall : ∀ n (p : MvPolynomial ι K),p.totalDegree=n → aeval f p=0 → p=0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hn hp
      have hc : p=C (p.coeff 0) := by
        by_cases hz : p.totalDegree=0
        · exact totalDegree_eq_zero_iff_eq_C.mp hz
        apply eq_constant_of_pderiv_zero
        intro i
        obtain ⟨D,hself,hother⟩ := h i
        have heval : aeval f (pderiv i p)=0 := by
          rw [← coordinate_derivation_aeval f D i hself hother p,hp,map_zero]
        exact ih (pderiv i p).totalDegree (by
          rw [← hn]
          exact pderiv_totalDegree_lt p i (Nat.pos_of_ne_zero hz))
          (pderiv i p) rfl heval
      have he : algebraMap K L (p.coeff 0)=0 := by
        simpa only [aeval_C] using (congrArg (aeval f) hc).symm.trans hp
      have hz : p.coeff 0=0 := (algebraMap K L).injective (he.trans (map_zero _).symm)
      simpa only [hz,C_0] using hc
  exact algebraicIndependent_iff.mpr fun p hp => hall p.totalDegree p rfl hp

theorem algebraicIndependent_of_derivation_values_surjective [CharZero K] (f : ι → L)
    (h : ∀ v : ι → L,∃ D : Derivation K L L,∀ i,D (f i)=v i) :
    AlgebraicIndependent K f := by
  classical
  apply algebraicIndependent_of_coordinate_derivations f
  intro i
  obtain ⟨D,hD⟩ := h (Pi.single i 1)
  refine ⟨D,?_,?_⟩
  · simpa using hD i
  · intro j hj
    simpa [Pi.single_apply,hj] using hD j

end FD56
