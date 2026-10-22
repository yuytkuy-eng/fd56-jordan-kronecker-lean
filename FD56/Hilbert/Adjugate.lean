/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.KernelDimension
import FD56.Hilbert.HilbertObstruction
import FD56.Stabilizer.TraceAnnihilator
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! Adjugates give bounded scalar-translation solutions for square pencils. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]

theorem polynomial_det_degree {a : Type*} [Fintype a] [DecidableEq a]
    (P : Matrix a a K[X]) (e : ℕ) (hP : DegreeBound P e) :
    P.det.natDegree ≤ Fintype.card a * e := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  calc
    (Equiv.Perm.sign σ • ∏ i, P (σ i) i).natDegree ≤ (∏ i, P (σ i) i).natDegree := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · rw [h, one_smul]
      · rw [h, Units.neg_smul, one_smul, Polynomial.natDegree_neg]
    _ ≤ ∑ i, (P (σ i) i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i : a, e := Finset.sum_le_sum (fun i _ => hP (σ i) i)
    _ = Fintype.card a * e := by simp

theorem polynomial_adjugate_degree (n e : ℕ) (P : Matrix (Fin n) (Fin n) K[X])
    (hP : DegreeBound P e) : DegreeBound P.adjugate ((n - 1) * e) := by
  cases n with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
    intro i j
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    have hm := polynomial_det_degree (P.submatrix j.succAbove i.succAbove) e
      (fun k l => hP (j.succAbove k) (i.succAbove l))
    have hs : ((-1 : K[X]) ^ (j.val + i.val)).natDegree = 0 := by simp
    exact Polynomial.natDegree_mul_le.trans (by simpa [hs] using hm)

variable {a : Type*} [Fintype a] [DecidableEq a]

theorem adjugate_multiple_degree (P : Matrix a a K[X]) (e d : ℕ)
    (hA : DegreeBound P.adjugate e) (c : Polynomial.degreeLT K (d + 1 - e)) :
    DegreeBound (c.val • P.adjugate) d := by
  rcases (mem_degreeLT_shift_iff c.val d e).mp c.property with hc | ⟨he, hc⟩
  · simp [hc, DegreeBound]
  · intro i j
    have hm := Polynomial.natDegree_mul_le (p := c.val) (q := P.adjugate i j)
    have ha := hA i j
    change (c.val * P.adjugate i j).natDegree ≤ d
    omega

def adjugateSLMap (M P : Matrix a a K[X]) (e d : ℕ)
    (hA : DegreeBound P.adjugate e) (i₀ : a) :
    Polynomial.degreeLT K (d + 1 - e) →ₗ[K] boundedSLKernel M P d where
  toFun c := ⟨(0, boundedMatrixOf (c.val • P.adjugate) (adjugate_multiple_degree P e d hA c)), by
    letI : Nonempty a := ⟨i₀⟩
    apply (slRadical_iff_equations M P 0 (c.val • P.adjugate)).mpr
    refine ⟨by simp, by simp, -(c.val * P.det), ?_⟩
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul]
    simp⟩
  map_add' c c' := by
    apply Subtype.ext
    apply Prod.ext
    · simp
    · funext i j
      apply Subtype.ext
      exact congrArg (fun A : Matrix a a K[X] => A i j) (add_smul c.val c'.val P.adjugate)
  map_smul' k c := by
    apply Subtype.ext
    apply Prod.ext
    · simp
    · funext i j
      apply Subtype.ext
      change (k • c.val) * P.adjugate i j = k • (c.val * P.adjugate i j)
      exact smul_mul_assoc k c.val (P.adjugate i j)

theorem adjugateSLMap_injective (M P : Matrix a a K[X]) (e d : ℕ)
    (hA : DegreeBound P.adjugate e) (i₀ : a) (hdet : P.det ≠ 0) :
    Function.Injective (adjugateSLMap M P e d hA i₀) := by
  intro c c' h
  apply Subtype.ext
  have hU : c.val • P.adjugate = c'.val • P.adjugate :=
    congrArg (fun z : boundedSLKernel M P d => entries z.val.2) h
  have hh := congrArg (fun A : Matrix a a K[X] => (A * P) i₀ i₀) hU
  simp only [Matrix.smul_mul, Matrix.adjugate_mul, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply, if_pos rfl, mul_one] at hh
  exact mul_right_cancel₀ hdet (by simpa only [ite_true, mul_one] using hh)

theorem slHilbert_adjugate_lower (M P : Matrix a a K[X]) (e d : ℕ)
    (hA : DegreeBound P.adjugate e) (i₀ : a) (hdet : P.det ≠ 0) :
    d + 1 - e ≤ slHilbert M P d := by
  have hh := LinearMap.finrank_le_finrank_of_injective
    (adjugateSLMap_injective M P e d hA i₀ hdet)
  rw [(Polynomial.degreeLTEquiv K (d + 1 - e)).finrank_eq] at hh
  simpa [slHilbert] using hh

theorem square_slHilbert_lower (n : ℕ) (hn : 0 < n)
    (M P : Matrix (Fin n) (Fin n) K[X]) (hP : DegreeBound P 1)
    (hdet : P.det ≠ 0) (d : ℕ) : d + 1 - (n - 1) ≤ slHilbert M P d := by
  apply slHilbert_adjugate_lower M P (n - 1) d _ ⟨0, hn⟩ hdet
  simpa using polynomial_adjugate_degree n 1 P hP

end FD56
