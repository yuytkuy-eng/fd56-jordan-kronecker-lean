/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialMatrix
import Mathlib.Algebra.Polynomial.Degree.Support

/-! Affine matrices acting on block monomial vectors realize arbitrary
polynomial columns with one additional degree. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K a r : Type*} [Field K] [Fintype r] [DecidableEq r]

def blockMonomialKernel (e : r → ℕ) : Matrix (Σ j, Fin (e j + 1)) r K[X] :=
  fun x j => if x.1 = j then (-Polynomial.X) ^ x.2.val else 0

def affineMonomialLiftEntry (p : K[X]) (e : ℕ) (k : Fin (e + 1)) : K[X] :=
  Polynomial.C ((-1 : K) ^ k.val) *
    (Polynomial.C (p.coeff k.val) +
      if k = Fin.last e then Polynomial.C (p.coeff (e + 1)) * Polynomial.X else 0)

theorem affineMonomialLiftEntry_degree (p : K[X]) (e : ℕ) (k : Fin (e + 1)) :
    (affineMonomialLiftEntry p e k).natDegree ≤ 1 := by
  unfold affineMonomialLiftEntry
  apply Polynomial.natDegree_mul_le.trans
  simp only [Polynomial.natDegree_C, Nat.zero_add]
  apply Polynomial.natDegree_add_le_of_degree_le (by simp)
  split_ifs
  · exact Polynomial.natDegree_mul_le.trans (by simp)
  · simp

theorem affineMonomialLiftEntry_sum (p : K[X]) (e : ℕ)
    (hp : p.natDegree ≤ e + 1) :
    ∑ k : Fin (e + 1), affineMonomialLiftEntry p e k * (-Polynomial.X) ^ k.val = p := by
  have hsign (k : ℕ) :
      Polynomial.C ((-1 : K) ^ k) * (-Polynomial.X) ^ k = Polynomial.X ^ k := by
    rw [map_pow, ← mul_pow]
    simp
  have hterm (k : Fin (e + 1)) :
      affineMonomialLiftEntry p e k * (-Polynomial.X) ^ k.val =
      Polynomial.C (p.coeff k.val) * Polynomial.X ^ k.val +
        if k = Fin.last e then Polynomial.C (p.coeff (e + 1)) * Polynomial.X ^ (e + 1)
        else 0 := by
    unfold affineMonomialLiftEntry
    rw [mul_right_comm, hsign]
    by_cases hk : k = Fin.last e
    · rw [if_pos hk, if_pos hk]
      have hv : k.val = e := congrArg Fin.val hk
      rw [hv]
      rw [pow_succ]
      ring
    · simp [hk]
  calc
    ∑ k : Fin (e + 1), affineMonomialLiftEntry p e k * (-Polynomial.X) ^ k.val =
        (∑ k : Fin (e + 1), Polynomial.C (p.coeff k.val) * Polynomial.X ^ k.val) +
          Polynomial.C (p.coeff (e + 1)) * Polynomial.X ^ (e + 1) := by
            simp_rw [hterm]
            rw [Finset.sum_add_distrib]
            simp
    _ = ∑ k ∈ Finset.range (e + 2), Polynomial.C (p.coeff k) * Polynomial.X ^ k := by
      rw [Fin.sum_univ_eq_sum_range (fun k => Polynomial.C (p.coeff k) * Polynomial.X ^ k)]
      exact (Finset.sum_range_succ
        (fun k => Polynomial.C (p.coeff k) * Polynomial.X ^ k) (e + 1)).symm
    _ = p := by
      simpa only [Polynomial.C_mul_X_pow_eq_monomial] using
        (p.as_sum_range' (e + 2) (by omega)).symm

theorem exists_affine_monomial_lift (e : r → ℕ) (W : Matrix a r K[X])
    (hW : ∀ i j, (W i j).natDegree ≤ e j + 1) :
    ∃ M : Matrix a (Σ j, Fin (e j + 1)) K[X],
      DegreeBound M 1 ∧ M * blockMonomialKernel e = W := by
  let M : Matrix a (Σ j, Fin (e j + 1)) K[X] :=
    fun i x => affineMonomialLiftEntry (W i x.1) (e x.1) x.2
  refine ⟨M, ?_, ?_⟩
  · intro i x
    exact affineMonomialLiftEntry_degree (W i x.1) (e x.1) x.2
  · funext i j
    simp only [Matrix.mul_apply, Fintype.sum_sigma, blockMonomialKernel]
    rw [Fintype.sum_eq_single j]
    · simpa only [if_pos rfl, M] using affineMonomialLiftEntry_sum (W i j) (e j) (hW i j)
    · intro k hk
      simp [hk]

end FD56
