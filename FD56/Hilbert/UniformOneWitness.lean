/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformSLRelationDegree

/-! A cubic companion witness for the square auxiliary matrix. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]

def uniformOneWitness (r : ℕ) : Matrix (Fin r) (Fin r) K[X] := fun i j =>
  (if i = j then X ^ 3 else 0) - (if i.val + 1 = j.val then 1 else 0)

theorem uniformOneWitness_degree (r : ℕ) : DegreeBound (uniformOneWitness (K := K) r) 3 := by
  intro i j
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le <;> split_ifs <;> simp

theorem uniformOneWitness_leading (r : ℕ) : matrixCoeff (uniformOneWitness (K := K) r) 3 = 1 := by
  funext i j
  simp only [matrixCoeff, uniformOneWitness, coeff_sub, Matrix.one_apply]
  split_ifs <;> norm_num [Polynomial.coeff_one]

theorem uniformOneWitness_injective (r : ℕ) :
    Function.Injective (uniformOneWitness (K := K) r).mulVec := by
  have hL : Function.Injective (Matrix.mulVec
      (fun i j => (uniformOneWitness (K := K) r i j).coeff 3)) := by
    change Function.Injective (matrixCoeff (uniformOneWitness (K := K) r) 3).mulVec
    rw [uniformOneWitness_leading]
    intro u v h; simpa only [Matrix.one_mulVec] using h
  classical
  intro v w h
  by_contra hn
  have hv : v - w ≠ 0 := sub_ne_zero.mpr hn
  obtain ⟨_, i, _, hi⟩ := predictable_weighted_degree (uniformOneWitness (K := K) r)
    (fun _ => 3) (v - w) (uniformOneWitness_degree r) hL hv
  apply hi
  rw [Matrix.mulVec_sub, h, sub_self]
  rfl

theorem uniformOneWitness_product_zero (r : ℕ) (hr : 0 < r)
    (E : Matrix (Fin r) (Fin r) K[X]) (i : Fin r) :
    (E * uniformOneWitness (K := K) r) i ⟨0, hr⟩ = E i ⟨0, hr⟩ * X ^ 3 := by
  simp [Matrix.mul_apply, uniformOneWitness, mul_sub, Finset.sum_sub_distrib, mul_ite]

theorem uniformOneWitness_product_succ (r : ℕ) (E : Matrix (Fin r) (Fin r) K[X])
    (i : Fin r) (j : ℕ) (hj : j + 1 < r) :
    (E * uniformOneWitness (K := K) r) i ⟨j + 1, hj⟩ =
      E i ⟨j + 1, hj⟩ * X ^ 3 - E i ⟨j, by omega⟩ := by
  have heq (x : Fin r) : (x.val + 1 = j + 1) ↔ x = ⟨j, by omega⟩ := by
    simp only [Nat.add_right_cancel_iff, Fin.ext_iff]
  have heq' (x : Fin r) : (x.val = j) ↔ x = ⟨j, by omega⟩ := by
    simp only [Fin.ext_iff]
  simp [Matrix.mul_apply, uniformOneWitness, mul_sub, Finset.sum_sub_distrib,
    mul_ite, heq, heq']

theorem uniformOneWitness_scalar_divisible (r : ℕ) (hr : 0 < r)
    (E : Matrix (Fin r) (Fin r) K[X]) (c : K[X])
    (hrel : E * uniformOneWitness (K := K) r = (-c) • 1) : X ^ (3 * r) ∣ c := by
  let z : Fin r := ⟨0, hr⟩
  have hrow (j : ℕ) (hj : j < r) : E z z = E z ⟨j, hj⟩ * X ^ (3 * j) := by
    induction j with
    | zero => simp [z]
    | succ j ih =>
      have hj' : j < r := by omega
      have hh := congrFun (congrFun hrel z) (⟨j + 1, hj⟩ : Fin r)
      have hzj : z ≠ (⟨j + 1, hj⟩ : Fin r) := by
        intro h
        have := congrArg Fin.val h
        simp [z] at this
      rw [uniformOneWitness_product_succ] at hh
      have hrec : E z ⟨j, hj'⟩ = E z ⟨j + 1, hj⟩ * X ^ 3 := by
        have hh' : E z ⟨j + 1, hj⟩ * X ^ 3 - E z ⟨j, hj'⟩ = 0 := by
          simpa [Matrix.smul_apply, Matrix.one_apply, hzj] using hh
        exact (sub_eq_zero.mp hh').symm
      rw [ih hj', hrec, mul_assoc, ← pow_add]
      congr 2
      omega
  have hbase := congrFun (congrFun hrel z) z
  rw [uniformOneWitness_product_zero r hr E z] at hbase
  have hb : E z z * X ^ 3 = -c := by simpa [z] using hbase
  have hlast := hrow (r - 1) (by omega)
  rw [hlast, mul_assoc, ← pow_add] at hb
  have he : 3 * (r - 1) + 3 = 3 * r := by omega
  rw [he] at hb
  refine ⟨-E z ⟨r - 1, by omega⟩, ?_⟩
  rw [mul_neg, mul_comm]
  linear_combination hb

theorem uniformOneWitness_relation_zero (r : ℕ) (E : Matrix (Fin r) (Fin r) K[X])
    (hrel : E * uniformOneWitness (K := K) r = 0) : E = 0 := by
  have hL : Function.Injective (matrixCoeff (uniformOneWitness (K := K) r) 3).transpose.mulVec := by
    rw [uniformOneWitness_leading, Matrix.transpose_one]
    intro u v h; simpa only [Matrix.one_mulVec] using h
  have hh := row_coordinates_degree_bound (uniformOneWitness (K := K) r) E (fun _ => 3) (fun _ => 0)
    (uniformOneWitness_degree r) hL (by rw [hrel]; intro i j; simp)
  funext i j
  rcases hh i j with hz | ⟨hbad, _⟩
  · exact hz
  · change 3 ≤ 0 at hbad
    omega

theorem uniformOneWitness_scalar_obstruction (r : ℕ) (hr : 0 < r) (k : ℕ)
    (E : Matrix (Fin r) (Fin r) K[X]) (c : K[X]) (hE : DegreeBound E k)
    (hrel : E * uniformOneWitness (K := K) r = (-c) • 1)
    (hc : ∀ j : Fin (k + 4 - 3 * r), c.coeff (3 * r + j.val) = 0) : E = 0 ∧ c = 0 := by
  have hdiv := uniformOneWitness_scalar_divisible r hr E c hrel
  have hdeg : c.natDegree ≤ k + 3 := by
    have hd := degreeBound_mul hE (uniformOneWitness_degree r) (⟨0, hr⟩ : Fin r) ⟨0, hr⟩
    rw [hrel] at hd
    simpa using hd
  have hc0 : c = 0 := by
    apply Polynomial.ext
    intro i
    by_cases hi : i < 3 * r
    · simpa using (Polynomial.X_pow_dvd_iff.mp hdiv) i hi
    · by_cases hik : i ≤ k + 3
      · let j : Fin (k + 4 - 3 * r) := ⟨i - 3 * r, by omega⟩
        have hj : 3 * r + j.val = i := by dsimp [j]; omega
        simpa only [hj, coeff_zero] using hc j
      · simp only [coeff_zero]
        exact coeff_eq_zero_of_natDegree_lt (by omega)
  refine ⟨uniformOneWitness_relation_zero r E ?_, hc0⟩
  simpa [hc0] using hrel

end FD56
