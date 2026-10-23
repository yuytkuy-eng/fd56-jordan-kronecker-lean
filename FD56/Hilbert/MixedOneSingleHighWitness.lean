/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedGenericWitness
import FD56.Hilbert.UniformCriterion

/-! A weighted bidiagonal witness for one high first-kernel degree. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option maxHeartbeats 800000

def mixedOneChainDegree (u : ℕ) (j : Fin (u+1)) : ℕ :=
  if j.val < u then 3 else 4

def mixedOneChainSuffix (u : ℕ) (j : Fin (u+1)) : ℕ :=
  if j.val < u then 3*(u-j.val)+1 else 0

variable {K : Type*} [Field K]

def mixedOneChain (u : ℕ) : Matrix (Fin (u+2)) (Fin (u+1)) K[X] := fun i j =>
  (if i.val = j.val then X ^ mixedOneChainDegree u j else 0) -
    (if i.val = j.val+1 then 1 else 0)

theorem mixedOneChain_degree (u : ℕ) (i : Fin (u+2)) (j : Fin (u+1)) :
    (mixedOneChain (K := K) u i j).natDegree ≤ mixedOneChainDegree u j := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le <;> split_ifs <;> simp

theorem mixedOneChain_mul {h : Type*} (u : ℕ) (E : Matrix h (Fin (u+2)) K[X])
    (i : h) (j : Fin (u+1)) :
    (E * mixedOneChain (K := K) u) i j =
      E i ⟨j.val,by omega⟩ * X ^ mixedOneChainDegree u j - E i ⟨j.val+1,by omega⟩ := by
  have h0 : ∀ x : Fin (u+2), x.val = j.val ↔ x = ⟨j.val,by omega⟩ :=
    fun x => (@Fin.ext_iff _ x ⟨j.val,by omega⟩).symm
  have h1 : ∀ x : Fin (u+2), x.val = j.val+1 ↔ x = ⟨j.val+1,by omega⟩ :=
    fun x => (@Fin.ext_iff _ x ⟨j.val+1,by omega⟩).symm
  simp [Matrix.mul_apply, mixedOneChain, mul_sub, Finset.sum_sub_distrib, mul_ite, h0,h1]

theorem mixedOneChain_suffix_mulVec (u : ℕ) :
    mixedOneChain (K := K) u *ᵥ (fun j => X ^ mixedOneChainSuffix u j) =
      (fun i => if i.val = 0 then X^(3*u+4) else if i.val = u+1 then -1 else 0) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, mixedOneChain, sub_mul, ite_mul,
    zero_mul, one_mul, Finset.sum_sub_distrib]
  by_cases hi0 : i.val = 0
  · have hsum0 : ∀ j : Fin (u+1), i.val = j.val ↔ j = 0 := by
      intro j
      rw [Fin.ext_iff]
      change i.val = j.val ↔ j.val = 0
      omega
    have hsum1 : ∀ j : Fin (u+1), ¬i.val = j.val+1 := by intro j; omega
    simp only [hsum0, hsum1, if_false, Finset.sum_const_zero, sub_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [if_pos hi0]
    rw [← pow_add]
    congr 1
    simp only [mixedOneChainDegree, mixedOneChainSuffix, Fin.val_zero]
    split_ifs <;> omega
  · by_cases hil : i.val = u+1
    · have hsum0 : ∀ j : Fin (u+1), ¬i.val = j.val := by intro j; have := j.isLt; omega
      have hsum1 : ∀ j : Fin (u+1), i.val = j.val+1 ↔ j = ⟨u,by omega⟩ := by
        intro j
        simp only [Fin.ext_iff]
        omega
      simp only [hsum0, if_false, Finset.sum_const_zero, hsum1, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, if_neg hi0, if_pos hil, zero_sub]
      simp [mixedOneChainSuffix]
    · have hilow : i.val < u+1 := by have := i.isLt; omega
      have hip : i.val-1 < u+1 := by omega
      have hsum0 : ∀ j : Fin (u+1), i.val = j.val ↔ j = ⟨i.val,hilow⟩ := by
        intro j
        simp only [Fin.ext_iff]
        omega
      have hsum1 : ∀ j : Fin (u+1), i.val = j.val+1 ↔ j = ⟨i.val-1,hip⟩ := by
        intro j
        simp only [Fin.ext_iff]
        omega
      simp only [hsum0, hsum1, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        if_neg hi0, if_neg hil]
      rw [← pow_add]
      apply sub_eq_zero.mpr
      congr 1
      simp only [mixedOneChainDegree, mixedOneChainSuffix]
      split_ifs <;> omega

theorem mixedOneChain_boundary {h : Type*} (u : ℕ)
    (E : Matrix h (Fin (u+2)) K[X]) (i : h) :
    ((E * mixedOneChain (K := K) u) *ᵥ (fun j => X ^ mixedOneChainSuffix u j)) i =
      E i 0 * X^(3*u+4) - E i ⟨u+1,by omega⟩ := by
  rw [← Matrix.mulVec_mulVec, mixedOneChain_suffix_mulVec]
  have h0 : ∀ x : Fin (u+2), x.val = 0 ↔ x = 0 :=
    fun x => (@Fin.ext_iff _ x 0).symm
  have hl : ∀ x : Fin (u+2), x.val = u+1 ↔ x = ⟨u+1,by omega⟩ :=
    fun x => (@Fin.ext_iff _ x ⟨u+1,by omega⟩).symm
  simp only [Matrix.mulVec, dotProduct, h0, hl]
  have hf (x : Fin (u+2)) :
      E i x * (if x = 0 then X^(3*u+4) else if x = ⟨u+1,by omega⟩ then -1 else 0) =
      (if x = 0 then E i x * X^(3*u+4) else 0) -
        (if x = ⟨u+1,by omega⟩ then E i x else 0) := by
    split_ifs <;> simp_all
  simp [hf, Finset.sum_sub_distrib]

theorem mixedOneChain_scalar_zero (u : ℕ) (hu : 0 < u)
    (E : Matrix (Fin (u+1)) (Fin (u+2)) K[X]) (c : K[X])
    (hE : ∀ i x, (E i x).natDegree ≤ 3*u+3-mixedOneChainDegree u i)
    (hc : c.natDegree ≤ 3*u+3)
    (hrel : E * mixedOneChain (K := K) u = (-c) • (1 : Matrix (Fin (u+1)) (Fin (u+1)) K[X])) : c = 0 := by
  have hb (i : Fin (u+1)) :
      E i 0 * X^(3*u+4) - E i ⟨u+1,by omega⟩ =
        -c * X ^ mixedOneChainSuffix u i := by
    rw [← mixedOneChain_boundary u E i, hrel]
    simp [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply]
  apply Polynomial.ext
  intro k
  simp only [coeff_zero]
  by_cases hk : k ≤ 3*u+3
  · let i : Fin (u+1) := ⟨min (k/3) u, by omega⟩
    have hi : 3*i.val ≤ k ∧ k < 3*i.val + mixedOneChainDegree u i := by
      dsimp only [i]
      simp only [mixedOneChainDegree]
      have hdiv := Nat.mod_add_div k 3
      have hmod := Nat.mod_lt k (by omega : 0 < 3)
      split_ifs <;> omega
    have hsum : 3*i.val + mixedOneChainDegree u i + mixedOneChainSuffix u i = 3*u+4 := by
      simp only [mixedOneChainDegree, mixedOneChainSuffix]
      split_ifs <;> omega
    have hlow : k+mixedOneChainSuffix u i < 3*u+4 := by omega
    have hhigh : (E i ⟨u+1,by omega⟩).natDegree < k+mixedOneChainSuffix u i := by
      have hh := hE i ⟨u+1,by omega⟩
      have hsmall : mixedOneChainDegree u i ≤ 3*u+3 := by
        simp only [mixedOneChainDegree]
        split_ifs <;> omega
      omega
    have hh := congrArg (fun p : K[X] => p.coeff (k+mixedOneChainSuffix u i)) (hb i)
    dsimp only at hh
    rw [Polynomial.coeff_sub, Polynomial.coeff_mul_X_pow',
      Polynomial.coeff_eq_zero_of_natDegree_lt hhigh, Polynomial.coeff_mul_X_pow'] at hh
    simp only [not_le.mpr hlow, if_false, Nat.le_add_left, if_true,
      Nat.add_sub_cancel_right, Polynomial.coeff_neg, zero_sub, neg_eq_zero] at hh
    simpa using hh.symm
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem mixedOneChain_injective (u : ℕ) :
    Function.Injective (mixedOneChain (K := K) u).mulVec := by
  apply polynomial_matrix_injective_of_zero
  intro v w h
  funext j
  have he (x : Fin (u+1)) : j.val+1=x.val+1 ↔ x=j := by
    rw [Fin.ext_iff]
    omega
  have hrow (x : Fin (u+1)) :
      Polynomial.eval 0 (mixedOneChain (K := K) u ⟨j.val+1,by omega⟩ x) =
        if x=j then -1 else 0 := by
    have hx : mixedOneChainDegree u x ≠ 0 := by
      simp only [mixedOneChainDegree]
      split_ifs <;> omega
    simp only [mixedOneChain, Polynomial.eval_sub]
    split_ifs <;> simp_all [Fin.ext_iff]
  have hh := congrFun h (⟨j.val+1,by omega⟩ : Fin (u+2))
  simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Polynomial.coe_evalRingHom,
    hrow, ite_mul, zero_mul, neg_one_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, neg_inj] using hh

theorem mixedOneChain_relation_zero_of_degree {h : Type*} (u : ℕ)
    (E : Matrix h (Fin (u+2)) K[X]) (hE : DegreeBound E (3*u+3))
    (hrel : E * mixedOneChain (K := K) u = 0) : E = 0 := by
  have hbase (i : h) : E i 0 = 0 := by
    have hh := mixedOneChain_boundary u E i
    rw [hrel, Matrix.zero_mulVec, Pi.zero_apply] at hh
    have he : E i 0 * X^(3*u+4) = E i ⟨u+1,by omega⟩ := (sub_eq_zero.mp hh.symm)
    by_contra hn
    have hd := congrArg Polynomial.natDegree he
    rw [Polynomial.natDegree_mul hn (pow_ne_zero _ Polynomial.X_ne_zero),
      Polynomial.natDegree_X_pow] at hd
    have hb := hE i ⟨u+1,by omega⟩
    omega
  funext i j
  change E i j = 0
  induction j using Fin.induction with
  | zero => exact hbase i
  | succ j ih =>
    have hh := congrFun (congrFun hrel i) j
    rw [mixedOneChain_mul] at hh
    change E i j.castSucc * X^mixedOneChainDegree u j - E i j.succ = 0 at hh
    rw [ih, zero_mul, zero_sub, neg_eq_zero] at hh
    exact hh

theorem mixedOneChain_scalar_obstruction (u : ℕ) (hu : 0 < u)
    (E : Matrix (Fin (u+1)) (Fin (u+2)) K[X]) (c : K[X])
    (hE : ∀ i x, (E i x).natDegree ≤ 3*u+3-mixedOneChainDegree u i)
    (hc : c.natDegree ≤ 3*u+3)
    (hrel : E * mixedOneChain (K := K) u =
      (-c) • (1 : Matrix (Fin (u+1)) (Fin (u+1)) K[X])) : E = 0 ∧ c = 0 := by
  have hc0 := mixedOneChain_scalar_zero u hu E c hE hc hrel
  refine ⟨mixedOneChain_relation_zero_of_degree u E
    (fun i x => (hE i x).trans (Nat.sub_le _ _)) ?_,hc0⟩
  simpa only [hc0, neg_zero, zero_smul] using hrel

end FD56
