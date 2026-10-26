/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Relations among complementary products of distinct prime factors. -/

namespace FD56
open scoped BigOperators

variable {R ι : Type*} [CommRing R] [IsDomain R] [Fintype ι] [DecidableEq ι]

/-- The product of all factors except the selected one. -/
def complementaryProduct (L : ι → R) (i : ι) : R :=
  ∏ j ∈ Finset.univ.erase i, L j

omit [IsDomain R] in
theorem complementary_product_relation_divisible (L A : ι → R)
    (hprime : ∀ i, Prime (L i)) (hdistinct : ∀ i j, i ≠ j → ¬ L i ∣ L j)
    (hrel : ∑ i, complementaryProduct L i * A i = 0) :
    ∀ i, L i ∣ A i := by
  intro i
  have hrest : L i ∣ ∑ j ∈ Finset.univ.erase i, complementaryProduct L j * A j := by
    apply Finset.dvd_sum
    intro j hj
    apply dvd_mul_of_dvd_left
    exact Finset.dvd_prod_of_mem L (by simpa using (Finset.mem_erase.mp hj).1.symm)
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun j => complementaryProduct L j * A j) (Finset.mem_univ i)
  have hterm : complementaryProduct L i * A i =
      -(∑ j ∈ Finset.univ.erase i, complementaryProduct L j * A j) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [add_comm] using hsplit.trans hrel
  have hdiv : L i ∣ complementaryProduct L i * A i := by
    rw [hterm]
    exact dvd_neg.mpr hrest
  have hnot : ¬ L i ∣ complementaryProduct L i := by
    apply (hprime i).not_dvd_finset_prod
    intro j hj
    exact hdistinct i j (Finset.mem_erase.mp hj).1.symm
  exact ((hprime i).dvd_mul.mp hdiv).resolve_left hnot

theorem complementary_product_pair_relation_iff (L c A : ι → R)
    (hprime : ∀ i, Prime (L i)) (hdistinct : ∀ i j, i ≠ j → ¬ L i ∣ L j) :
    ((∑ i, complementaryProduct L i * A i) = 0 ∧
      (∑ i, c i * complementaryProduct L i * A i) = 0) ↔
      ∃ B : ι → R, (∀ i, A i = L i * B i) ∧
        (∑ i, B i) = 0 ∧ (∑ i, c i * B i) = 0 := by
  let G := ∏ i, L i
  have hG : G ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (hprime i).ne_zero)
  have hprod (i : ι) : complementaryProduct L i * L i = G := by
    exact Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  have hsum (B : ι → R) :
      (∑ i, complementaryProduct L i * (L i * B i)) = G * ∑ i, B i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc, hprod]
  have hcsum (B : ι → R) :
      (∑ i, c i * complementaryProduct L i * (L i * B i)) =
        G * ∑ i, c i * B i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      c i * complementaryProduct L i * (L i * B i) =
          (complementaryProduct L i * L i) * (c i * B i) := by ring
      _ = G * (c i * B i) := by rw [hprod]
  constructor
  · rintro ⟨hA, hcA⟩
    choose B hB using complementary_product_relation_divisible L A hprime hdistinct hA
    refine ⟨B, hB, ?_, ?_⟩
    · have h : G * ∑ i, B i = 0 := by simpa only [hB, hsum] using hA
      exact (mul_eq_zero.mp h).resolve_left hG
    · have h : G * ∑ i, c i * B i = 0 := by simpa only [hB, hcsum] using hcA
      exact (mul_eq_zero.mp h).resolve_left hG
  · rintro ⟨B, hB, hsumB, hcsumB⟩
    constructor
    · simp only [hB, hsum, hsumB, mul_zero]
    · simp only [hB, hcsum, hcsumB, mul_zero]

end FD56
