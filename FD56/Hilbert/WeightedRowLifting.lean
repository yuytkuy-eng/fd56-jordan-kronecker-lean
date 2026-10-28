/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.WeightedSurjectivity

/-! Weighted polynomial division for a primitive matrix with independent leading rows. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

theorem weighted_row_polynomial_preimage
    (A : Matrix m n K[X]) (R : Matrix n m K[X]) (hAR : A*R=1)
    (e : m → ℕ) (hA : ∀ i j, (A i j).natDegree≤e i)
    (hlead : Function.Surjective (show Matrix m n K from fun i j => (A i j).coeff (e i)).mulVec)
    (N E : ℕ) (hR : DegreeBound R N) (he : ∀ i, e i≤E)
    (d : ℕ) (b : m → K[X]) (hb : ∀ i, (b i).natDegree≤d+e i) :
    ∃ v : n → K[X], (∀ j, (v j).natDegree≤max d (N+E)) ∧ A*ᵥv=b := by
  induction d generalizing b with
  | zero =>
    refine ⟨R*ᵥb,?_,?_⟩
    · intro j
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i _
      have hi : (b i).natDegree≤E := (by simpa using hb i : (b i).natDegree≤e i) |>.trans (he i)
      simpa only [max_eq_right (Nat.zero_le _)] using
        Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hR j i) hi)
    · rw [Matrix.mulVec_mulVec,hAR,Matrix.one_mulVec]
  | succ d ih =>
    obtain ⟨u,hu⟩ := hlead (fun i => (b i).coeff (e i+(d+1)))
    let w : n → K[X] := fun j => C (u j)*X^(d+1)
    have hw : ∀ j, (w j).natDegree≤d+1 := by
      intro j
      exact (natDegree_mul_le).trans (by simp [w])
    have hAw : ∀ i, ((A*ᵥw) i).natDegree≤d+1+e i := by
      intro i
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro j _
      change (A i j*w j).natDegree≤d+1+e i
      have ht := Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hA i j) (hw j))
      omega
    have htop (i : m) : ((A*ᵥw) i).coeff (e i+(d+1))=(b i).coeff (e i+(d+1)) := by
      have h := congrFun hu i
      simpa only [Matrix.mulVec,dotProduct,w,← mul_assoc,Polynomial.finset_sum_coeff,
        coeff_mul_X_pow,coeff_mul_C] using h
    have hlow : ∀ i, ((b-A*ᵥw) i).natDegree≤d+e i := by
      intro i
      apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro k hk
      change ((b i)-(A*ᵥw) i).coeff k=0
      rw [coeff_sub]
      by_cases heq : k=e i+(d+1)
      · rw [heq,htop,sub_self]
      · rw [coeff_eq_zero_of_natDegree_lt ((hb i).trans_lt (by omega)),
          coeff_eq_zero_of_natDegree_lt ((hAw i).trans_lt (by omega)),sub_self]
    obtain ⟨v,hv,hAv⟩ := ih (b-A*ᵥw) hlow
    refine ⟨v+w,?_,?_⟩
    · intro j
      exact (Polynomial.natDegree_add_le _ _).trans
        (max_le ((hv j).trans (max_le_max (by omega) le_rfl))
          ((hw j).trans (le_max_left _ _)))
    · rw [Matrix.mulVec_add,hAv,sub_add_cancel]

theorem weighted_row_coefficient_surjective_eventually
    (A : Matrix m n K[X]) (R : Matrix n m K[X]) (hAR : A*R=1)
    (e : m → ℕ) (hA : ∀ i j, (A i j).natDegree≤e i)
    (hlead : Function.Surjective (show Matrix m n K from fun i j => (A i j).coeff (e i)).mulVec) :
    ∃ N : ℕ, ∀ d, N≤d → Function.Surjective
      (weightedCoefficientMatrix A (fun _ => d) (fun i => d+e i)).mulVec := by
  let NR := (Finset.univ : Finset n).sup (fun j =>
    (Finset.univ : Finset m).sup (fun i => (R j i).natDegree))
  let E := (Finset.univ : Finset m).sup e
  have hR : DegreeBound R NR := by
    intro j i
    have h1 : (R j i).natDegree≤(Finset.univ : Finset m).sup (fun i => (R j i).natDegree) :=
      Finset.le_sup (f:=fun i : m => (R j i).natDegree) (Finset.mem_univ i)
    have h2 : (Finset.univ : Finset m).sup (fun i => (R j i).natDegree)≤NR :=
      Finset.le_sup (f:=fun j : n => (Finset.univ : Finset m).sup (fun i => (R j i).natDegree))
        (Finset.mem_univ j)
    exact h1.trans h2
  have he : ∀ i, e i≤E := fun i => Finset.le_sup (f:=e) (Finset.mem_univ i)
  refine ⟨NR+E,?_⟩
  intro d hd
  apply weighted_coefficient_surjective_of_lifts
  intro b hb
  obtain ⟨v,hv,hAv⟩ := weighted_row_polynomial_preimage A R hAR e hA hlead NR E hR he d b hb
  exact ⟨v,by simpa only [max_eq_left hd] using hv,hAv⟩

end FD56
