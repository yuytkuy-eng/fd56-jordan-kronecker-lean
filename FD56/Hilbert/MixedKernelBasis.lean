/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericMinimal

/-! Actual reduced kernel bases with specified low and high degree indices. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

theorem list_count_eq_indicator_sum (xs : List ℕ) (c : ℕ) :
    xs.count c = (xs.map (fun x => if x = c then 1 else 0)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.count_cons, ih, Nat.add_comm]

theorem count_ofFn_eq_card_fiber {s : ℕ} (f : Fin s → ℕ) (c : ℕ) :
    (List.ofFn f).count c = Fintype.card {i // f i = c} := by
  rw [list_count_eq_indicator_sum, List.map_ofFn, List.sum_ofFn,
    Fintype.card_subtype, Finset.card_filter]
  rfl

def degreePermutation {s t : Type*} [Fintype s] [Fintype t]
    (e : s → ℕ) (f : t → ℕ)
    (h : ∀ c, Fintype.card {i // e i = c} = Fintype.card {j // f j = c}) : s ≃ t :=
  Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (h c))

theorem degreePermutation_map {s t : Type*} [Fintype s] [Fintype t]
    (e : s → ℕ) (f : t → ℕ)
    (h : ∀ c, Fintype.card {i // e i = c} = Fintype.card {j // f j = c}) (i : s) :
    f (degreePermutation e f h i) = e i :=
  Equiv.ofFiberEquiv_map _ i

def mixedKernelDegree (a u v : ℕ) : Fin u ⊕ Fin v → ℕ :=
  Sum.elim (fun _ => a) (fun _ => a + 1)

@[simp] theorem mixedKernelDegree_inl (a u v : ℕ) (i : Fin u) :
    mixedKernelDegree a u v (Sum.inl i) = a := rfl

@[simp] theorem mixedKernelDegree_inr (a u v : ℕ) (i : Fin v) :
    mixedKernelDegree a u v (Sum.inr i) = a + 1 := rfl

theorem mixedKernelDegree_fiber_card (a u v c : ℕ) :
    Fintype.card {i // mixedKernelDegree a u v i = c} =
      (if a + 1 = c then v else 0) + (if a = c then u else 0) := by
  rw [Fintype.card_subtype, Finset.card_filter]
  rw [Fintype.sum_sum_type]
  simp only [mixedKernelDegree_inl, mixedKernelDegree_inr, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  split_ifs <;> simp [Nat.add_comm]

variable {K : Type*} [Field K]

theorem mixed_minimal_kernel_basis {x y : Type*} [Fintype y] [DecidableEq y]
    (A : Matrix x y K[X]) (a u v : ℕ)
    (h : HasMinimalKernelDegrees A
      (List.replicate v (a + 1) ++ List.replicate u a)) :
    ∃ B : Basis (Fin u ⊕ Fin v) K[X] (LinearMap.ker (Matrix.toLin' A)),
      (∀ i j, (polynomialKernelBasisMatrix A B i j).natDegree ≤ mixedKernelDegree a u v j) ∧
      Function.Injective (Matrix.mulVec
        (fun i j => (polynomialKernelBasisMatrix A B i j).coeff (mixedKernelDegree a u v j))) := by
  obtain ⟨s, B, e, hB, hL, hp⟩ := h
  have hc : ∀ c, Fintype.card {i // e i = c} =
      Fintype.card {j // mixedKernelDegree a u v j = c} := by
    intro c
    rw [← count_ofFn_eq_card_fiber, hp.count_eq, mixedKernelDegree_fiber_card]
    simp [List.count_replicate]
  let q := degreePermutation e (mixedKernelDegree a u v) hc
  have hq (j : Fin u ⊕ Fin v) : e (q.symm j) = mixedKernelDegree a u v j := by
    simpa only [q, Equiv.apply_symm_apply] using
      (degreePermutation_map e (mixedKernelDegree a u v) hc (q.symm j)).symm
  refine ⟨B.reindex q, ?_, ?_⟩
  · intro i j
    simpa [polynomialKernelBasisMatrix, Basis.reindex_apply, hq] using hB i (q.symm j)
  · apply Matrix.mulVec_injective_iff.mpr
    have hh := (Matrix.mulVec_injective_iff.mp hL).comp q.symm q.symm.injective
    change LinearIndependent K (fun j i =>
      (polynomialKernelBasisMatrix A B i (q.symm j)).coeff (e (q.symm j))) at hh
    simp only [polynomialKernelBasisMatrix, Basis.reindex_apply]
    change LinearIndependent K (fun j i =>
      (polynomialKernelBasisMatrix A B i (q.symm j)).coeff (mixedKernelDegree a u v j))
    simpa only [hq] using hh

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem generic_mixed_kernel_basis (a u v : ℕ) (hu : 0 < u)
    (hm : Fintype.card m = a * (u + v) + v)
    (hn : Fintype.card n = Fintype.card m + (u + v)) :
    ∃ B : Basis (Fin u ⊕ Fin v)
      (Polynomial (AffineCoefficientField K (MatrixParameters n m)))
      (LinearMap.ker (Matrix.toLin' (genericAffineRows K n m))),
      (∀ i j, (polynomialKernelBasisMatrix (genericAffineRows K n m) B i j).natDegree ≤
        mixedKernelDegree a u v j) ∧
      Function.Injective (Matrix.mulVec
        (fun i j => (polynomialKernelBasisMatrix (genericAffineRows K n m) B i j).coeff
          (mixedKernelDegree a u v j))) := by
  apply mixed_minimal_kernel_basis
  have hmn : Fintype.card m < Fintype.card n := by omega
  have hd : Fintype.card n - Fintype.card m = u + v := by omega
  have hmod : (a * (u + v) + v) % (u + v) = v := by
    rw [Nat.mul_comm a, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hdiv : (a * (u + v) + v) / (u + v) = a := by
    rw [Nat.mul_comm a, Nat.mul_add_div (by omega),
      Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have h := generic_rows_minimal_degrees (K := K) hmn
  rw [balancedDegreeList, hd, hm, hmod, hdiv] at h
  simpa using h

end FD56
