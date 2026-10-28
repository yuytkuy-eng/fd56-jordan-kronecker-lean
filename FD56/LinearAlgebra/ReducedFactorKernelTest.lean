/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.ReducedFactorDegrees

/-! Vanishing of low-degree vectors in a containing kernel bounds the degrees
of a reduced factor, without requiring equality with that kernel. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n r s t : Type*} [Field K] [Fintype r] [Fintype s]

theorem reduced_factor_degrees_lt_of_kernel_vanishing
    (V : Matrix n r K[X]) (C : Matrix r s K[X]) (e : r → ℕ) (D d : ℕ)
    (hV : ∀ i j, (V i j).natDegree≤e j)
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (V i j).coeff (e j))))
    (hC : Function.Injective C.transpose.mulVec) (hVC : DegreeBound (V*C) D)
    (A : Matrix t s K[X]) (hAC : A*C.transpose=0)
    (hzero : ∀ z : s → K[X], A*ᵥz=0 → (∀ j, (z j).natDegree≤d) → z=0) :
    ∀ i, e i+d<D := by
  classical
  obtain ⟨he,hdegree⟩ := reduced_factor_degree_bounds V C e D hV hlead hC hVC
  intro i
  by_contra! hi
  have hrow : (fun j => C i j)=0 := by
    apply hzero
    · funext k
      exact congrFun (congrFun hAC k) i
    · intro j
      exact (hdegree i j).trans (by have := he i; omega)
  have hz : C.transpose*ᵥPi.single i 1=C.transpose*ᵥ0 := by
    funext j
    simpa only [Matrix.mulVec_single_one,Matrix.mulVec_zero,Matrix.transpose_apply,
      Pi.zero_apply] using congrFun hrow j
  have h := congrFun (hC hz) i
  simp at h

theorem reduced_factor_degrees_eq_of_kernel_vanishing_and_sum
    (V : Matrix n r K[X]) (C : Matrix r s K[X]) (e : r → ℕ) (D d : ℕ)
    (hV : ∀ i j, (V i j).natDegree≤e j)
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (V i j).coeff (e j))))
    (hC : Function.Injective C.transpose.mulVec) (hVC : DegreeBound (V*C) D)
    (A : Matrix t s K[X]) (hAC : A*C.transpose=0)
    (hzero : ∀ z : s → K[X], A*ᵥz=0 → (∀ j, (z j).natDegree≤d) → z=0)
    (hsum : (∑ i, e i)=Fintype.card r*(D-d-1)) :
    ∀ i, e i=D-d-1 := by
  have hb := reduced_factor_degrees_lt_of_kernel_vanishing V C e D d hV hlead hC hVC A hAC hzero
  have hle (i : r) (_ : i∈Finset.univ) : e i≤D-d-1 := by have := hb i; omega
  have he := (Finset.sum_eq_sum_iff_of_le hle).mp (show (∑ i, e i)=∑ _i : r, (D-d-1) by
    simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul] using hsum)
  exact fun i => he i (Finset.mem_univ i)

end FD56
