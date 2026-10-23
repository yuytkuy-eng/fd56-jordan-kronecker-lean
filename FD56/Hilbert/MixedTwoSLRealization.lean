/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedTwoSLCriticalBound
import FD56.Hilbert.MixedTwoGenericWitness
import FD56.Hilbert.MixedSLGeneralRealization
import FD56.Hilbert.GenericKernelExtension

/-! Actual mixed quotient-two scalar corrections at degree six. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_mixed_two_slHilbert_six_upper_of_ge (u v : ℕ)
    (_hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u)
    (hm : Fintype.card m = 2*(u+v)+v)
    (hn : Fintype.card n = Fintype.card m+(u+v)) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) 6 ≤
      3*u*v+(8-v*(u-v)) := by
  let F := MixedWitnessField K 2 u v
  let W := genericMixedWitness K 2 u v
  have hsize : u+v < 2*(u+v)+v := by omega
  have hW2 : Module.finrank F (polynomialKernelAtDegree W.transpose 2) = 0 := by
    rw [genericMixedWitness_kernel_hilbert 2 u v hsize]
    omega
  have hW3 : Module.finrank F (polynomialKernelAtDegree W.transpose 3) = 3*v := by
    rw [genericMixedWitness_kernel_hilbert 2 u v hsize]
    omega
  have hsum : (∑ i, Module.finrank F (polynomialKernelAtDegree W.transpose
      (6-(mixedKernelDegree 2 u v i+1)))) = 3*u*v := by
    simp only [Fintype.sum_sum_type,mixedKernelDegree_inl,mixedKernelDegree_inr,
      Nat.reduceAdd,Nat.reduceSub,hW2,hW3,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul,mul_zero,add_zero]
    ring
  have hz (E : Matrix (Fin u ⊕ Fin v) (MixedScalarRows 2 (Fin u) (Fin v)) F[X])
      (c : F[X])
      (hE : ∀ i j, E i j = 0 ∨ (mixedKernelDegree 2 u v i+1 ≤ 6 ∧
        (E i j).natDegree ≤ 6-(mixedKernelDegree 2 u v i+1)))
      (hc : c.natDegree ≤ 7) (hrel : E * W = (-c) • 1)
      (ht : ∀ j : Fin (8-v*(u-v)), c.coeff (v*(u-v)+j.val) = 0) : c = 0 := by
    let Eh := E.submatrix Sum.inr id
    have hEh : DegreeBound Eh 2 := by
      intro i j
      rcases hE (Sum.inr i) j with h | ⟨_,h⟩
      · change (E (Sum.inr i) j).natDegree ≤ 2
        rw [h]; simp
      · simpa only [mixedKernelDegree_inr,Nat.reduceAdd,Nat.reduceSub] using h
    have hrelh : Eh * W = (-c) • (mixedScalarHighIdentity :
        Matrix (Fin v) (Fin u ⊕ Fin v) F[X]) := by
      funext i j
      have h := congrArg (fun A : Matrix (Fin u ⊕ Fin v) (Fin u ⊕ Fin v) F[X] =>
        A (Sum.inr i) j) hrel
      simpa [Eh,mixedScalarHighIdentity,Matrix.mul_apply,Matrix.one_apply] using h
    exact (genericMixedTwoWitness_quadratic_scalar_obstruction (K := K)
      u v hv hvu Eh c hEh hc hrelh ht).2
  obtain ⟨M,P,hM,hP,hH⟩ := exists_mixed_sl_upper_witness_of_matrix
    2 u v 6 hv (by omega) hm hn W (genericMixedWitness_degree 2 u v)
    (genericMixedWitness_injective 2 u v (by omega) hv) (3*u*v) hsum
    (8-v*(u-v)) (fun j => v*(u-v)+j.val) hz
  exact (generic_slHilbert_le_field_witness (algebraMap K F) M P hM hP i₀ 6).trans hH

theorem generic_mixed_two_slHilbert_six_of_ge (u v : ℕ)
    (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u)
    (hm : Fintype.card m = 2*(u+v)+v)
    (hn : Fintype.card n = Fintype.card m+(u+v)) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) 6 =
      3*u*v+(8-v*(u-v)) :=
  le_antisymm (generic_mixed_two_slHilbert_six_upper_of_ge u v hu hv hvu hm hn i₀)
    (generic_mixed_two_slHilbert_six_lower u v hu hvu hm hn i₀)

theorem generic_mixed_two_slHilbert_six (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hm : Fintype.card m = 2*(u+v)+v)
    (hn : Fintype.card n = Fintype.card m+(u+v)) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) 6 =
      3*u*v+v*(v-u)+(8-v*(u-v)) := by
  by_cases hvu : v ≤ u
  · rw [generic_mixed_two_slHilbert_six_of_ge u v hu hv hvu hm hn i₀,
      Nat.sub_eq_zero_of_le hvu,mul_zero,add_zero]
  · have huv : u ≤ v := by omega
    rw [generic_mixed_two_slHilbert_high_of_le u v hu huv hm hn i₀ 6 (by omega),
      generic_mixed_two_glHilbert_six u v hu hm hn,
      Nat.sub_eq_zero_of_le huv,mul_zero,Nat.sub_zero]

end FD56
