/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedSLRealization
import FD56.Hilbert.MixedGenericWitness
import FD56.Hilbert.MixedSLCriticalBound
import FD56.Hilbert.GenericKernelExtension

/-! The mixed critical SL Hilbert function from simultaneous auxiliary witnesses. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_mixed_slHilbert_critical_upper (a u v : ℕ) (ha : 2 ≤ a)
    (hu : 0 < u) (hv : 0 < v)
    (hm : Fintype.card m = a * (u+v) + v)
    (hn : Fintype.card n = Fintype.card m + (u+v)) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) (a+2) ≤
      u * (Fintype.card m - 4 * (u+v)) + (a+4-3*(u+v)*v) := by
  let F := MixedWitnessField K a u v
  let W := genericMixedWitness K a u v
  have hsize : u+v < a*(u+v)+v := by nlinarith
  have hW0 : Module.finrank F (polynomialKernelAtDegree W.transpose 0) = 0 := by
    rw [genericMixedWitness_kernel_hilbert a u v hsize]
    omega
  have hW1 : Module.finrank F (polynomialKernelAtDegree W.transpose 1) =
      a*(u+v)+v-4*(u+v) := by
    rw [genericMixedWitness_kernel_hilbert a u v hsize]
    omega
  let t := (a+1)-3*(v*(u+v)-1)
  let f : Fin t → ℕ := fun l => 3*(v*(u+v)-1)+l.val
  have hz (E : Matrix (Fin v) (MixedScalarRows a (Fin u) (Fin v)) F[X]) (c : F[X])
      (hE : DegreeBound E 0) (hc : c.natDegree ≤ a+3)
      (hrel : E * W = (-c) • (fun i j => if Sum.inr i = j then 1 else 0 :
        Matrix (Fin v) (Fin u ⊕ Fin v) F[X]))
      (ht : ∀ j, c.coeff (f j) = 0) : c = 0 := by
    let E₀ : Matrix (Fin v) (MixedScalarRows a (Fin u) (Fin v)) F :=
      fun i j => (E i j).coeff 0
    have he : E = E₀.map C := by
      funext i j
      exact eq_C_of_natDegree_le_zero (hE i j)
    exact (genericMixedWitness_scalar_obstruction a u v (by omega) hv E₀ c hc
      (by rw [← he]; exact hrel) ht).2
  obtain ⟨M,P,hM,hP,hH⟩ := exists_mixed_sl_critical_upper_witness_of_matrix
    a u v hv hm hn W (genericMixedWitness_degree a u v)
    (genericMixedWitness_injective a u v (by omega) hv) hW0 hW1 t f hz
  have hupper := (generic_slHilbert_le_field_witness (algebraMap K F)
    M P hM hP i₀ (a+2)).trans hH
  have hpos : 1 ≤ v*(u+v) := by nlinarith
  have hs := Nat.sub_add_cancel hpos
  have hthree : 3*(v*(u+v)-1)+3 = 3*(u+v)*v := by nlinarith
  have ht : t = a+4-3*(u+v)*v := by dsimp only [t]; omega
  simpa only [ht] using hupper

theorem generic_mixed_slHilbert_critical (a u v : ℕ) (ha : 4 ≤ a)
    (hu : 0 < u) (hv : 0 < v)
    (hm : Fintype.card m = a * (u+v) + v)
    (hn : Fintype.card n = Fintype.card m + (u+v)) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) (a+2) =
      u * (Fintype.card m - 4 * (u+v)) + (a+4-3*(u+v)*v) := by
  exact le_antisymm (generic_mixed_slHilbert_critical_upper a u v (by omega) hu hv hm hn i₀)
    (generic_mixed_slHilbert_critical_lower a u v ha hu hm hn i₀)

theorem generic_mixed_three_slHilbert_five_of_product (u v : ℕ)
    (hu : 0 < u) (hv : 0 < v) (hprod : 3 ≤ (u+v)*v)
    (hm : Fintype.card m = 3 * (u+v) + v)
    (hn : Fintype.card n = Fintype.card m + (u+v)) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) 5 = 0 := by
  have hh := generic_mixed_slHilbert_critical_upper (K := K)
    3 u v (by omega) hu hv hm hn i₀
  have hGL : Fintype.card m - 4 * (u+v) = 0 := by omega
  have ht : 3+4-3*(u+v)*v = 0 := by
    apply Nat.sub_eq_zero_of_le
    nlinarith
  simpa only [hGL, ht, mul_zero, add_zero, Nat.reduceAdd, Nat.le_zero] using hh

end FD56
