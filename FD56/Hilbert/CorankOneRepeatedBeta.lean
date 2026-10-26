/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.CorankOneObservabilityHilbert
import FD56.Hilbert.ObservabilityBlockHilbert
import FD56.Hilbert.ObservabilityBetaBlockDimension
import FD56.Hilbert.GenericObservabilityBetaTransfer
import FD56.Stabilizer.GenericWideObservabilityRightInverse
import FD56.Hilbert.MinimalProfile

/-! Equal second auxiliary degrees from repeated actual corank-one terminal stacks. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m t : Type*} [Field K] [Fintype n] [Fintype m] [Fintype t]
  [DecidableEq n] [DecidableEq m] [DecidableEq t]

theorem generic_corank_one_repeated_bounded_beta_hilbert (q d : ℕ)
    (hm : 2 ≤ Fintype.card m) (hn : Fintype.card n+1=(q+1)*Fintype.card m) :
    Module.finrank (AffineCoefficientField K (MatrixParameters (n × t) (m × t)))
      (boundedObservabilityBetaKernel q (genericAffineSquare K (n × t) (m × t))
        (genericAffineRows K (n × t) (m × t)) d) =
      Fintype.card t*(d+1-(Fintype.card m*(∑ i : Fin (q+1), (i.val+1))-(q+1))) := by
  let M := fun _ : t => genericAffineSquare K n m
  let P := fun _ : t => genericAffineRows K n m
  have hM : DegreeBound (blockDiagonal M) 1 :=
    blockDiagonal_degreeBound_one M (fun _ => genericAffineSquare_degree K n m)
  have hP : DegreeBound (blockDiagonal P) 1 :=
    blockDiagonal_degreeBound_one P (fun _ => genericAffineRows_degree K n m)
  let σ : K →+* AffineCoefficientField K (MatrixParameters n m) :=
    (algebraMap (MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K) _).comp MvPolynomial.C
  apply le_antisymm
  · have hh := generic_observability_beta_kernel_le_field_witness q σ
      (blockDiagonal M) (blockDiagonal P) hM hP d
    rw [observability_beta_blocks_finrank] at hh
    simpa only [M,P,generic_corank_one_all_depths_bounded_beta_hilbert q d hm hn,
      Finset.sum_const,Finset.card_univ,smul_eq_mul] using hh
  · have hh := observability_beta_kernel_lower q
      (genericAffineSquare K (n × t) (m × t)) (genericAffineRows K (n × t) (m × t))
      (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _) d
    have he := corank_one_observability_beta_dimension_identity q d
      (Fintype.card m) (Fintype.card n) (by omega) hn
    rw [Fintype.card_prod,Fintype.card_prod] at hh
    have hscale : Fintype.card m*Fintype.card t*((d+1)+(∑ i : Fin q, (d+q-i.val+1))) -
        Fintype.card n*Fintype.card t*(d+q+2) =
        Fintype.card t*(Fintype.card m*((d+1)+(∑ i : Fin q, (d+q-i.val+1))) -
          Fintype.card n*(d+q+2)) := by
      rw [Nat.mul_sub_left_distrib]
      congr 1 <;> ring
    rwa [hscale,he] at hh

theorem generic_corank_one_repeated_beta_degrees {r : Type*} [Fintype r] [Nonempty t]
    (q : ℕ) (hm : 2 ≤ Fintype.card m)
    (hn : Fintype.card n+1=(q+1)*Fintype.card m)
    (B : Basis r (AffineCoefficientField K (MatrixParameters (n × t) (m × t)))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K (n × t) (m × t))
        (genericAffineRows K (n × t) (m × t)) q)))) :
    HasMinimalKernelDegrees (genericAffineRows K (n × t) (m × t) *
      (genericAffineSquare K (n × t) (m × t))^q * polynomialKernelBasisMatrix _ B).transpose
      (List.replicate (Fintype.card t)
        (Fintype.card m*(∑ i : Fin (q+1), (i.val+1))-(q+1))) := by
  have hbase : q*Fintype.card m < Fintype.card n := by nlinarith
  have hsize : q*Fintype.card (m × t) < Fintype.card (n × t) := by
    simpa only [Fintype.card_prod,Nat.mul_assoc] using
      Nat.mul_lt_mul_of_pos_right hbase (Fintype.card_pos (α := t))
  obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse (K := K) q hsize
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [← observability_beta_kernel_finrank q _ _ B R hR
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
    (generic_observability_row_leading_injective q hsize.le) d,
    generic_corank_one_repeated_bounded_beta_hilbert q d hm hn]
  simp

end FD56
