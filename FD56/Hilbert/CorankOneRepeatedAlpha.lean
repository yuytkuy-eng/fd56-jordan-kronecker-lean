/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.CorankOneObservabilityAlpha
import FD56.Hilbert.ObservabilityBlockHilbert
import FD56.Hilbert.GenericDepthTwoAlpha

/-! Repeating an actual corank-one witness proves equal first auxiliary degrees at every depth. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m t : Type*} [Field K] [Fintype n] [Fintype m] [Fintype t]
  [DecidableEq n] [DecidableEq m] [DecidableEq t]

theorem generic_corank_one_repeated_alpha_hilbert (q d : ℕ)
    (hn : Fintype.card n=q*Fintype.card m+1) :
    Module.finrank (AffineCoefficientField K (MatrixParameters (n × t) (m × t)))
      (polynomialKernelAtDegree (observabilityMatrix
        (genericAffineSquare K (n × t) (m × t))
        (genericAffineRows K (n × t) (m × t)) q) d) =
      Fintype.card t*(d+1-Fintype.card m*(∑ i : Fin q, (i.val+1))) := by
  let M := fun _ : t => genericAffineSquare K n m
  let P := fun _ : t => genericAffineRows K n m
  have hM : DegreeBound (blockDiagonal M) 1 :=
    blockDiagonal_degreeBound_one M (fun _ => genericAffineSquare_degree K n m)
  have hP : DegreeBound (blockDiagonal P) 1 :=
    blockDiagonal_degreeBound_one P (fun _ => genericAffineRows_degree K n m)
  let σ : K →+* AffineCoefficientField K (MatrixParameters n m) :=
    (algebraMap (MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K) _).comp MvPolynomial.C
  apply le_antisymm
  · have hh := generic_observability_kernel_le_field_witness σ (blockDiagonal M) (blockDiagonal P)
      hM hP q d
    rw [observability_blocks_kernel_finrank] at hh
    have hb := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
      (generic_corank_one_observability_alpha_degrees (K := K) q hn) d
    simpa only [M,P,hb,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
      Finset.sum_const,Finset.card_univ,smul_eq_mul] using hh
  · have hsize : q*Fintype.card (m × t) ≤ Fintype.card (n × t) := by
      simp only [Fintype.card_prod,hn]
      nlinarith
    have hh := prescribed_matrix_kernel_lower
      (observabilityMatrix (genericAffineSquare K (n × t) (m × t))
        (genericAffineRows K (n × t) (m × t)) q)
      (fun ij => ij.1.val+1)
      (fun i j => (observability_polynomial_degree_top _ _ q
        (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _) i j).1)
      (by simpa only [Fintype.card_prod,Fintype.card_fin] using hsize) d
    have hs : (∑ ij : Fin q × (m × t), (ij.1.val+1)) =
        Fintype.card t*(Fintype.card m*(∑ i : Fin q, (i.val+1))) := by
      simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_prod,
        smul_eq_mul,← Finset.mul_sum]
      ring
    have hr : Fintype.card (n × t)-q*Fintype.card (m × t)=Fintype.card t := by
      simp only [Fintype.card_prod,hn]
      rw [Nat.add_mul,Nat.mul_assoc,one_mul,Nat.add_sub_cancel_left]
    rw [hs] at hh
    simp only [Fintype.card_prod,Fintype.card_fin] at hh
    simp only [Fintype.card_prod] at hr
    simpa only [hr,← Nat.mul_sub_left_distrib] using hh

theorem generic_corank_one_repeated_alpha_degrees (q : ℕ)
    (hn : Fintype.card n=q*Fintype.card m+1) :
    HasMinimalKernelDegrees (observabilityMatrix
      (genericAffineSquare K (n × t) (m × t))
      (genericAffineRows K (n × t) (m × t)) q)
      (List.replicate (Fintype.card t) (Fintype.card m*(∑ i : Fin q, (i.val+1)))) := by
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [generic_corank_one_repeated_alpha_hilbert q d hn]
  simp

end FD56
