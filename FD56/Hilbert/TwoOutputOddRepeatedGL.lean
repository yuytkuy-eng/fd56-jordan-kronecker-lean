/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.CorankOneRepeatedAlpha
import FD56.Hilbert.CorankOneRepeatedBeta
import FD56.Hilbert.TwoOutputOddGL
import FD56.Hilbert.GenericObservabilityGLTransfer

/-! Equal Kronecker blocks for repetitions of every odd state size with two outputs. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m t : Type*} [Field K] [Fintype n] [Fintype m] [Fintype t]
  [DecidableEq n] [DecidableEq m] [DecidableEq t] [Nonempty t]

theorem generic_two_output_odd_repeated_gl_minimal_degrees (q : ℕ)
    (hm : Fintype.card m=2) (hn : Fintype.card n=2*q+1) :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (n × t) (m × t))
      (genericAffineRows K (n × t) (m × t)))
      (List.replicate (Fintype.card t^2) (2*q^2+4*q+1)) := by
  have ht : 0 < Fintype.card t := Fintype.card_pos
  cases q with
  | zero =>
    have hsize : Fintype.card (n × t) < Fintype.card (m × t) := by
      simp only [Fintype.card_prod,hm,hn]
      nlinarith
    have h := generic_above_gl_minimal_degrees (K := K) hsize
    have hd : 2*Fintype.card t-Fintype.card t=Fintype.card t := by omega
    simpa only [Fintype.card_prod,hm,hn,Nat.mul_zero,Nat.zero_add,Nat.one_mul,
      hd,Nat.mod_self,Nat.div_self ht,Nat.mul_zero,List.replicate_zero,
      Nat.sub_zero,List.nil_append,pow_two,Nat.zero_mul,zero_add] using h
  | succ q =>
    have hsize : (q+1)*Fintype.card (m × t) < Fintype.card (n × t) := by
      simp only [Fintype.card_prod,hm,hn]
      nlinarith
    have hsize' : Fintype.card (n × t) ≤ (q+2)*Fintype.card (m × t) := by
      simp only [Fintype.card_prod,hm,hn]
      nlinarith
    have hα := generic_corank_one_repeated_alpha_degrees (K := K) (t := t)
      (q+1) (show Fintype.card n=(q+1)*Fintype.card m+1 by rw [hm,hn]; omega)
    have hα' : HasMinimalKernelDegrees (observabilityMatrix
        (genericAffineSquare K (n × t) (m × t))
        (genericAffineRows K (n × t) (m × t)) (q+1))
        (List.replicate (Fintype.card t) ((q+1)*(q+2))) := by
      simpa only [hm,twice_sum_fin_positive] using hα
    have hβd : (q+2)*(q+2+1)-(q+2)=(q+2)^2 := by
      rw [show (q+2)*(q+2+1)=(q+2)^2+(q+2) by ring,Nat.add_sub_cancel]
    have hβ : ∀ (r : ℕ) (B : Basis (Fin r)
        (AffineCoefficientField K (MatrixParameters (n × t) (m × t)))[X]
        (LinearMap.ker (Matrix.toLin' (observabilityMatrix
          (genericAffineSquare K (n × t) (m × t))
          (genericAffineRows K (n × t) (m × t)) (q+1))))),
        HasMinimalKernelDegrees (genericAffineRows K (n × t) (m × t) *
          (genericAffineSquare K (n × t) (m × t))^(q+1) *
          polynomialKernelBasisMatrix _ B).transpose
          (List.replicate (Fintype.card t) ((q+2)^2)) := by
      intro r B
      have h := generic_corank_one_repeated_beta_degrees (q+1) (by omega : 2 ≤ Fintype.card m)
        (show Fintype.card n+1=(q+1+1)*Fintype.card m by rw [hm,hn]; omega) B
      simpa only [hm,twice_sum_fin_positive,hβd] using h
    have h := generic_observability_gl_minimal_degrees_of_auxiliary_profiles q
      hsize hsize' _ _ hα' hβ
    have he : (q+1)*(q+2)+(q+2)^2+1+q=2*(q+1)^2+4*(q+1)+1 := by ring
    simp only [degreeConvolution,List.flatMap_replicate,List.map_replicate,
      List.flatten_replicate_replicate] at h
    rw [show Fintype.card t*Fintype.card t=Fintype.card t^2 by ring,he] at h
    exact h

theorem generic_two_output_odd_repeated_gl_kronecker_decomposition (q : ℕ)
    (hm : Fintype.card m=2) (hn : Fintype.card n=2*q+1) :
    HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K (n × t) (m × t))
      (genericAffineRows K (n × t) (m × t)))
      (List.replicate (Fintype.card t^2) (2*q^2+4*q+1)) := by
  apply glKirillovMatrix_kronecker _ _ _
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
    (generic_two_output_odd_repeated_gl_minimal_degrees q hm hn)
  simp only [SLInput,Fintype.card_sum,Fintype.card_prod,hm,hn,List.map_replicate,
    List.sum_replicate,smul_eq_mul]
  ring

end FD56
