/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ResidueOneGenericFrame
import FD56.Hilbert.GenericNondivisibleSLStructure
import FD56.Hilbert.MinimalDegreeFrameBound

/-! Complete SL classification in every residue-one family n=mq+1, m at least two. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 2000000
variable (m : ℕ) [NeZero m]

theorem residueOne_frame_degree_identity (q : ℕ) :
    2*residueOneFrameDegree m q=m*q^2+(m+2)*q := by
  have hs := residueOne_row_weight m q
  simp only [residueOneLevel,Fin.sum_univ_castSucc,Fin.coe_castSucc,Fin.val_last] at hs
  rw [Nat.mul_div_cancel_left q (NeZero.pos m)] at hs
  nlinarith [residueOne_prefix_row_weight m q]

variable {K : Type*} [Field K] [CharZero K]

theorem generic_residue_one_sl_uniform_of_profile
    (q : ℕ) (i₀ : Fin (m*q+1)) (xs : List ℕ) (hlen : xs.length=m)
    (hsum : 2*xs.sum+m+1=(m*q+1)*(m*q+1+m))
    (hmin : HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (m*q+1)) (Fin m))
      (genericAffineRows K (Fin (m*q+1)) (Fin m)) i₀) xs) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (m*q+1)) (Fin m))
      (genericAffineRows K (Fin (m*q+1)) (Fin m)) i₀)
      (List.replicate m (residueOneFrameDegree m q)) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (m*q+1)) (Fin m))
      (genericAffineRows K (Fin (m*q+1)) (Fin m)) i₀)
      (List.replicate m (residueOneFrameDegree m q)) := by
  have hs : xs.sum=m*residueOneFrameDegree m q := by
    have he := residueOne_frame_degree_identity m q
    nlinarith
  obtain ⟨Z,hAZ,hZ,hinj⟩ := generic_residue_one_sl_kernel_frame (K:=K) m q i₀
  have hfinal := minimal_degrees_uniform_of_full_frame_at_point _ xs hmin
    m (residueOneFrameDegree m q) Z hlen hs hAZ hZ 0 hinj
  refine ⟨hfinal,slKirillovMatrix_kronecker _ _ i₀ _
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _) hfinal ?_⟩
  rw [slChartInput_card,nat_list_affine_sum]
  simp only [List.sum_replicate,List.length_replicate,smul_eq_mul,SLInput,
    Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  rw [Nat.mul_add] at hsum
  omega

theorem generic_residue_one_sl_minimal_and_kronecker (hm : 2≤m)
    (q : ℕ) (i₀ : Fin (m*q+1)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (m*q+1)) (Fin m))
      (genericAffineRows K (Fin (m*q+1)) (Fin m)) i₀)
      (List.replicate m (residueOneFrameDegree m q)) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (m*q+1)) (Fin m))
      (genericAffineRows K (Fin (m*q+1)) (Fin m)) i₀)
      (List.replicate m (residueOneFrameDegree m q)) := by
  cases q with
  | zero =>
    have hcount : m-1+1=m := by omega
    constructor
    · simpa [residueOneFrameDegree,balancedDegreeList,hcount] using
        generic_above_sl_minimal_degrees (K:=K) (m:=Fin m) i₀ (by simpa using hm)
    · simpa [residueOneFrameDegree,balancedDegreeList,hcount] using
        generic_above_sl_kronecker_decomposition (K:=K) (m:=Fin m) i₀ (by simpa using hm)
  | succ q =>
    obtain ⟨xs,hlen,hsum,hmin,_⟩ := generic_nondivisible_sl_kronecker_structure
      (K:=K) (n:=Fin (m*(q+1)+1)) (m:=Fin m) (q+1) (by omega) i₀
      (by simp only [Fintype.card_fin]; nlinarith)
      (by simp only [Fintype.card_fin]; nlinarith)
    have hl : xs.length=m := by
      simp only [Fintype.card_fin] at hlen
      rw [show m*(q+1)+1-(q+1)*m=1 by rw [Nat.mul_comm (q+1) m]; omega,
        show (q+1+1)*m-(m*(q+1)+1)=m-1 by
          rw [show (q+1+1)*m=m*(q+1)+m by ring]; omega] at hlen
      omega
    exact generic_residue_one_sl_uniform_of_profile m (q+1) i₀ xs hl
      (by simpa only [Fintype.card_fin,hl] using hsum) hmin

theorem generic_residue_one_sl_hilbert (hm : 2≤m) (q d : ℕ) :
    slHilbert (genericAffineSquare K (Fin (m*q+1)) (Fin m))
      (genericAffineRows K (Fin (m*q+1)) (Fin m)) d=m*(d+1-residueOneFrameDegree m q) := by
  rw [slHilbert_eq_matrix_kernel _ _ (0 : Fin (m*q+1)),
    (hasMinimalKernelDegrees_iff_hilbert _ _).mp
      (generic_residue_one_sl_minimal_and_kronecker m hm q 0).1]
  simp

end FD56
