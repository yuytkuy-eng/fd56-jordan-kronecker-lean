/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.TerminalCorankOneGenericFrame
import FD56.Hilbert.GenericNondivisibleSLStructure
import FD56.Hilbert.MinimalDegreeFrameBound

/-! Complete SL classification for n=mq+m-1, with m=s+2 at least two. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 2000000
variable (s : ℕ)

theorem terminalOne_frame_degree_identity (q : ℕ) :
    2*terminalOneFrameDegree s q=(s+2)*q^2+(3*s+4)*q+2*s := by
  have hs := terminalOne_row_weight s q
  simp only [terminalOneLevel] at hs
  rw [Nat.add_assoc,Fin.sum_univ_add] at hs
  simp only [Fin.coe_castAdd,Fin.coe_natAdd] at hs
  have h (i : Fin (s+1)) : ((s+2)*q+i.val)/(s+2)=q := by
    rw [Nat.mul_add_div (by omega : 0<s+2),Nat.div_eq_of_lt (by omega : i.val<s+2),Nat.add_zero]
  simp_rw [h] at hs
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
  nlinarith [residueOne_prefix_row_weight (s+2) q]

variable {K : Type*} [Field K] [CharZero K]

theorem generic_terminal_one_sl_uniform_of_profile
    (q : ℕ) (i₀ : Fin ((s+2)*q+s+1)) (xs : List ℕ) (hlen : xs.length=(s+2))
    (hsum : 2*xs.sum+(s+2)+1=((s+2)*q+s+1)*((s+2)*q+s+1+(s+2)))
    (hmin : HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin ((s+2)*q+s+1)) (Fin (s+2)))
      (genericAffineRows K (Fin ((s+2)*q+s+1)) (Fin (s+2))) i₀) xs) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin ((s+2)*q+s+1)) (Fin (s+2)))
      (genericAffineRows K (Fin ((s+2)*q+s+1)) (Fin (s+2))) i₀)
      (List.replicate (s+2) (terminalOneFrameDegree s q)) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin ((s+2)*q+s+1)) (Fin (s+2)))
      (genericAffineRows K (Fin ((s+2)*q+s+1)) (Fin (s+2))) i₀)
      (List.replicate (s+2) (terminalOneFrameDegree s q)) := by
  have hs : xs.sum=(s+2)*terminalOneFrameDegree s q := by
    have he := terminalOne_frame_degree_identity s q
    nlinarith
  obtain ⟨Z,hAZ,hZ,hinj⟩ := generic_terminal_one_sl_kernel_frame (K:=K) s q i₀
  have hfinal := minimal_degrees_uniform_of_full_frame_at_point _ xs hmin
    (s+2) (terminalOneFrameDegree s q) Z hlen hs hAZ hZ 0 hinj
  refine ⟨hfinal,slKirillovMatrix_kronecker _ _ i₀ _
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _) hfinal ?_⟩
  rw [slChartInput_card,nat_list_affine_sum]
  simp only [List.sum_replicate,List.length_replicate,smul_eq_mul,SLInput,
    Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  rw [Nat.mul_add] at hsum
  omega

theorem generic_terminal_one_sl_minimal_and_kronecker
    (q : ℕ) (i₀ : Fin ((s+2)*q+s+1)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin ((s+2)*q+s+1)) (Fin (s+2)))
      (genericAffineRows K (Fin ((s+2)*q+s+1)) (Fin (s+2))) i₀)
      (List.replicate (s+2) (terminalOneFrameDegree s q)) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin ((s+2)*q+s+1)) (Fin (s+2)))
      (genericAffineRows K (Fin ((s+2)*q+s+1)) (Fin (s+2))) i₀)
      (List.replicate (s+2) (terminalOneFrameDegree s q)) := by
  cases q with
  | zero =>
    have hdiff : s+2-(s+1)=1 := by omega
    have hdeg : (s+1)*(s+1)-1=s*(s+2) := by
      rw [show (s+1)*(s+1)=s*(s+2)+1 by ring]
      omega
    constructor
    · simpa [terminalOneFrameDegree,balancedDegreeList,hdiff,hdeg] using
        generic_above_sl_minimal_degrees (K:=K) (m:=Fin (s+2)) i₀ (by simp)
    · simpa [terminalOneFrameDegree,balancedDegreeList,hdiff,hdeg] using
        generic_above_sl_kronecker_decomposition (K:=K) (m:=Fin (s+2)) i₀ (by simp)
  | succ q =>
    obtain ⟨xs,hlen,hsum,hmin,_⟩ := generic_nondivisible_sl_kronecker_structure
      (K:=K) (n:=Fin ((s+2)*(q+1)+s+1)) (m:=Fin (s+2)) (q+1) (by omega) i₀
      (by simp only [Fintype.card_fin]; nlinarith)
      (by simp only [Fintype.card_fin]; nlinarith)
    have hl : xs.length=s+2 := by
      simp only [Fintype.card_fin] at hlen
      rw [show (s+2)*(q+1)+s+1-(q+1)*(s+2)=s+1 by
          rw [Nat.mul_comm (q+1) (s+2)]; omega,
        show (q+1+1)*(s+2)-((s+2)*(q+1)+s+1)=1 by
          rw [show (q+1+1)*(s+2)=(s+2)*(q+1)+(s+2) by ring]; omega] at hlen
      omega
    exact generic_terminal_one_sl_uniform_of_profile s (q+1) i₀ xs hl
      (by simpa only [Fintype.card_fin,hl] using hsum) hmin

theorem generic_terminal_one_sl_hilbert (q d : ℕ) :
    slHilbert (genericAffineSquare K (Fin ((s+2)*q+s+1)) (Fin (s+2)))
      (genericAffineRows K (Fin ((s+2)*q+s+1)) (Fin (s+2))) d=(s+2)*(d+1-terminalOneFrameDegree s q) := by
  rw [slHilbert_eq_matrix_kernel _ _ (0 : Fin ((s+2)*q+s+1)),
    (hasMinimalKernelDegrees_iff_hilbert _ _).mp
      (generic_terminal_one_sl_minimal_and_kronecker s q 0).1]
  simp

end FD56
