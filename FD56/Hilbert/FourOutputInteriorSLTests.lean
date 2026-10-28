/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericNondivisibleSLStructure
import FD56.Hilbert.MinimalDegreeBudgetTests

/-! Two bounded-kernel tests suffice for the balanced SL profile in sizes
(4q+2,4). The tests remain explicit hypotheses. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K]

theorem generic_four_output_interior_sl_degree_budget
    (q : ℕ) (hq : 0<q) (i₀ : Fin (4*q+2)) :
    ∃ xs : List ℕ, xs.length=5 ∧ xs.sum=8*q^2+16*q+3 ∧
      HasMinimalKernelDegrees (slEquationMatrix
        (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
        (genericAffineRows K (Fin (4*q+2)) (Fin 4)) i₀) xs ∧
      HasKroneckerDecomposition (slKirillovMatrix
        (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
        (genericAffineRows K (Fin (4*q+2)) (Fin 4)) i₀) xs := by
  obtain ⟨xs,hl,hs,hmin,hcan⟩ := generic_nondivisible_sl_kronecker_structure
    (K:=K) (n:=Fin (4*q+2)) (m:=Fin 4) q hq i₀
    (by simp only [Fintype.card_fin]; omega) (by simp only [Fintype.card_fin]; omega)
  simp only [Fintype.card_fin] at hl hs
  have hlen : xs.length=5 := by
    rw [show 4*q+2-q*4=2 by omega,show (q+1)*4-(4*q+2)=2 by omega] at hl
    exact hl
  exact ⟨xs,hlen,by nlinarith,hmin,hcan⟩

theorem generic_four_output_interior_sl_balanced_of_two_tests
    (q : ℕ) (hq : 0<q) (i₀ : Fin (4*q+2))
    (hzero : slHilbert (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
      (genericAffineRows K (Fin (4*q+2)) (Fin 4)) ((8*q^2+16*q+3)/5-1)=0)
    (hcritical : slHilbert (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
      (genericAffineRows K (Fin (4*q+2)) (Fin 4)) ((8*q^2+16*q+3)/5)
        ≤5-(8*q^2+16*q+3)%5) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
      (genericAffineRows K (Fin (4*q+2)) (Fin 4)) i₀)
      (balancedDegreeList (8*q^2+16*q+3) 5) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
      (genericAffineRows K (Fin (4*q+2)) (Fin 4)) i₀)
      (balancedDegreeList (8*q^2+16*q+3) 5) := by
  obtain ⟨xs,hlen,hsum,hmin,_⟩ := generic_four_output_interior_sl_degree_budget (K:=K) q hq i₀
  let S := 8*q^2+16*q+3
  have hS : 5≤S := by dsimp [S]; nlinarith
  have hr : S%5<5 := Nat.mod_lt _ (by decide)
  have hc : (5-S%5)+S%5=5 := by omega
  have hd : (S/5)*((5-S%5)+S%5)+S%5=S := by rw [hc]; omega
  have hfinal := minimal_degrees_balanced_of_budget_tests _ xs hmin (S/5)
    (5-S%5) (S%5) (by omega) (by omega) (by omega)
    (by change xs.sum=_; rw [hd]; exact hsum)
    (by rw [← slHilbert_eq_matrix_kernel]; exact hzero)
    (by rw [← slHilbert_eq_matrix_kernel]; exact hcritical)
  rw [hd,hc] at hfinal
  refine ⟨hfinal,slKirillovMatrix_kronecker _ _ i₀ _
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _) hfinal ?_⟩
  rw [slChartInput_card,nat_list_affine_sum,
    balancedDegreeList_sum S 5 (by decide),balancedDegreeList_length S 5 (by decide)]
  simp only [SLInput,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  dsimp [S]
  rw [show (4*q+2)*(4*q+2)+(4*q+2)*4=2*(8*q^2+16*q+3)+6 by ring]
  omega

end FD56
