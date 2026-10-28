/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.FourOutputSLDualDegrees
import FD56.Hilbert.BalancedDegreeProfile
import FD56.Hilbert.ConstantEquivalence

/-! Balance of the actual six-minor polar row implies the balanced generic
SL profile and its full Kronecker decomposition. The polar profile is the
only additional hypothesis. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 2000000

private theorem minimal_degree_lists_perm
    {K a n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (A : Matrix a n K[X]) (xs ys : List ℕ)
    (hx : HasMinimalKernelDegrees A xs) (hy : HasMinimalKernelDegrees A ys) :
    xs.Perm ys := by
  apply listHilbert_determines_indices
  intro d
  rw [listHilbert_nat,listHilbert_nat]
  exact_mod_cast ((hasMinimalKernelDegrees_iff_hilbert A xs).mp hx d).symm.trans
    ((hasMinimalKernelDegrees_iff_hilbert A ys).mp hy d)

private theorem balanced_member_bounds (S k x : ℕ)
    (hx : x∈balancedDegreeList S k) : S/k≤x ∧ x≤S/k+1 := by
  simp only [balancedDegreeList,List.mem_append,List.mem_replicate] at hx
  rcases hx with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> omega

variable {K : Type*} [Field K]

private def polarChangeMatrix : Matrix (Fin 6) (Fin 6) K :=
  ![![0,0,0,0,0,1],![0,0,0,0,-1,0],![0,0,0,1,0,0],
    ![0,0,1,0,0,0],![0,-1,0,0,0,0],![1,0,0,0,0,0]]

private theorem polarChangeMatrix_square :
    polarChangeMatrix (K:=K)*polarChangeMatrix (K:=K)=1 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [polarChangeMatrix,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply]

private theorem polarChangeMatrix_mul (F : Fin 6 → K[X]) :
    ((show Matrix Unit (Fin 6) K[X] from fun _ => F)*(polarChangeMatrix (K:=K)).map C :
      Matrix Unit (Fin 6) K[X])=pluckerPolarRow F := by
  funext i j
  cases i
  fin_cases j <;>
    simp [polarChangeMatrix,pluckerPolarRow,Matrix.mul_apply,Fin.sum_univ_succ]

theorem pluckerPolarRow_minimal_degrees_iff (F : Fin 6 → K[X]) (xs : List ℕ) :
    HasMinimalKernelDegrees (pluckerPolarRow F) xs ↔
      HasMinimalKernelDegrees (fun _ : Unit => F) xs := by
  have hHilbert (d : ℕ) :
      Module.finrank K (polynomialKernelAtDegree (pluckerPolarRow F) d)=
        Module.finrank K (polynomialKernelAtDegree (fun _ : Unit => F) d) := by
    apply constant_equivalence_kernel_hilbert (fun _ : Unit => F)
      (pluckerPolarRow F) 1 1 polarChangeMatrix polarChangeMatrix
    · simpa using polarChangeMatrix_mul F
    · rw [← polarChangeMatrix_mul F,Matrix.mul_assoc,← Matrix.map_mul,polarChangeMatrix_square]
      simp
    · exact polarChangeMatrix_square
    · exact polarChangeMatrix_square
  rw [hasMinimalKernelDegrees_iff_hilbert,hasMinimalKernelDegrees_iff_hilbert]
  constructor
  · intro h d
    rw [← hHilbert]
    exact h d
  · intro h d
    rw [hHilbert]
    exact h d

theorem generic_four_output_sl_minimal_degrees_of_balanced_polar
    (q : ℕ) (hq : 0<q) (i₀ : Fin (4*q+2))
    (hpolar : HasMinimalKernelDegrees
      (pluckerPolarRow (genericFourOutputInteriorMinors (K:=K) q))
      (balancedDegreeList (2*(q+1)^2) 5)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
      (genericAffineRows K (Fin (4*q+2)) (Fin 4)) i₀)
      (balancedDegreeList (8*q^2+16*q+3) 5) := by
  obtain ⟨e,he,hsl,hdual⟩ := generic_four_output_sl_dual_degrees (K:=K) q hq i₀
  have hp := minimal_degree_lists_perm _ _ _ hdual hpolar
  have hb (i : Fin 5) : (2*(q+1)^2)/5≤2*(q+1)^2-1-e i ∧
      2*(q+1)^2-1-e i≤(2*(q+1)^2)/5+1 := by
    apply balanced_member_bounds
    exact hp.mem_iff.mp (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have hbalance : ∀ i j, e i≤e j+1 := by
    intro i j
    have hi := hb i
    have hj := hb j
    have hei := he i
    have hej := he j
    omega
  obtain ⟨xs,_,hxSum,hxMin,_⟩ := generic_four_output_interior_sl_degree_budget (K:=K) q hq i₀
  have heSum : (∑ i, e i)=8*q^2+16*q+3 := by
    have h := (minimal_degree_lists_perm _ _ _ hsl hxMin).sum_eq
    simpa only [List.sum_ofFn,hxSum] using h
  have hpSL := pairwise_balanced_degrees_perm (by decide : 0<5) e hbalance
  rw [heSum] at hpSL
  obtain ⟨r,B,d,hB,hL,hperm⟩ := hsl
  exact ⟨r,B,d,hB,hL,hperm.trans hpSL⟩

theorem generic_four_output_sl_kronecker_of_balanced_polar
    (q : ℕ) (hq : 0<q) (i₀ : Fin (4*q+2))
    (hpolar : HasMinimalKernelDegrees
      (pluckerPolarRow (genericFourOutputInteriorMinors (K:=K) q))
      (balancedDegreeList (2*(q+1)^2) 5)) :
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
      (genericAffineRows K (Fin (4*q+2)) (Fin 4)) i₀)
      (balancedDegreeList (8*q^2+16*q+3) 5) := by
  apply slKirillovMatrix_kronecker _ _ i₀ _
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
    (generic_four_output_sl_minimal_degrees_of_balanced_polar q hq i₀ hpolar)
  rw [slChartInput_card,nat_list_affine_sum,
    balancedDegreeList_sum _ 5 (by decide),balancedDegreeList_length _ 5 (by decide)]
  simp only [SLInput,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  rw [show (4*q+2)*(4*q+2)+(4*q+2)*4=2*(8*q^2+16*q+3)+6 by ring]
  omega

end FD56
