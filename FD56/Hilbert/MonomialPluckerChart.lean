/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedMonomialPlucker
import FD56.Hilbert.ConstantEquivalence
import FD56.LinearAlgebra.DualConstant

/-! Two constant output shears put the balanced Plucker row in a coprime full-degree chart. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- The exterior-square action of row1 += row4 and row2 += row3. -/
def pluckerChartShear (F : Fin 6 → K[X]) : Fin 6 → K[X] :=
  ![F 0+F 1-F 4-F 5, F 1-F 5, F 2, F 3, F 4+F 5, F 5]

private def chartShearMatrix : Matrix (Fin 6) (Fin 6) K :=
  ![![1,0,0,0,0,0], ![1,1,0,0,0,0], ![0,0,1,0,0,0],
    ![0,0,0,1,0,0], ![-1,0,0,0,1,0], ![-1,-1,0,0,1,1]]

private def chartShearInverse : Matrix (Fin 6) (Fin 6) K :=
  ![![1,0,0,0,0,0], ![-1,1,0,0,0,0], ![0,0,1,0,0,0],
    ![0,0,0,1,0,0], ![1,0,0,0,1,0], ![-1,1,0,0,-1,1]]

private theorem chartShear_inverse :
    chartShearMatrix (K:=K)*chartShearInverse (K:=K)=1 ∧
      chartShearInverse (K:=K)*chartShearMatrix (K:=K)=1 := by
  constructor <;> funext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [chartShearMatrix,chartShearInverse,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply]

private theorem chartShear_mul (F : Fin 6 → K[X]) :
    ((show Matrix Unit (Fin 6) K[X] from fun _ => F)*(chartShearMatrix (K:=K)).map C :
      Matrix Unit (Fin 6) K[X]) =
      (fun _ : Unit => pluckerChartShear F) := by
  funext i j
  fin_cases j <;>
    simp [chartShearMatrix,pluckerChartShear,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring

theorem pluckerChartShear_relation (F : Fin 6 → K[X]) :
    pluckerChartShear F 0*pluckerChartShear F 5-
      pluckerChartShear F 1*pluckerChartShear F 4+
      pluckerChartShear F 2*pluckerChartShear F 3 = F 0*F 5-F 1*F 4+F 2*F 3 := by
  simp [pluckerChartShear]
  ring

theorem pluckerChartShear_minimal_degrees (F : Fin 6 → K[X]) (xs : List ℕ)
    (hmin : HasMinimalKernelDegrees (fun _ : Unit => F) xs) :
    HasMinimalKernelDegrees (fun _ : Unit => pluckerChartShear F) xs := by
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [← (hasMinimalKernelDegrees_iff_hilbert _ _).mp hmin d]
  apply constant_equivalence_kernel_hilbert (fun _ : Unit => F)
    (fun _ : Unit => pluckerChartShear F) 1 1 chartShearMatrix chartShearInverse
  · simpa using chartShear_mul F
  · rw [← chartShear_mul F,Matrix.mul_assoc,← Matrix.map_mul,chartShear_inverse.1]
    simp
  · exact chartShear_inverse.1
  · exact chartShear_inverse.2

def monomialPluckerChart (a b c : ℕ) : Fin 6 → K[X] :=
  pluckerChartShear (monomialPluckerRow a b c)

theorem monomialPluckerChart_bezout (a b c : ℕ) :
    (1-2*X^(a+2*b+c) : K[X])*monomialPluckerChart (K:=K) a b c 0+
      (4*X^(2*b+c)-(1-2*X^(a+2*b+c)))*monomialPluckerChart (K:=K) a b c 1=1 := by
  simp [monomialPluckerChart,pluckerChartShear,monomialPluckerRow,pow_add,pow_mul]
  ring

theorem monomialPluckerChart_coprime (a b c : ℕ) :
    IsCoprime (monomialPluckerChart (K:=K) a b c 0) (monomialPluckerChart (K:=K) a b c 1) :=
  ⟨1-2*X^(a+2*b+c),4*X^(2*b+c)-(1-2*X^(a+2*b+c)),monomialPluckerChart_bezout a b c⟩

theorem monomialPluckerChart_degree_bound (a b c : ℕ) :
    ∀ i, (monomialPluckerChart (K:=K) a b c i).natDegree≤2*a+2*b+c := by
  have hf : ∀ (_ : Unit) j, (monomialPluckerRow (K:=K) a b c j).natDegree≤2*a+2*b+c := by
    intro i j
    fin_cases j <;> simp [monomialPluckerRow] <;> try omega
    apply Polynomial.natDegree_mul_le.trans
    simp
    omega
  have hh := mul_constant_row_degree (fun _ : Unit => monomialPluckerRow (K:=K) a b c)
    chartShearMatrix (fun _ => 2*a+2*b+c) hf
  rw [chartShear_mul] at hh
  exact fun i => hh () i

theorem monomialPluckerChart_first_degree (a b c : ℕ) (ha : 0<a) :
    (monomialPluckerChart (K:=K) a b c 0).natDegree=2*a+2*b+c := by
  have h0 : 2*a+2*b+c≠0 := by omega
  have h1 : 2*a+2*b+c≠a := by omega
  have h2 : 2*a+2*b+c≠a+2*b+c := by omega
  have h3 : 2*a≠a := by omega
  have hc : (monomialPluckerChart (K:=K) a b c 0).coeff (2*a+2*b+c) = -1 := by
    change (1+X^a-2*X^(a+2*b+c)-X^(2*a+2*b+c) : K[X]).coeff (2*a+2*b+c) = -1
    rw [show (2*X^(a+2*b+c) : K[X])=X^(a+2*b+c)+X^(a+2*b+c) by ring]
    simp [Polynomial.coeff_X_pow,Polynomial.coeff_one,h0,h1,h2,h3,
      Nat.ne_of_gt ha,Ne.symm h1,Ne.symm h2]
  apply Nat.le_antisymm (monomialPluckerChart_degree_bound a b c 0)
  exact Polynomial.le_natDegree_of_ne_zero (by rw [hc]; exact neg_ne_zero.mpr one_ne_zero)

variable [CharZero K]

theorem monomialPluckerChart_minimal_degrees (a b c : ℕ) :
    HasMinimalKernelDegrees (fun _ : Unit => monomialPluckerChart (K:=K) a b c) [a,b,c,b,a] :=
  pluckerChartShear_minimal_degrees _ _ (monomialPlucker_minimal_degrees a b c)

theorem balancedMonomialPluckerChart_certificate (W : ℕ) (hW : 5≤W) :
    let F := monomialPluckerChart (K:=K) (pluckerGapA W) (pluckerGapB W) (pluckerGapC W)
    (∀ i, (F i).natDegree≤W) ∧ (F 0).natDegree=W ∧ IsCoprime (F 0) (F 1) ∧
      F 0*F 5-F 1*F 4+F 2*F 3=0 ∧
      HasMinimalKernelDegrees (fun _ : Unit => F) (balancedDegreeList W 5) := by
  dsimp only
  have hs := pluckerGap_sum W
  refine ⟨?_,?_,monomialPluckerChart_coprime _ _ _,?_,?_⟩
  · simpa only [hs] using monomialPluckerChart_degree_bound (K:=K)
      (pluckerGapA W) (pluckerGapB W) (pluckerGapC W)
  · rw [monomialPluckerChart_first_degree _ _ _ (by simp only [pluckerGapA]; omega),hs]
  · rw [monomialPluckerChart,pluckerChartShear_relation]
    exact monomialPlucker_relation _ _ _
  · exact pluckerChartShear_minimal_degrees _ _ (balancedMonomialPlucker_minimal_degrees W)

end FD56
