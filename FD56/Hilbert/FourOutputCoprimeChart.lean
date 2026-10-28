/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialRowProjectionExtension
import FD56.Hilbert.FourOutputInteriorMinors
import FD56.LinearAlgebra.PluckerOutputActionTransport
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Constant base-field row changes giving a coprime chart for a split
four-by-two polynomial matrix over an extension field. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- A constant base-field row applied to the polynomial matrix. -/
def fourOutputConstantRow (G : Matrix (Fin 4) (Fin 2) L[X]) (u : Fin 4 → K) : Fin 2 → L[X] :=
  fun j => ∑ i, C (algebraMap K L (u i))*G i j

/-- The alternating minor of two constant base-field rows. -/
def fourOutputConstantMinor (G : Matrix (Fin 4) (Fin 2) L[X]) (u v : Fin 4 → K) : L[X] :=
  fourOutputConstantRow G u 0*fourOutputConstantRow G v 1-
    fourOutputConstantRow G u 1*fourOutputConstantRow G v 0

private theorem constantRow_single (G : Matrix (Fin 4) (Fin 2) L[X])
    (i : Fin 4) (j : Fin 2) :
    fourOutputConstantRow G (Pi.single i (1:K)) j=G i j := by
  classical
  simp [fourOutputConstantRow,Pi.single_apply]

private theorem constantRow_smul (G : Matrix (Fin 4) (Fin 2) L[X])
    (u : Fin 4 → K) (a : K) (j : Fin 2) :
    fourOutputConstantRow G (a • u) j=C (algebraMap K L a)*fourOutputConstantRow G u j := by
  simp only [fourOutputConstantRow,Pi.smul_apply,smul_eq_mul,map_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem constantRow_degree (G : Matrix (Fin 4) (Fin 2) L[X])
    (d : ℕ) (hG : ∀ i j, (G i j).natDegree≤d) (u : Fin 4 → K) (j : Fin 2) :
    (fourOutputConstantRow G u j).natDegree≤d := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_C_mul_le _ _).trans (hG i j)

private theorem constantRow_coeff (G : Matrix (Fin 4) (Fin 2) L[X])
    (d : ℕ) (u : Fin 4 → K) (j : Fin 2) :
    (fourOutputConstantRow G u j).coeff d=∑ i, algebraMap K L (u i)*(G i j).coeff d := by
  simp [fourOutputConstantRow,finset_sum_coeff,coeff_C_mul]

private theorem constantMinor_degree (G : Matrix (Fin 4) (Fin 2) L[X])
    (d : ℕ) (hG : ∀ i j, (G i j).natDegree≤d) (u v : Fin 4 → K) :
    (fourOutputConstantMinor G u v).natDegree≤2*d := by
  unfold fourOutputConstantMinor
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact natDegree_mul_le.trans (by
      have h0 := constantRow_degree G d hG u 0
      have h1 := constantRow_degree G d hG v 1
      omega)
  · exact natDegree_mul_le.trans (by
      have h0 := constantRow_degree G d hG u 1
      have h1 := constantRow_degree G d hG v 0
      omega)

private theorem constantMinor_coeff (G : Matrix (Fin 4) (Fin 2) L[X])
    (d : ℕ) (hG : ∀ i j, (G i j).natDegree≤d) (u v : Fin 4 → K) :
    (fourOutputConstantMinor G u v).coeff (2*d)=
      (fourOutputConstantRow G u 0).coeff d*(fourOutputConstantRow G v 1).coeff d-
      (fourOutputConstantRow G u 1).coeff d*(fourOutputConstantRow G v 0).coeff d := by
  unfold fourOutputConstantMinor
  rw [coeff_sub,show 2*d=d+d by omega,
    coeff_mul_add_eq_of_natDegree_le (constantRow_degree G d hG u 0) (constantRow_degree G d hG v 1),
    coeff_mul_add_eq_of_natDegree_le (constantRow_degree G d hG u 1) (constantRow_degree G d hG v 0)]

private theorem primitive_minor_functional (G : Matrix (Fin 4) (Fin 2) L[X])
    (R : Matrix (Fin 2) (Fin 4) L[X]) (hRG : R*G=1)
    (u : Fin 4 → K)
    (hu : IsCoprime (fourOutputConstantRow G u 0) (fourOutputConstantRow G u 1)) :
    ∃ a : Fin 4 → L[X],
      ∑ i, (fourOutputConstantRow G u 0*G i 1-fourOutputConstantRow G u 1*G i 0)*a i=1 := by
  obtain ⟨a,b,hab⟩ := hu
  refine ⟨fun i => a*R 1 i-b*R 0 i,?_⟩
  have h00 := congrFun (congrFun hRG 0) 0
  have h01 := congrFun (congrFun hRG 0) 1
  have h10 := congrFun (congrFun hRG 1) 0
  have h11 := congrFun (congrFun hRG 1) 1
  simp only [Matrix.mul_apply,Matrix.one_apply,Fin.isValue,ite_true,ite_false,Fin.zero_ne_one,
    Ne.symm Fin.zero_ne_one] at h00 h01 h10 h11
  calc
    _=a*fourOutputConstantRow G u 0*(∑ i, R 1 i*G i 1)-
        b*fourOutputConstantRow G u 0*(∑ i, R 0 i*G i 1)-
        a*fourOutputConstantRow G u 1*(∑ i, R 1 i*G i 0)+
        b*fourOutputConstantRow G u 1*(∑ i, R 0 i*G i 0) := by
      simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _=1 := by rw [h00,h01,h10,h11]; simpa using hab

private theorem minor_functional_eq (G : Matrix (Fin 4) (Fin 2) L[X]) (u v : Fin 4 → K) :
    (∑ i, C (algebraMap K L (v i))*
      (fourOutputConstantRow G u 0*G i 1-fourOutputConstantRow G u 1*G i 0))=
      fourOutputConstantMinor G u v := by
  simp only [fourOutputConstantMinor,fourOutputConstantRow,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem short_span_ne_top {t : ℕ} (ht : t<4) (v : Fin t → (Fin 4 → K)) :
    Submodule.span K (Set.range v)≠⊤ := by
  intro he
  have h := finrank_le_of_span_eq_top he
  simp only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul,mul_one] at h
  omega

private theorem complete_three_rows [Infinite K] (u v w : Fin 4 → K)
    (huv : LinearIndependent K ![u,v])
    (hw : w∉Submodule.span K (Set.range ![u,v])) :
    ∃ Q : Matrix (Fin 4) (Fin 4) K,
      IsUnit Q ∧ Q 0=u ∧ Q 1=v ∧ Q 2=w := by
  let rows : Fin 3 → (Fin 4 → K) := Fin.snoc ![u,v] w
  have hrows : LinearIndependent K rows := linearIndependent_fin_snoc.mpr ⟨huv,hw⟩
  obtain ⟨z,hz⟩ := exists_avoiding_finite_submodules
    ({Submodule.span K (Set.range rows)} : Finset (Submodule K (Fin 4 → K))) (by
      intro S hS
      obtain rfl := Finset.mem_singleton.mp hS
      exact short_span_ne_top (K:=K) (by omega) rows)
  let Q : Matrix (Fin 4) (Fin 4) K := Fin.snoc rows z
  have hQ : LinearIndependent K Q := linearIndependent_fin_snoc.mpr
    ⟨hrows,hz _ (Finset.mem_singleton_self _)⟩
  refine ⟨Q,Matrix.linearIndependent_rows_iff_isUnit.mp hQ,?_,?_,?_⟩ <;> rfl

private def leadingRowMap (G : Matrix (Fin 4) (Fin 2) L[X]) (d : ℕ) :
    (Fin 4 → K) →ₗ[K] (Fin 2 → L) where
  toFun u j := ∑ i, u i • (G i j).coeff d
  map_add' u v := by ext j; simp [add_smul,Finset.sum_add_distrib]
  map_smul' a u := by ext j; simp [smul_smul,Finset.smul_sum]

private theorem leadingRowMap_apply (G : Matrix (Fin 4) (Fin 2) L[X])
    (d : ℕ) (u : Fin 4 → K) (j : Fin 2) :
    leadingRowMap (K:=K) G d u j=(fourOutputConstantRow G u j).coeff d := by
  rw [constantRow_coeff]
  simp [leadingRowMap,Algebra.smul_def]

private theorem leadingRowMap_ker_ne_top (G : Matrix (Fin 4) (Fin 2) L[X])
    (d : ℕ) (hlead : Function.Injective (Matrix.mulVec (fun i j => (G i j).coeff d))) :
    LinearMap.ker (leadingRowMap (K:=K) G d)≠⊤ := by
  intro he
  have hz (i : Fin 4) (j : Fin 2) : (G i j).coeff d=0 := by
    have hm : Pi.single i (1:K)∈LinearMap.ker (leadingRowMap (K:=K) G d) := by rw [he]; trivial
    have hh := congrFun (LinearMap.mem_ker.mp hm) j
    simpa [leadingRowMap,Pi.single_apply] using hh
  have hh : (Pi.single 0 (1:L) : Fin 2 → L)=0 := hlead (by
    ext i
    simp [Matrix.mulVec,dotProduct,hz])
  have := congrFun hh 0
  simp at this

private theorem exists_full_degree_partner (G : Matrix (Fin 4) (Fin 2) L[X])
    (d : ℕ) (hG : ∀ i j, (G i j).natDegree≤d)
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (G i j).coeff d)))
    (u : Fin 4 → K) (hu : u∉LinearMap.ker (leadingRowMap (K:=K) G d)) :
    ∃ v : Fin 4 → K, fourOutputConstantMinor G u v≠0 ∧
      (fourOutputConstantMinor G u v).natDegree=2*d := by
  let x := (fourOutputConstantRow G u 0).coeff d
  let y := (fourOutputConstantRow G u 1).coeff d
  obtain ⟨i,hi⟩ : ∃ i : Fin 4, x*(G i 1).coeff d-y*(G i 0).coeff d≠0 := by
    by_contra! hz
    have hh : (![-y,x] : Fin 2 → L)=0 := hlead (by
      ext i
      simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.head_cons,Pi.zero_apply,mul_zero,add_zero]
      linear_combination hz i)
    have hy : y=0 := by simpa using congrFun hh 0
    have hx : x=0 := by simpa using congrFun hh 1
    apply hu
    apply LinearMap.mem_ker.mpr
    ext j
    rw [leadingRowMap_apply]
    fin_cases j <;> assumption
  let v : Fin 4 → K := Pi.single i 1
  have hcoeff : (fourOutputConstantMinor G u v).coeff (2*d)≠0 := by
    rw [constantMinor_coeff G d hG]
    simpa only [v,constantRow_single] using hi
  refine ⟨v,?_,natDegree_eq_of_le_of_coeff_ne_zero (constantMinor_degree G d hG u v) hcoeff⟩
  intro hz
  exact hcoeff (by rw [hz]; simp)

private theorem minor_ne_zero_rows_independent (G : Matrix (Fin 4) (Fin 2) L[X])
    (u v : Fin 4 → K) (hminor : fourOutputConstantMinor G u v≠0) :
    LinearIndependent K ![u,v] := by
  have hu : u≠0 := by
    intro hz
    apply hminor
    simp [fourOutputConstantMinor,fourOutputConstantRow,hz]
  apply (LinearIndependent.pair_iff' hu).mpr
  intro a ha
  apply hminor
  rw [← ha]
  unfold fourOutputConstantMinor
  rw [constantRow_smul,constantRow_smul]
  ring

/-- A split polynomial two-plane with independent uniform leading columns
admits a full-degree coprime chart after a constant change over the base field. -/
theorem exists_four_output_coprime_chart_rows [Infinite K]
    (G : Matrix (Fin 4) (Fin 2) L[X])
    (R : Matrix (Fin 2) (Fin 4) L[X]) (hRG : R*G=1)
    (d : ℕ) (hG : ∀ i j, (G i j).natDegree≤d)
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (G i j).coeff d))) :
    ∃ Q : Matrix (Fin 4) (Fin 4) K, IsUnit Q ∧
      (fourOutputConstantMinor G (Q 0) (Q 1)).natDegree=2*d ∧
      IsCoprime (fourOutputConstantMinor G (Q 0) (Q 1))
        (fourOutputConstantMinor G (Q 0) (Q 2)) := by
  classical
  obtain ⟨u,hcop,hu⟩ := exists_coprime_constant_row_projection_extension_avoiding G R hRG
    ({LinearMap.ker (leadingRowMap (K:=K) G d)} : Finset (Submodule K (Fin 4 → K))) (by
      intro S hS
      obtain rfl := Finset.mem_singleton.mp hS
      exact leadingRowMap_ker_ne_top G d hlead)
  change IsCoprime (fourOutputConstantRow G u 0) (fourOutputConstantRow G u 1) at hcop
  obtain ⟨v,hv,hd⟩ := exists_full_degree_partner G d hG hlead u
    (hu _ (Finset.mem_singleton_self _))
  obtain ⟨a,ha⟩ := primitive_minor_functional G R hRG u hcop
  obtain ⟨w,hw,hws⟩ := exists_coprime_constant_polynomial_functional_avoiding
    (fun i => fourOutputConstantRow G u 0*G i 1-fourOutputConstantRow G u 1*G i 0)
    a ha (fourOutputConstantMinor G u v) hv
    ({Submodule.span K (Set.range ![u,v])} : Finset (Submodule K (Fin 4 → K))) (by
      intro S hS
      obtain rfl := Finset.mem_singleton.mp hS
      exact short_span_ne_top (K:=K) (by omega) ![u,v])
  rw [minor_functional_eq] at hw
  obtain ⟨Q,hQ,hQ0,hQ1,hQ2⟩ := complete_three_rows u v w
    (minor_ne_zero_rows_independent G u v hv) (hws _ (Finset.mem_singleton_self _))
  exact ⟨Q,hQ,by simpa only [hQ0,hQ1] using hd,by simpa only [hQ0,hQ1,hQ2] using hw⟩

/-- Exterior minors commute with an arbitrary change of output rows. -/
theorem fourOutputPluckerVector_mul {A : Type*} [CommRing A]
    (Q : Matrix (Fin 4) (Fin 4) A) (G : Matrix (Fin 4) (Fin 2) A) :
    fourOutputPluckerVector (Q*G)=pluckerOutputChange Q (fourOutputPluckerVector G) := by
  ext i
  fin_cases i <;>
    simp [fourOutputPluckerVector,fourOutputPluckerRows,pluckerMinorVector,
      pluckerOutputChange,pluckerUpperCoordinates,pluckerSkewMatrix,
      Matrix.det_fin_two,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring

private theorem base_change_first_minor (G : Matrix (Fin 4) (Fin 2) L[X])
    (Q : Matrix (Fin 4) (Fin 4) K) :
    fourOutputPluckerVector (Q.map (C.comp (algebraMap K L))*G) 0=
      fourOutputConstantMinor G (Q 0) (Q 1) := by
  simp [fourOutputPluckerVector,fourOutputPluckerRows,pluckerMinorVector,
    Matrix.det_fin_two,Matrix.mul_apply,fourOutputConstantMinor,fourOutputConstantRow]

private theorem base_change_second_minor (G : Matrix (Fin 4) (Fin 2) L[X])
    (Q : Matrix (Fin 4) (Fin 4) K) :
    fourOutputPluckerVector (Q.map (C.comp (algebraMap K L))*G) 1=
      fourOutputConstantMinor G (Q 0) (Q 2) := by
  simp [fourOutputPluckerVector,fourOutputPluckerRows,pluckerMinorVector,
    Matrix.det_fin_two,Matrix.mul_apply,fourOutputConstantMinor,fourOutputConstantRow]

/-- The coprime chart is realized by a base-field matrix and its two-sided inverse. -/
theorem exists_four_output_coprime_chart [Infinite K]
    (G : Matrix (Fin 4) (Fin 2) L[X])
    (R : Matrix (Fin 2) (Fin 4) L[X]) (hRG : R*G=1)
    (d : ℕ) (hG : ∀ i j, (G i j).natDegree≤d)
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (G i j).coeff d))) :
    ∃ Q S : Matrix (Fin 4) (Fin 4) K, Q*S=1 ∧ S*Q=1 ∧
      (fourOutputPluckerVector (Q.map (C.comp (algebraMap K L))*G) 0).natDegree=2*d ∧
      IsCoprime (fourOutputPluckerVector (Q.map (C.comp (algebraMap K L))*G) 0)
        (fourOutputPluckerVector (Q.map (C.comp (algebraMap K L))*G) 1) := by
  obtain ⟨Q,hQ,hd,hcop⟩ := exists_four_output_coprime_chart_rows (K:=K) G R hRG d hG hlead
  obtain ⟨U,rfl⟩ := hQ
  refine ⟨↑U,U.inv,U.val_inv,U.inv_val,?_,?_⟩
  · simpa only [base_change_first_minor] using hd
  · simpa only [base_change_first_minor,base_change_second_minor] using hcop

/-- The same chart written as the linear exterior action on the six coordinates. -/
theorem exists_four_output_coprime_chart_action [Infinite K]
    (G : Matrix (Fin 4) (Fin 2) L[X])
    (R : Matrix (Fin 2) (Fin 4) L[X]) (hRG : R*G=1)
    (d : ℕ) (hG : ∀ i j, (G i j).natDegree≤d)
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (G i j).coeff d))) :
    ∃ Q S : Matrix (Fin 4) (Fin 4) K, Q*S=1 ∧ S*Q=1 ∧
      (pluckerOutputChange (Q.map (C.comp (algebraMap K L))) (fourOutputPluckerVector G) 0).natDegree=2*d ∧
      IsCoprime (pluckerOutputChange (Q.map (C.comp (algebraMap K L))) (fourOutputPluckerVector G) 0)
        (pluckerOutputChange (Q.map (C.comp (algebraMap K L))) (fourOutputPluckerVector G) 1) := by
  simpa only [fourOutputPluckerVector_mul] using
    exists_four_output_coprime_chart (K:=K) G R hRG d hG hlead

end FD56
