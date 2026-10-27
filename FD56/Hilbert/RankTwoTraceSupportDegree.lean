/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.RankTwoTraceKernel
import FD56.Hilbert.PolynomialHyperplaneChart
import FD56.Hilbert.MinimalProfile

/-! A maximal singleton minimal index forces the trace to meet every Jordan primary block. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K ι r : Type*} [Field K] [Fintype ι] [DecidableEq ι]
  [Fintype r] [DecidableEq r]

theorem singleton_minimal_degree_le_of_kernel {a b : Type*} [Fintype b] [DecidableEq b]
    (H : Matrix a b K[X]) (e d : ℕ) (hm : HasMinimalKernelDegrees H [e])
    (v : b → K[X]) (hv : H *ᵥ v=0) (hn : v≠0)
    (hd : ∀ i, (v i).natDegree≤d) : e≤d := by
  let z : polynomialKernelAtDegree H d := ⟨fun i => boundedPolyOf (v i) (hd i),hv⟩
  have hz : z≠0 := by
    intro h
    apply hn
    exact congrArg (fun w : polynomialKernelAtDegree H d => fun i => (w.val i).val) h
  have hp : 0<Module.finrank K (polynomialKernelAtDegree H d) :=
    (Module.finrank_pos_iff_exists_ne_zero (R := K) (M := polynomialKernelAtDegree H d)).mpr ⟨z,hz⟩
  rw [(hasMinimalKernelDegrees_iff_hilbert _ _).mp hm] at hp
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] at hp
  omega

def rankTwoTraceSumCovector (a b : ι → K) (k : ℕ) : (Σ _ : ι, rankTwoJordanIndex k) → K :=
  fun i => rankTwoTraceCovector (a i.1) (b i.1) k i.2

theorem rankTwo_trace_support_degree_bound (lam a b : ι → K) (k e : ℕ)
    (E : Matrix (Σ _ : ι, rankTwoJordanIndex k) r K)
    (F : Matrix r (Σ _ : ι, rankTwoJordanIndex k) K)
    (hE : E.transpose *ᵥ rankTwoTraceSumCovector a b k=0)
    (hEF : ∀ v, rankTwoTraceSumCovector a b k ⬝ᵥ v=0 → E *ᵥ (F *ᵥ v)=v)
    (hm : HasMinimalKernelDegrees ((E.map C).transpose*
      Matrix.blockDiagonal' (fun i => rankTwoJordanPencil (lam i) k)*E.map C) [e])
    (s : Finset ι) (hs : ∀ i, i∉s → a i=0 ∧ b i=0)
    (hn : ∃ i∈s, a i≠0 ∨ b i≠0) : e≤s.card-1 := by
  let c := rankTwoTraceSumCovector a b k
  let v : (Σ _ : ι, rankTwoJordanIndex k) → K[X] :=
    fun i => rankTwoTraceSolution (a i.1) (b i.1) (partialPoleCofactor lam s i.1) k i.2
  have hc : (fun i => C (c i)) ⬝ᵥ v=0 := by
    change (∑ i : Σ _ : ι, rankTwoJordanIndex k,
      C (rankTwoTraceCovector (a i.1) (b i.1) k i.2)*v i)=0
    rw [Fintype.sum_sigma]
    apply Finset.sum_eq_zero
    intro i _
    exact rankTwoTraceSolution_trace (a i) (b i) (partialPoleCofactor lam s i) k
  have hv : v≠0 := by
    obtain ⟨i,hi,hab⟩ := hn
    intro hzero
    apply rankTwoTraceSolution_ne_zero (a i) (b i) (partialPoleCofactor lam s i) k hab
      (partialPoleCofactor_ne_zero lam s i hi)
    exact funext (fun j => congrFun hzero ⟨i,j⟩)
  have hrec := polynomial_hyperplane_chart_recovery E F c hEF v hc
  have hw : F.map C *ᵥ v≠0 := by
    intro hz
    apply hv
    rw [hz,Matrix.mulVec_zero] at hrec
    exact hrec.symm
  apply singleton_minimal_degree_le_of_kernel _ e (s.card-1) hm (F.map C *ᵥ v)
  · exact polynomial_hyperplane_chart_kernel _ E F c hE hEF v _ hc
      (partialPole_trace_solution_identity lam a b s k hs)
  · exact hw
  · exact constant_mulVec_degree F v (s.card-1) (fun i =>
      rankTwoTraceSolution_degree _ _ _ _ _ (partialPoleCofactor_degree lam s i.1) i.2)

theorem rankTwo_trace_full_support_of_maximal_index (lam a b : ι → K) (k : ℕ)
    (E : Matrix (Σ _ : ι, rankTwoJordanIndex k) r K)
    (F : Matrix r (Σ _ : ι, rankTwoJordanIndex k) K)
    (hE : E.transpose *ᵥ rankTwoTraceSumCovector a b k=0)
    (hEF : ∀ v, rankTwoTraceSumCovector a b k ⬝ᵥ v=0 → E *ᵥ (F *ᵥ v)=v)
    (hm : HasMinimalKernelDegrees ((E.map C).transpose*
      Matrix.blockDiagonal' (fun i => rankTwoJordanPencil (lam i) k)*E.map C)
      [Fintype.card ι-1])
    (hn : ∃ i, a i≠0 ∨ b i≠0) : ∀ i, a i≠0 ∨ b i≠0 := by
  classical
  let s : Finset ι := Finset.univ.filter (fun i => a i≠0 ∨ b i≠0)
  have hs : ∀ i, i∉s → a i=0 ∧ b i=0 := by
    intro i hi
    simpa only [s,Finset.mem_filter,Finset.mem_univ,true_and,not_or,not_not] using hi
  have hns : ∃ i∈s, a i≠0 ∨ b i≠0 := by
    obtain ⟨i,hi⟩ := hn
    exact ⟨i,by simp [s,hi],hi⟩
  have hb := rankTwo_trace_support_degree_bound lam a b k (Fintype.card ι-1) E F hE hEF hm s hs hns
  have hp : 0<s.card := Finset.card_pos.mpr (by obtain ⟨i,hi,_⟩ := hns; exact ⟨i,hi⟩)
  have hle : s.card≤Fintype.card ι := Finset.card_le_univ s
  have hcard : s.card=Fintype.card ι := by omega
  have heq : s=Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ s) (by simp [hcard])
  intro i
  have hi : i∈s := heq ▸ Finset.mem_univ i
  simpa [s] using hi

end FD56
