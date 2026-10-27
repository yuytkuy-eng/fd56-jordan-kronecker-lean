/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.NilpotentRankTwoJordan
import FD56.Hilbert.RectangularBlocks

/-! Polynomial vectors for a trace hyperplane in a sum of rank-two Jordan pencils. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

def partialPoleCofactor (lam : ι → K) (s : Finset ι) (i : ι) : K[X] :=
  if i∈s then ∏ j ∈ s.erase i, (X-C (lam j)) else 0

omit [Fintype ι] in
theorem partialPoleCofactor_identity (lam : ι → K) (s : Finset ι) (i : ι) :
    (X-C (lam i))*partialPoleCofactor lam s i=
      if i∈s then ∏ j∈s, (X-C (lam j)) else 0 := by
  by_cases hi : i∈s
  · simp only [partialPoleCofactor,hi,if_true]
    exact Finset.mul_prod_erase s (fun j => X-C (lam j)) hi
  · simp [partialPoleCofactor,hi]

omit [Fintype ι] in
theorem partialPoleCofactor_degree (lam : ι → K) (s : Finset ι) (i : ι) :
    (partialPoleCofactor lam s i).natDegree≤s.card-1 := by
  by_cases hi : i∈s
  · simp only [partialPoleCofactor,hi,if_true]
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C (lam j))]
    simp [hi,Finset.card_erase_of_mem]
  · simp [partialPoleCofactor,hi]

omit [Fintype ι] in
theorem partialPoleCofactor_ne_zero (lam : ι → K) (s : Finset ι) (i : ι) (hi : i∈s) :
    partialPoleCofactor lam s i≠0 := by
  simp only [partialPoleCofactor,hi,if_true]
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => Polynomial.X_sub_C_ne_zero _)

def rankTwoTraceCovector (a b : K) (k : ℕ) : rankTwoJordanIndex k → K :=
  Sum.elim (Sum.elim ![a,0] ![0,b]) (fun _ => 0)

def rankTwoTraceSolution (a b : K) (p : K[X]) (k : ℕ) : rankTwoJordanIndex k → K[X] :=
  Sum.elim (Sum.elim ![0,-C b*p] ![C a*p,0]) (fun _ => 0)

theorem rankTwoTraceSolution_identity (lam a b : K) (p : K[X]) (k : ℕ) :
    rankTwoJordanPencil lam k *ᵥ rankTwoTraceSolution a b p k=
      fun i => (X-C lam)*p*C (rankTwoTraceCovector a b k i) := by
  funext i
  rcases i with (i|i)|i
  · fin_cases i <;>
      simp [rankTwoJordanPencil,skewJordanBlockPencil,jordanUpperPencil,
        rankTwoTraceSolution,rankTwoTraceCovector,Matrix.mulVec,dotProduct,
        Fintype.sum_sum_type,Fin.sum_univ_succ] <;> ring
  · fin_cases i <;>
      simp [rankTwoJordanPencil,skewJordanBlockPencil,jordanUpperPencil,
        rankTwoTraceSolution,rankTwoTraceCovector,Matrix.mulVec,dotProduct,
        Fintype.sum_sum_type,Fin.sum_univ_succ] <;> ring
  · simp [rankTwoJordanPencil,rankTwoTraceSolution,rankTwoTraceCovector,
      Matrix.mulVec,dotProduct,Fintype.sum_sum_type]

theorem rankTwoTraceSolution_trace (a b : K) (p : K[X]) (k : ℕ) :
    (fun i => C (rankTwoTraceCovector a b k i)) ⬝ᵥ rankTwoTraceSolution a b p k=0 := by
  simp [rankTwoTraceCovector,rankTwoTraceSolution,dotProduct,
    Fintype.sum_sum_type,Fin.sum_univ_succ]

theorem rankTwoTraceSolution_degree (a b : K) (p : K[X]) (k d : ℕ)
    (hp : p.natDegree≤d) (i : rankTwoJordanIndex k) :
    (rankTwoTraceSolution a b p k i).natDegree≤d := by
  rcases i with (i|i)|i
  · fin_cases i
    · simp [rankTwoTraceSolution]
    · simpa [rankTwoTraceSolution] using (Polynomial.natDegree_mul_le (p := -C b) (q := p)).trans
        (by simpa using hp)
  · fin_cases i
    · simpa [rankTwoTraceSolution] using (Polynomial.natDegree_mul_le (p := C a) (q := p)).trans
        (by simpa using hp)
    · simp [rankTwoTraceSolution]
  · simp [rankTwoTraceSolution]

theorem rankTwoTraceSolution_ne_zero (a b : K) (p : K[X]) (k : ℕ)
    (hab : a≠0 ∨ b≠0) (hp : p≠0) : rankTwoTraceSolution a b p k≠0 := by
  intro hz
  rcases hab with ha | hb
  · have he := congrFun hz (.inl (.inr 0))
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr ha) hp he
  · have he := congrFun hz (.inl (.inl 1))
    exact mul_ne_zero (neg_ne_zero.mpr (Polynomial.C_ne_zero.mpr hb)) hp he

theorem partialPole_trace_solution_identity (lam a b : ι → K) (s : Finset ι) (k : ℕ)
    (hs : ∀ i, i∉s → a i=0 ∧ b i=0) :
    Matrix.blockDiagonal' (fun i => rankTwoJordanPencil (lam i) k) *ᵥ
        (fun i : Σ _ : ι, rankTwoJordanIndex k =>
          rankTwoTraceSolution (a i.1) (b i.1) (partialPoleCofactor lam s i.1) k i.2)=
      fun i => (∏ j∈s, (X-C (lam j)))*C (rankTwoTraceCovector (a i.1) (b i.1) k i.2) := by
  funext ⟨i,j⟩
  rw [blockDiagonal_mulVec]
  dsimp only
  rw [rankTwoTraceSolution_identity]
  dsimp only
  rw [partialPoleCofactor_identity]
  by_cases hi : i∈s
  · simp [hi]
  · obtain ⟨ha,hb⟩ := hs i hi
    simp only [hi,if_false,zero_mul,ha,hb]
    rcases j with (j|j)|j
    · fin_cases j <;> simp [rankTwoTraceCovector]
    · fin_cases j <;> simp [rankTwoTraceCovector]
    · simp [rankTwoTraceCovector]

end FD56
