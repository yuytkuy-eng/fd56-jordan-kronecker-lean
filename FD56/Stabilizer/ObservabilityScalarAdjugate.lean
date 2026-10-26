/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ScalarObservability
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! Explicit scalar-commutator solutions from square observability minors. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {R n m : Type*} [CommRing R] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

def observabilityScalarColumn (N : Matrix n n R) (row : n → m) (k : n) : Matrix n m R :=
  fun i a => if a=row k then N i k else 0

omit [Fintype n] [DecidableEq n] in
theorem observabilityScalarColumn_mul (N : Matrix n n R) (row : n → m) (k : n)
    (P : Matrix m n R) :
    observabilityScalarColumn N row k*P=fun i j => N i k*P (row k) j := by
  funext i j
  simp [Matrix.mul_apply,observabilityScalarColumn,ite_mul]

omit [Fintype m] [DecidableEq n] in
theorem mul_observabilityScalarColumn (A : Matrix m n R) (N : Matrix n n R)
    (row : n → m) (k : n) :
    A*observabilityScalarColumn N row k=fun i a => if a=row k then (A*N) i k else 0 := by
  funext i a
  by_cases h : a=row k <;> simp [Matrix.mul_apply,observabilityScalarColumn,h]

def matrixCommutatorSum (M D : Matrix n n R) (i : ℕ) : Matrix n n R :=
  ∑ s ∈ Finset.range i, M^s*D*M^(i-1-s)

theorem matrixCommutatorSum_commutator (M D : Matrix n n R) (i : ℕ) :
    M*matrixCommutatorSum M D i-matrixCommutatorSum M D i*M=M^i*D-D*M^i := by
  let f : ℕ → Matrix n n R := fun s => M^s*D*M^(i-s)
  unfold matrixCommutatorSum
  rw [Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib]
  calc
    (∑ s ∈ Finset.range i, (M*(M^s*D*M^(i-1-s))-(M^s*D*M^(i-1-s))*M)) =
        (∑ s ∈ Finset.range i, (f (s+1)-f s)) := by
      apply Finset.sum_congr rfl
      intro s hs
      have hsi : s < i := Finset.mem_range.mp hs
      have h₁ : i-(s+1)=i-1-s := by omega
      have h₂ : i-s=(i-1-s)+1 := by omega
      dsimp [f]
      rw [h₁,h₂]
      rw [pow_succ' M s,pow_succ M (i-1-s)]
      simp only [Matrix.mul_assoc]
    _ = f i-f 0 := Finset.sum_range_sub f i
    _ = M^i*D-D*M^i := by simp [f]

def observabilityScalarX (M : Matrix n n R) (P : Matrix m n R)
    (N : Matrix n n R) (level : n → ℕ) (row : n → m) : Matrix n n R :=
  ∑ k, matrixCommutatorSum M (observabilityScalarColumn N row k*P) (level k)

def observabilityScalarU (M N : Matrix n n R) (level : n → ℕ) (row : n → m) :
    Matrix n m R := ∑ k, M^(level k)*observabilityScalarColumn N row k

theorem observabilityScalar_commutator (M : Matrix n n R) (P : Matrix m n R)
    (N : Matrix n n R) (level : n → ℕ) (row : n → m) :
    M*observabilityScalarX M P N level row-observabilityScalarX M P N level row*M =
      observabilityScalarU M N level row*P-
        N*(show Matrix n n R from fun k j => (P*M^(level k)) (row k) j) := by
  unfold observabilityScalarX observabilityScalarU
  rw [Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib]
  simp_rw [matrixCommutatorSum_commutator]
  rw [Finset.sum_sub_distrib,Matrix.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.mul_assoc]
  · funext i j
    simp only [Matrix.sum_apply,Matrix.mul_assoc,observabilityScalarColumn_mul,
      Matrix.mul_apply,Finset.mul_sum,mul_assoc]

theorem observabilityScalarX_output_zero (M : Matrix n n R) (P : Matrix m n R)
    (N : Matrix n n R) (level : n → ℕ) (row : n → m)
    (hLower : ∀ k s, s<level k → ∀ a, (P*M^s*N) a k=0) :
    P*observabilityScalarX M P N level row=0 := by
  unfold observabilityScalarX
  rw [Matrix.mul_sum]
  apply Finset.sum_eq_zero
  intro k _
  unfold matrixCommutatorSum
  rw [Matrix.mul_sum]
  apply Finset.sum_eq_zero
  intro s hs
  have he : P*M^s*observabilityScalarColumn N row k=0 := by
    rw [mul_observabilityScalarColumn]
    funext a b
    simp [hLower k s (Finset.mem_range.mp hs) a]
  calc
    P*(M^s*(observabilityScalarColumn N row k*P)*M^(level k-1-s)) =
        (P*M^s*observabilityScalarColumn N row k)*P*M^(level k-1-s) := by
      simp only [Matrix.mul_assoc]
    _ = 0 := by rw [he,Matrix.zero_mul,Matrix.zero_mul]

theorem observabilityScalarX_trace_zero (M : Matrix n n R) (P : Matrix m n R)
    (N : Matrix n n R) (level : n → ℕ) (row : n → m)
    (hLower : ∀ k s, s<level k → ∀ a, (P*M^s*N) a k=0) :
    Matrix.trace (observabilityScalarX M P N level row)=0 := by
  unfold observabilityScalarX
  rw [Matrix.trace_sum]
  apply Finset.sum_eq_zero
  intro k _
  unfold matrixCommutatorSum
  rw [Matrix.trace_sum]
  apply Finset.sum_eq_zero
  intro s hs
  have hsi : s < level k := Finset.mem_range.mp hs
  have he : P*M^(level k-1-s+s)*observabilityScalarColumn N row k=0 := by
    rw [mul_observabilityScalarColumn]
    funext a b
    simp [hLower k (level k-1-s+s) (by omega) a]
  calc
    Matrix.trace (M^s*(observabilityScalarColumn N row k*P)*M^(level k-1-s)) =
        Matrix.trace ((M^s*observabilityScalarColumn N row k)*(P*M^(level k-1-s))) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((P*M^(level k-1-s))*(M^s*observabilityScalarColumn N row k)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace (P*M^(level k-1-s+s)*observabilityScalarColumn N row k) := by
      rw [pow_add]
      simp only [Matrix.mul_assoc]
    _ = 0 := by rw [he,Matrix.trace_zero]

def observabilitySelectedMatrix (M : Matrix n n R) (P : Matrix m n R)
    (level : n → ℕ) (row : n → m) : Matrix n n R :=
  fun k j => (P*M^(level k)) (row k) j

omit [Fintype m] [DecidableEq m] in
theorem observability_adjugate_lower_zero (M : Matrix n n R) (P : Matrix m n R)
    (level : n → ℕ) (row : n → m)
    (hLower : ∀ k s, s<level k → ∀ a, ∃ l, level l=s ∧ row l=a) :
    ∀ k s, s<level k → ∀ a,
      (P*M^s*(observabilitySelectedMatrix M P level row).adjugate) a k=0 := by
  intro k s hs a
  obtain ⟨l,hl,hr⟩ := hLower k s hs a
  have hne : l ≠ k := by intro he; subst l; omega
  let C := observabilitySelectedMatrix M P level row
  have he : (C*C.adjugate) l k=(P*M^s*C.adjugate) a k := by
    simp only [Matrix.mul_apply,C,observabilitySelectedMatrix,hl,hr]
  rw [← he,Matrix.mul_adjugate]
  simp [hne]

theorem observability_adjugate_scalar_equations (M : Matrix n n R) (P : Matrix m n R)
    (level : n → ℕ) (row : n → m)
    (hLower : ∀ k s, s<level k → ∀ a, ∃ l, level l=s ∧ row l=a) :
    let C := observabilitySelectedMatrix M P level row
    let X := observabilityScalarX M P C.adjugate level row
    let U := observabilityScalarU M C.adjugate level row
    P*X=0 ∧ Matrix.trace X=0 ∧ M*X-X*M=U*P+(-C.det)•1 := by
  dsimp only
  have hl := observability_adjugate_lower_zero M P level row hLower
  refine ⟨observabilityScalarX_output_zero M P _ level row hl,
    observabilityScalarX_trace_zero M P _ level row hl,?_⟩
  rw [observabilityScalar_commutator]
  change _ - (observabilitySelectedMatrix M P level row).adjugate*
    (observabilitySelectedMatrix M P level row) = _
  rw [Matrix.adjugate_mul]
  simp only [sub_eq_add_neg,neg_smul]

end FD56
