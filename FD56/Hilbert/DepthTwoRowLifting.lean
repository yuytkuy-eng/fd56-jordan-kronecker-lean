/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BetaKernel
import FD56.Hilbert.ColumnSurjectivity

/-! Bounded annihilators of a minimal stack with row degrees one and two. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K l m n r : Type*} [Field K]
  [Fintype m] [Fintype n] [Fintype r] [DecidableEq m] [DecidableEq n]

def depthTwoStack (P Q : Matrix m n K[X]) : Matrix (m ⊕ m) n K[X] :=
  Sum.elim P Q

def depthTwoRowDegree : m ⊕ m → ℕ := Sum.elim (fun _ => 1) (fun _ => 2)

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
theorem depthTwo_stack_degree (P Q : Matrix m n K[X])
    (hP : DegreeBound P 1) (hQ : DegreeBound Q 2) :
    ∀ i j, (depthTwoStack P Q i j).natDegree ≤ depthTwoRowDegree i := by
  intro i j
  cases i with
  | inl i => exact hP i j
  | inr i => exact hQ i j

theorem depthTwo_stack_factor (P Q : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P Q))))
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P Q * R = 1)
    (hP : DegreeBound P 1) (hQ : DegreeBound Q 2)
    (hlead : Function.Injective (Matrix.mulVec (fun x i =>
      (depthTwoStack P Q i x).coeff (depthTwoRowDegree i))))
    (S : Matrix l n K[X]) (d : ℕ) (hS : DegreeBound S d)
    (hSV : S * polynomialKernelBasisMatrix (depthTwoStack P Q) B = 0) :
    S = (S * R) * depthTwoStack P Q ∧
      ∀ i j, (S * R) i j = 0 ∨
        (depthTwoRowDegree j ≤ d ∧ ((S * R) i j).natDegree ≤ d - depthTwoRowDegree j) := by
  have he := row_factor_through_of_kernel_basis (depthTwoStack P Q) B R hR S hSV
  refine ⟨he, ?_⟩
  apply row_coordinates_degree_bound (depthTwoStack P Q) (S * R)
    depthTwoRowDegree (fun _ => d) (depthTwo_stack_degree P Q hP hQ) hlead
  simpa only [← he] using hS

theorem depthTwo_affine_annihilator (P Q : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P Q))))
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P Q * R = 1)
    (hP : DegreeBound P 1) (hQ : DegreeBound Q 2)
    (hlead : Function.Injective (Matrix.mulVec (fun x i =>
      (depthTwoStack P Q i x).coeff (depthTwoRowDegree i))))
    (S : Matrix l n K[X]) (hS : DegreeBound S 1)
    (hSV : S * polynomialKernelBasisMatrix (depthTwoStack P Q) B = 0) :
    S = (show Matrix l m K[X] from fun i j => C (((S * R) i (Sum.inl j)).coeff 0)) * P := by
  obtain ⟨he, hd⟩ := depthTwo_stack_factor P Q B R hR hP hQ hlead S 1 hS hSV
  have hlow (i : l) (j : m) : (S * R) i (Sum.inl j) =
      C (((S * R) i (Sum.inl j)).coeff 0) := by
    apply Polynomial.eq_C_of_natDegree_le_zero
    rcases hd i (Sum.inl j) with h | ⟨_, h⟩
    · simp [h]
    · exact h
  have hhigh (i : l) (j : m) : (S * R) i (Sum.inr j) = 0 := by
    rcases hd i (Sum.inr j) with h | ⟨h, _⟩
    · exact h
    · change 2 ≤ 1 at h
      omega
  calc
    S = (S * R) * depthTwoStack P Q := he
    _ = _ := by
      funext i j
      rw [Matrix.mul_apply, Fintype.sum_sum_type]
      simp only [depthTwoStack, Sum.elim_inl, Sum.elim_inr, hhigh,
        zero_mul, Finset.sum_const_zero, add_zero]
      change (∑ k, (S * R) i (Sum.inl k) * P k j) =
        ∑ k, C (((S * R) i (Sum.inl k)).coeff 0) * P k j
      exact Finset.sum_congr rfl (fun k _ => congrArg (fun z => z * P k j) (hlow i k))

theorem depthTwo_quadratic_annihilator (P Q : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P Q))))
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P Q * R = 1)
    (hP : DegreeBound P 1) (hQ : DegreeBound Q 2)
    (hlead : Function.Injective (Matrix.mulVec (fun x i =>
      (depthTwoStack P Q i x).coeff (depthTwoRowDegree i))))
    (S : Matrix l n K[X]) (hS : DegreeBound S 2)
    (hSV : S * polynomialKernelBasisMatrix (depthTwoStack P Q) B = 0) :
    ∃ A : Matrix l m K[X], ∃ D : Matrix l m K,
      DegreeBound A 1 ∧ S = A * P + D.map C * Q := by
  obtain ⟨he, hd⟩ := depthTwo_stack_factor P Q B R hR hP hQ hlead S 2 hS hSV
  let A : Matrix l m K[X] := fun i j => (S * R) i (Sum.inl j)
  let D : Matrix l m K := fun i j => ((S * R) i (Sum.inr j)).coeff 0
  have hhigh (i : l) (j : m) : (S * R) i (Sum.inr j) = C (D i j) := by
    apply Polynomial.eq_C_of_natDegree_le_zero
    rcases hd i (Sum.inr j) with h | ⟨_, h⟩
    · simp [h]
    · exact h
  refine ⟨A, D, ?_, ?_⟩
  · intro i j
    rcases hd i (Sum.inl j) with h | ⟨_, h⟩
    · simp [A, h]
    · exact h
  · calc
      S = (S * R) * depthTwoStack P Q := he
      _ = _ := by
        funext i j
        rw [Matrix.mul_apply, Fintype.sum_sum_type]
        simp only [depthTwoStack, Sum.elim_inl, Sum.elim_inr, hhigh]
        rfl

theorem depthTwo_affine_action_factor (P Q : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P Q))))
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P Q * R = 1)
    (hP : DegreeBound P 1) (hQ : DegreeBound Q 2)
    (hlead : Function.Injective (Matrix.mulVec (fun x i =>
      (depthTwoStack P Q i x).coeff (depthTwoRowDegree i))))
    (M : Matrix n n K[X]) (hM : DegreeBound M 1)
    (hMV : P * M * polynomialKernelBasisMatrix (depthTwoStack P Q) B = 0) :
    ∃ A : Matrix m m K[X], ∃ D : Matrix m m K,
      DegreeBound A 1 ∧ P * M = A * P + D.map C * Q :=
  depthTwo_quadratic_annihilator P Q B R hR hP hQ hlead (P * M)
    (degreeBound_mul hP hM) hMV

end FD56
