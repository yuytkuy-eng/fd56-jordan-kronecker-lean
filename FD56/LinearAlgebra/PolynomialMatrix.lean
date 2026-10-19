/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-! Polynomial matrices and finite dimensional degree truncations. -/

noncomputable section
open Matrix Polynomial
open scoped BigOperators

namespace FD56

variable {K : Type*} [Field K]
variable {l m n : Type*}

/-- Every entry has degree at most `d`; the zero polynomial is included. -/
def DegreeBound (A : Matrix m n K[X]) (d : ℕ) : Prop :=
  ∀ i j, (A i j).natDegree ≤ d

theorem degreeBound_mul [Fintype m] {A : Matrix l m K[X]} {B : Matrix m n K[X]}
    {a b : ℕ} (hA : DegreeBound A a) (hB : DegreeBound B b) :
    DegreeBound (A * B) (a + b) := by
  intro i j
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k _
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hA i k) (hB k j))

theorem degreeBound_sub {A B : Matrix m n K[X]} {d : ℕ}
    (hA : DegreeBound A d) (hB : DegreeBound B d) : DegreeBound (A - B) d := by
  intro i j
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le (hA i j) (hB i j))

abbrev BoundedPoly (K : Type*) [Field K] (d : ℕ) := Polynomial.degreeLT K (d + 1)

instance boundedPolyFinite (d : ℕ) : Module.Finite K (BoundedPoly K d) :=
  Module.Finite.of_injective (Polynomial.degreeLTEquiv K (d + 1)).toLinearMap
    (Polynomial.degreeLTEquiv K (d + 1)).injective

@[simp] theorem boundedPoly_finrank (d : ℕ) :
    Module.finrank K (BoundedPoly K d) = d + 1 := by
  rw [(Polynomial.degreeLTEquiv K (d + 1)).finrank_eq]
  simp

theorem boundedPoly_degree (d : ℕ) (p : BoundedPoly K d) :
    (p.val : K[X]).natDegree ≤ d := by
  have h := p.property
  change p.val ∈ Polynomial.degreeLT K (d + 1) at h
  rwa [Polynomial.degreeLT_succ_eq_degreeLE, Polynomial.mem_degreeLE,
    ← Polynomial.natDegree_le_iff_degree_le] at h

def boundedPolyOf {d : ℕ} (p : K[X]) (hp : p.natDegree ≤ d) : BoundedPoly K d :=
  ⟨p, by change p ∈ Polynomial.degreeLT K (d + 1)
         rwa [Polynomial.degreeLT_succ_eq_degreeLE, Polynomial.mem_degreeLE,
    ← Polynomial.natDegree_le_iff_degree_le]⟩

abbrev BoundedMatrix (K : Type*) [Field K] (m n : Type*) (d : ℕ) :=
  Matrix m n (BoundedPoly K d)

def entries {d : ℕ} (A : BoundedMatrix K m n d) : Matrix m n K[X] :=
  fun i j => (A i j).val

@[simp] theorem entries_zero (d : ℕ) :
    entries (0 : BoundedMatrix K m n d) = 0 := rfl

@[simp] theorem entries_add {d : ℕ} (A B : BoundedMatrix K m n d) :
    entries (A + B) = entries A + entries B := rfl

@[simp] theorem entries_smul {d : ℕ} (c : K) (A : BoundedMatrix K m n d) :
    entries (c • A) = c • entries A := rfl

theorem entries_injective (d : ℕ) :
    Function.Injective (entries : BoundedMatrix K m n d → Matrix m n K[X]) := by
  intro A B h
  funext i j
  apply Subtype.ext
  exact congrFun (congrFun h i) j

theorem entries_degree {d : ℕ} (A : BoundedMatrix K m n d) :
    DegreeBound (entries A) d := by
  intro i j
  exact boundedPoly_degree d (A i j)

@[simp] theorem boundedMatrix_finrank [Fintype m] [Fintype n] (d : ℕ) :
    Module.finrank K (BoundedMatrix K m n d) =
      Fintype.card m * Fintype.card n * (d + 1) := by
  simp [BoundedMatrix, Matrix, Module.finrank_pi_fintype, mul_assoc]

/-- Rank-nullity in the form needed by both coefficient counts. -/
theorem exists_nonzero_kernel {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [Module.Finite K W] (f : V →ₗ[K] W)
    (hdim : Module.finrank K W < Module.finrank K V) :
    ∃ v : V, v ≠ 0 ∧ f v = 0 := by
  by_contra h
  push_neg at h
  have hinj : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    by_contra hv0
    exact h v hv0 hv
  exact (not_le_of_gt hdim) (LinearMap.finrank_le_finrank_of_injective hinj)

end FD56
