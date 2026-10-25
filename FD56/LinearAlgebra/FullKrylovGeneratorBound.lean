/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.KernelCoordinateReconstruction
import FD56.LinearAlgebra.FiniteFieldGenerators

/-! Field generators on a normalized full-rank Krylov coordinate chart. -/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators

universe u v w w'

/-- The columns are the successive images of a vector under a matrix. -/
def krylovMatrix {F n : Type*} [Semiring F] [Fintype n] [DecidableEq n]
    (M : Matrix n n F) (v : n → F) (q : ℕ) : Matrix n (Fin q) F :=
  fun i j => (M ^ j.val *ᵥ v) i

/-- Entries of the two original matrices, with repetitions retained. -/
def matrixEntryGenerators {F n m : Type*} (M : Matrix n n F) (P : Matrix m n F) :
    (n × n) ⊕ (m × n) → F :=
  Sum.elim (fun ij => M ij.1 ij.2) (fun ij => P ij.1 ij.2)

/-- The chart keeps all matrix entries, one normalized vector, and the free kernel columns. -/
abbrev FullKrylovChartIndex (t m : Type*) (q : ℕ) (c : Fin q ⊕ t) :=
  ((Fin q ⊕ t) × (Fin q ⊕ t)) ⊕ ({i : Fin q ⊕ t // i ≠ c} ⊕ (m × t))

/-- Coordinates retained on the chart. -/
def fullKrylovChartGenerators {F t m : Type*} {q : ℕ}
    (M : Matrix (Fin q ⊕ t) (Fin q ⊕ t) F) (P : Matrix m (Fin q ⊕ t) F)
    (v : (Fin q ⊕ t) → F) (c : Fin q ⊕ t) :
    FullKrylovChartIndex t m q c → F :=
  Sum.elim (fun ij => M ij.1 ij.2)
    (Sum.elim (fun i => v i.val) (fun ij => P ij.1 (Sum.inr ij.2)))

theorem matrix_power_mulVec_mem_subfield {F n : Type*} [Field F]
    [Fintype n] [DecidableEq n] (S : Subfield F) (M : Matrix n n F) (v : n → F)
    (hM : ∀ i j, M i j ∈ S) (hv : ∀ i, v i ∈ S) (k : ℕ) :
    ∀ i, (M ^ k *ᵥ v) i ∈ S := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    intro i
    exact S.sum_mem (fun j _ => S.mul_mem (hM i j) (ih j))

/-- A nonsingular pivot reconstructs every eliminated entry of `P` in the reduced field. -/
theorem fullKrylovChartGenerators_adjoin_eq_top
    {K : Type u} {F : Type v} {t : Type w} {m : Type w'}
    [Field K] [Field F] [Algebra K F] [Fintype t] [DecidableEq t]
    {q : ℕ} (M : Matrix (Fin q ⊕ t) (Fin q ⊕ t) F)
    (P : Matrix m (Fin q ⊕ t) F) (v : (Fin q ⊕ t) → F) (c : Fin q ⊕ t)
    (U : Matrix (Fin q) (Fin q) F) (hv : v c = 1)
    (hker : ∀ j : Fin q, P *ᵥ (M ^ j.val *ᵥ v) = 0)
    (hU : (krylovMatrix M v q).submatrix Sum.inl id * U = 1)
    (hgen : IntermediateField.adjoin K (Set.range (matrixEntryGenerators M P)) = ⊤) :
    IntermediateField.adjoin K (Set.range (fullKrylovChartGenerators M P v c)) = ⊤ := by
  classical
  let S := IntermediateField.adjoin K (Set.range (fullKrylovChartGenerators M P v c))
  have hM : ∀ i j, M i j ∈ S := by
    intro i j
    exact IntermediateField.subset_adjoin K _ ⟨Sum.inl (i, j), rfl⟩
  have hvS : ∀ i, v i ∈ S := by
    intro i
    by_cases hi : i = c
    · simpa only [hi, hv] using S.one_mem
    · exact IntermediateField.subset_adjoin K _ ⟨Sum.inr (Sum.inl ⟨i, hi⟩), rfl⟩
  have hA : ∀ i j, krylovMatrix M v q i j ∈ S := by
    intro i j
    exact matrix_power_mulVec_mem_subfield S.toSubfield M v hM hvS j.val i
  have hPR : ∀ i j, P i (Sum.inr j) ∈ S := by
    intro i j
    exact IntermediateField.subset_adjoin K _ ⟨Sum.inr (Sum.inr (i, j)), rfl⟩
  have hPA : P * krylovMatrix M v q = 0 := by
    ext i j
    exact congrFun (hker j) i
  have hP : ∀ i j, P i j ∈ S :=
    kernel_coordinates_mem_subfield S.toSubfield _ P U hPA hU hA hPR
  have hle : IntermediateField.adjoin K (Set.range (matrixEntryGenerators M P)) ≤ S := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨ij, rfl⟩
    cases ij with
    | inl ij => exact hM ij.1 ij.2
    | inr ij => exact hP ij.1 ij.2
  exact top_unique (hgen ▸ hle)

theorem fullKrylovChartIndex_card {t m : Type*} [Fintype t] [DecidableEq t]
    [Fintype m] (q : ℕ) (c : Fin q ⊕ t) :
    Fintype.card (FullKrylovChartIndex t m q c) =
      Fintype.card (Fin q ⊕ t) ^ 2 + (Fintype.card (Fin q ⊕ t) - 1) +
        Fintype.card m * (Fintype.card (Fin q ⊕ t) - q) := by
  simp [FullKrylovChartIndex, Fintype.card_subtype_compl, pow_two, Nat.add_assoc]

/-- The full-rank chart gives the expected `n² + (n - 1) + m(n - q)` bound. -/
theorem trdeg_le_fullKrylovChart_bound
    {K : Type u} {F : Type v} {t : Type w} {m : Type w'}
    [Field K] [Field F] [Algebra K F] [Fintype t] [DecidableEq t] [Fintype m]
    {q : ℕ} (M : Matrix (Fin q ⊕ t) (Fin q ⊕ t) F)
    (P : Matrix m (Fin q ⊕ t) F) (v : (Fin q ⊕ t) → F) (c : Fin q ⊕ t)
    (U : Matrix (Fin q) (Fin q) F) (hv : v c = 1)
    (hker : ∀ j : Fin q, P *ᵥ (M ^ j.val *ᵥ v) = 0)
    (hU : (krylovMatrix M v q).submatrix Sum.inl id * U = 1)
    (hgen : IntermediateField.adjoin K (Set.range (matrixEntryGenerators M P)) = ⊤) :
    Algebra.trdeg K F ≤
      ((Fintype.card (Fin q ⊕ t) ^ 2 + (Fintype.card (Fin q ⊕ t) - 1) +
        Fintype.card m * (Fintype.card (Fin q ⊕ t) - q) : ℕ) : Cardinal.{v}) := by
  rw [← fullKrylovChartIndex_card q c]
  exact trdeg_le_card_of_finite_field_generators (fullKrylovChartGenerators M P v c)
    (fullKrylovChartGenerators_adjoin_eq_top M P v c U hv hker hU hgen)

/-- A finite algebraically independent family is bounded by the same chart count. -/
theorem card_algebraicIndependent_le_fullKrylovChart_bound
    {K : Type u} {F : Type v} {t : Type w} {m : Type w'} {κ : Type*}
    [Field K] [Field F] [Algebra K F] [Fintype t] [DecidableEq t] [Fintype m]
    [Fintype κ] {x : κ → F} (hx : AlgebraicIndependent K x)
    {q : ℕ} (M : Matrix (Fin q ⊕ t) (Fin q ⊕ t) F)
    (P : Matrix m (Fin q ⊕ t) F) (v : (Fin q ⊕ t) → F) (c : Fin q ⊕ t)
    (U : Matrix (Fin q) (Fin q) F) (hv : v c = 1)
    (hker : ∀ j : Fin q, P *ᵥ (M ^ j.val *ᵥ v) = 0)
    (hU : (krylovMatrix M v q).submatrix Sum.inl id * U = 1)
    (hgen : IntermediateField.adjoin K (Set.range (matrixEntryGenerators M P)) = ⊤) :
    Fintype.card κ ≤ Fintype.card (Fin q ⊕ t) ^ 2 +
      (Fintype.card (Fin q ⊕ t) - 1) +
        Fintype.card m * (Fintype.card (Fin q ⊕ t) - q) := by
  rw [← fullKrylovChartIndex_card q c]
  exact card_le_card_of_algebraicIndependent_of_finite_field_generators hx
    (fullKrylovChartGenerators M P v c)
    (fullKrylovChartGenerators_adjoin_eq_top M P v c U hv hker hU hgen)

end FD56
