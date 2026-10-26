/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ObservabilityScalarAdjugate

/-! Scalar-adjugate constructions commute with coefficient specialization. -/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators
variable {R S n m : Type*} [CommRing R] [CommRing S]
  [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

omit [Fintype n] [Fintype m] [DecidableEq n] in
theorem observabilityScalarColumn_map (φ : R →+* S) (N : Matrix n n R)
    (row : n → m) (k : n) :
    (observabilityScalarColumn N row k).map φ=observabilityScalarColumn (N.map φ) row k := by
  funext i a
  by_cases h : a=row k <;> simp [observabilityScalarColumn,Matrix.map_apply,h]

theorem matrixCommutatorSum_map (φ : R →+* S) (M D : Matrix n n R) (i : ℕ) :
    (matrixCommutatorSum M D i).map φ=matrixCommutatorSum (M.map φ) (D.map φ) i := by
  unfold matrixCommutatorSum
  change φ.mapMatrix (∑ s ∈ Finset.range i, M^s*D*M^(i-1-s)) = _
  simp only [map_sum,map_mul,map_pow]
  rfl

theorem observabilityScalarX_map (φ : R →+* S) (M : Matrix n n R) (P : Matrix m n R)
    (N : Matrix n n R) (level : n → ℕ) (row : n → m) :
    (observabilityScalarX M P N level row).map φ=
      observabilityScalarX (M.map φ) (P.map φ) (N.map φ) level row := by
  unfold observabilityScalarX
  change φ.mapMatrix (∑ k, matrixCommutatorSum M (observabilityScalarColumn N row k*P)
    (level k)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  change (matrixCommutatorSum M (observabilityScalarColumn N row k*P) (level k)).map φ = _
  rw [matrixCommutatorSum_map,Matrix.map_mul,observabilityScalarColumn_map]

omit [Fintype m] in
theorem observabilityScalarU_map (φ : R →+* S) (M N : Matrix n n R)
    (level : n → ℕ) (row : n → m) :
    (observabilityScalarU M N level row).map φ=
      observabilityScalarU (M.map φ) (N.map φ) level row := by
  funext i a
  simp only [observabilityScalarU,Matrix.map_apply,Matrix.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hp : (M^(level k)).map φ=(M.map φ)^(level k) := map_pow φ.mapMatrix M _
  have h : (M^(level k)*observabilityScalarColumn N row k).map φ =
      (M.map φ)^(level k)*observabilityScalarColumn (N.map φ) row k := by
    rw [Matrix.map_mul,hp,observabilityScalarColumn_map]
  exact congrFun (congrFun h i) a

omit [Fintype m] [DecidableEq m] in
theorem observabilitySelectedMatrix_map (φ : R →+* S) (M : Matrix n n R)
    (P : Matrix m n R) (level : n → ℕ) (row : n → m) :
    (observabilitySelectedMatrix M P level row).map φ=
      observabilitySelectedMatrix (M.map φ) (P.map φ) level row := by
  funext i j
  have hp : (M^(level i)).map φ=(M.map φ)^(level i) := map_pow φ.mapMatrix M _
  have h : (P*M^(level i)).map φ=P.map φ*(M.map φ)^(level i) := by
    rw [Matrix.map_mul,hp]
  exact congrFun (congrFun h (row i)) j

end FD56
