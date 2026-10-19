/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.Observability
import FD56.LinearAlgebra.RankSpecialization

/-! A polynomial matrix for the observability conditions, compatible with
specialization of its entries. -/

noncomputable section
namespace FD56
open Matrix

def observabilityMatrix {R n m : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (P : Matrix m n R) (q : ℕ) : Matrix (Fin q × m) n R :=
  fun ij k => (P * M ^ ij.1.val) ij.2 k

theorem observabilityMatrix_map {R S n m : Type*} [CommRing R] [CommRing S]
    [Fintype n] [DecidableEq n] (φ : R →+* S)
    (M : Matrix n n R) (P : Matrix m n R) (q : ℕ) :
    (observabilityMatrix M P q).map φ = observabilityMatrix (M.map φ) (P.map φ) q := by
  ext ij k
  have h : (P * M ^ ij.1.val).map φ = P.map φ * (M ^ ij.1.val).map φ := Matrix.map_mul
  have hpow : (M ^ ij.1.val).map φ = (M.map φ) ^ ij.1.val := map_pow φ.mapMatrix M ij.1.val
  rw [hpow] at h
  have he := congrArg (fun A : Matrix m n S => A ij.2 k) h
  exact he

theorem observabilityMatrix_mulVec {K n m : Type*} [Field K] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (P : Matrix m n K) (q : ℕ) (v : n → K) (i : Fin q) (j : m) :
    (observabilityMatrix M P q *ᵥ v) (i, j) = (observabilityMap M P q v) i j := by
  change ((P * M ^ i.val) *ᵥ v) j = (P *ᵥ (M ^ i.val *ᵥ v)) j
  rw [Matrix.mulVec_mulVec]

theorem observabilityMatrix_ker {K n m : Type*} [Field K]
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (M : Matrix n n K) (P : Matrix m n K) (q : ℕ) :
    LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q)) = unobservableSpace M P q := by
  rw [← observabilityMap_ker]
  ext v
  constructor
  · intro h
    apply funext
    intro i
    apply funext
    intro j
    simpa only [Matrix.toLin'_apply, observabilityMatrix_mulVec] using congrFun h (i, j)
  · intro h
    apply funext
    rintro ⟨i, j⟩
    simpa only [Matrix.toLin'_apply, observabilityMatrix_mulVec] using congrFun (congrFun h i) j

theorem observabilityMatrix_surjective {K n m : Type*} [Field K]
    [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (P : Matrix m n K) (q : ℕ)
    (h : Function.Surjective (observabilityMap M P q)) :
    Function.Surjective (observabilityMatrix M P q).mulVec := by
  intro w
  obtain ⟨v, hv⟩ := h (fun i j => w (i, j))
  refine ⟨v, ?_⟩
  funext ij
  rw [observabilityMatrix_mulVec, hv]

end FD56
