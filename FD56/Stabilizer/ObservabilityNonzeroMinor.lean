/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericTerminalObservability
import FD56.Stabilizer.ObservabilityCovariance
import FD56.LinearAlgebra.NonzeroMaximalMinor

/-! Universal observability has a nonzero maximal minor whenever the row count permits it. -/

noncomputable section
namespace FD56
open Matrix

theorem observabilityMatrix_injective_mono {K n m : Type*} [Field K]
    [Fintype n] [DecidableEq n] (M : Matrix n n K) (P : Matrix m n K)
    {q r : ℕ} (hqr : q ≤ r) (hi : Function.Injective (observabilityMatrix M P q).mulVec) :
    Function.Injective (observabilityMatrix M P r).mulVec := by
  intro v w h
  apply hi
  funext ij
  exact congrFun h (Fin.castLE hqr ij.1, ij.2)

/-- Existing terminal witnesses extend to every depth allowed by the row count. -/
theorem exists_observability_witness_of_sizes {K n m : Type*} [Field K]
    [Fintype n] [Fintype m] [DecidableEq n] (q : ℕ)
    (hnm : Fintype.card n ≤ q * Fintype.card m) :
    ∃ (M : Matrix n n K) (P : Matrix m n K),
      Function.Injective (observabilityMatrix M P q).mulVec := by
  induction q with
  | zero =>
    have hn : Fintype.card n = 0 := by simpa using hnm
    letI : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
    exact ⟨0, 0, fun _ _ _ => Subsingleton.elim _ _⟩
  | succ q ih =>
    by_cases hlow : q * Fintype.card m ≤ Fintype.card n
    · exact exists_terminal_observability_witness q hlow hnm
    · obtain ⟨M, P, hi⟩ := ih (Nat.le_of_lt (Nat.lt_of_not_ge hlow))
      exact ⟨M, P, observabilityMatrix_injective_mono M P (Nat.le_succ q) hi⟩

/-- A specialized nonzero minor certifies that the corresponding universal minor is nonzero. -/
theorem universal_observability_exists_nonzero_minor {K n m : Type*} [Field K]
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] (q : ℕ)
    (hnm : Fintype.card n ≤ q * Fintype.card m) :
    ∃ r : n → Fin q × m,
      ((observabilityMatrix (universalSquare K n m) (universalRows K n m) q).submatrix
        r id).det ≠ 0 := by
  obtain ⟨M, P, hi⟩ := exists_observability_witness_of_sizes (K := K) q hnm
  obtain ⟨r, hr⟩ := exists_nonzero_maximal_minor_of_injective (observabilityMatrix M P q) hi
  refine ⟨r, ?_⟩
  intro hz
  apply hr
  have hmap := observabilityMatrix_minor_map (matrixSpecialization M P)
    (universalSquare K n m) (universalRows K n m) q r
  rw [(universal_pair_specialization M P).1, (universal_pair_specialization M P).2,
    hz, map_zero] at hmap
  exact hmap.symm

theorem universal_observability_common_divisor_ne_zero {K n m : Type*} [Field K]
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] (q : ℕ)
    (hnm : Fintype.card n ≤ q * Fintype.card m)
    (g : MvPolynomial (MatrixParameters n m) K)
    (hg : ∀ r : n → Fin q × m,
      g ∣ ((observabilityMatrix (universalSquare K n m) (universalRows K n m) q).submatrix
        r id).det) : g ≠ 0 := by
  obtain ⟨r, hr⟩ := universal_observability_exists_nonzero_minor (K := K) q hnm
  intro hg0
  exact hr (by simpa only [hg0, zero_dvd_iff] using hg r)

end FD56
