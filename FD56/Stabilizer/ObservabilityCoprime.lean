/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ObservabilityHypersurface
import FD56.Stabilizer.ObservabilityInvariantKernel
import FD56.Stabilizer.ObservabilityDivisorKernel
import FD56.Stabilizer.ObservabilityNonzeroMinor
import FD56.LinearAlgebra.IrreducibleCommonDivisors
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! Maximal minors of a strictly tall universal observability matrix are coprime. -/

noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
namespace FD56
open Matrix
variable {K n m : Type*} [Field K] [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]

theorem universal_observability_no_irreducible_common_divisor
    (q : ℕ) (hm : 2 ≤ Fintype.card m) (hn : Fintype.card n < q * Fintype.card m)
    (g : MvPolynomial (MatrixParameters n m) K) (hg : Irreducible g) :
    ¬ ∀ r : n → Fin q × m,
      g ∣ ((observabilityMatrix (universalSquare K n m) (universalRows K n m) q).submatrix
        r id).det := by
  intro hdiv
  have hp : Prime g := UniqueFactorizationMonoid.irreducible_iff_prime.mp hg
  letI : (Ideal.span ({g} : Set (MvPolynomial (MatrixParameters n m) K))).IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  obtain ⟨c, v, hv, hc⟩ := normalized_observability_kernel_of_common_divisor
    (principalQuotientFieldMap g).toRingHom (universalSquare K n m)
    (universalRows K n m) q g hdiv
    ((principalQuotientFieldMap_eq_zero_iff g g).mpr (dvd_refl g))
  change observabilityMatrix (quotientStateMatrix g) (quotientOutputMatrix g) q *ᵥ v = 0 at hv
  have hiter := observability_kernel_iterates _ _ q v hv
  have hdep := quotient_observability_krylov_dependent g hp.ne_zero hg.not_isUnit
    q hn v c hc hiter
  have hq : 0 < q := Nat.pos_of_ne_zero (by intro he; simp [he] at hn)
  have hv0 : v ≠ 0 := by
    intro h
    have he := congrFun h c
    rw [hc] at he
    exact one_ne_zero he
  obtain ⟨W, hW, hinv, hker⟩ := exists_invariant_subspace_of_dependent_observability_kernel
    (quotientStateMatrix g) (quotientOutputMatrix g) q hq v hv0 hiter hdep
  exact quotient_no_invariant_output_kernel g hp.ne_zero hg.not_isUnit hm W hW hinv hker

theorem universal_observability_common_divisor_isUnit
    (q : ℕ) (hm : 2 ≤ Fintype.card m) (hn : Fintype.card n < q * Fintype.card m)
    (g : MvPolynomial (MatrixParameters n m) K)
    (hdiv : ∀ r : n → Fin q × m,
      g ∣ ((observabilityMatrix (universalSquare K n m) (universalRows K n m) q).submatrix
        r id).det) : IsUnit g := by
  exact isUnit_of_common_divisor_of_no_irreducible_common_divisor
    (fun r : n → Fin q × m =>
      ((observabilityMatrix (universalSquare K n m) (universalRows K n m) q).submatrix
        r id).det)
    (universal_observability_exists_nonzero_minor q hn.le)
    (universal_observability_no_irreducible_common_divisor q hm hn) hdiv

theorem universal_observability_minor_gcd_eq_one
    [NormalizedGCDMonoid (MvPolynomial (MatrixParameters n m) K)]
    (q : ℕ) (hm : 2 ≤ Fintype.card m) (hn : Fintype.card n < q * Fintype.card m) :
    observabilityMinorGCD (universalSquare K n m) (universalRows K n m) q = 1 := by
  have h := universal_observability_common_divisor_isUnit (K := K) q hm hn
    (observabilityMinorGCD (universalSquare K n m) (universalRows K n m) q)
    (fun r => Finset.gcd_dvd (Finset.mem_univ r))
  simpa only [observabilityMinorGCD, Finset.normalize_gcd] using normalize_eq_one.mpr h

end FD56
