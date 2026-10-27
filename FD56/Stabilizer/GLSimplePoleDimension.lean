/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.OutputFactorDimension

/-! The stabilizer dimension at a one-dimensional observability defect. -/

noncomputable section
namespace FD56
open Matrix

theorem gl_square_defect_one_finrank {K : Type*} {n m : Type} [Field K]
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (M : Matrix n n K) (P : Matrix m n K)
    (hsize : Fintype.card n = Fintype.card m) (hm : 2 ≤ Fintype.card m)
    (hfirst : Module.finrank K (unobservableSpace M P 1) = 1)
    (hnext : Module.finrank K (unobservableSpace M P 2) = 0) :
    Module.finrank K (glStabilizerSpace M P) = 2 * Fintype.card m - 2 := by
  have hk : Module.finrank K (LinearMap.ker (Matrix.toLin' P)) = 1 := by
    have he : unobservableSpace M P 1 = LinearMap.ker (Matrix.toLin' P) := by
      ext v
      simp [unobservableSpace, Matrix.toLin'_apply]
    rwa [← he]
  have hd : Module.finrank K (LinearMap.range (Matrix.toLin' P)) = Fintype.card m - 1 := by
    have hh := (Matrix.toLin' P).finrank_range_add_finrank_ker
    rw [hk, Module.finrank_fintype_fun_eq_card, hsize] at hh
    omega
  obtain ⟨Q,V,L,hVQ,hLV,hQ⟩ := matrix_output_factorization P (Fintype.card m - 1) hd
  have he (q : ℕ) : unobservableSpace M P q = unobservableSpace M Q q := by
    rw [← hVQ]
    exact unobservableSpace_output_factor M Q V L hLV q
  have hred : Module.finrank K (glStabilizerSpace M Q) = Fintype.card m - 2 := by
    have hs : Fintype.card n = (0 + 1) * Fintype.card (Fin (Fintype.card m - 1)) + 1 := by
      simp only [Fintype.card_fin, zero_add, one_mul]
      omega
    have h1 : Module.finrank K (unobservableSpace M Q (0 + 1)) = 1 := by
      rw [← he]
      exact hfirst
    have h2 : Module.finrank K (unobservableSpace M Q (0 + 2)) = 0 := by
      rw [← he]
      exact hnext
    have hh := gl_finrank_of_observability 0 1 M Q hs h1 h2
    simpa only [Fintype.card_fin, one_mul, Nat.sub_sub] using hh
  rw [← hVQ, gl_output_factor_finrank M Q V L hLV, hred]
  simp only [Fintype.card_fin, hsize]
  have hsub : Fintype.card m - (Fintype.card m - 1) = 1 := by omega
  rw [hsub, mul_one]
  omega

theorem gl_finrank_of_simple_observability_defect {K : Type*} {n m : Type} [Field K]
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (q : ℕ) (M : Matrix n n K) (P : Matrix m n K)
    (hm : 2 ≤ Fintype.card m)
    (hsize : Fintype.card n = (q + 1) * Fintype.card m)
    (hbefore : Module.finrank K (unobservableSpace M P q) = Fintype.card m)
    (hfirst : Module.finrank K (unobservableSpace M P (q + 1)) = 1)
    (hnext : Module.finrank K (unobservableSpace M P (q + 2)) = 0) :
    Module.finrank K (glStabilizerSpace M P) = 2 * Fintype.card m - 2 := by
  induction q generalizing n with
  | zero =>
    exact gl_square_defect_one_finrank M P (by simpa using hsize) hm hfirst hnext
  | succ q ih =>
    have hP := surjective_of_observabilityMap M P q
      (observabilityMap_surjective_of_finrank M P (q + 1) (by
        rw [hbefore]
        simp only [Nat.succ_eq_add_one, Nat.add_mul, one_mul] at hsize ⊢
        omega))
    obtain ⟨D,B,hd,ho⟩ := gl_observability_reduction M P hP
    rw [hd]
    apply ih D B
    · simp only [Fintype.card_fin, Nat.succ_eq_add_one, Nat.add_mul, one_mul] at hsize ⊢
      omega
    · exact (ho q).symm.trans hbefore
    · exact (ho (q + 1)).symm.trans hfirst
    · exact (ho (q + 2)).symm.trans hnext

end FD56
