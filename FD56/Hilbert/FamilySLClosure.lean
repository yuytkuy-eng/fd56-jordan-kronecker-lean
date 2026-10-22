/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.FamilySL

/-! The critical degree-five equality determines the complete SL degree list
for the family `(n,m) = (11k,8k)`. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

/-- If SL has no additional scalar solutions at one degree, it has none at
any smaller degree. -/
theorem slHilbert_eq_gl_below_of_eq_at_degree
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (i₀ : n)
    (htrace : ∀ (X : Matrix n n K[X]) (U : Matrix n m K[X]),
      P * X = 0 → M * X - X * M = U * P → Matrix.trace X = 0)
    (D d : ℕ) (hd : d ≤ D)
    (hH : slHilbert M P D =
      Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) D)) :
    slHilbert M P d =
      Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d) := by
  have hr := slHilbert_eq_gl_add_scalar_range M P hM hP i₀ D htrace
  have hdim : Module.finrank K (LinearMap.range (boundedSLScalar M P hM hP i₀ D)) = 0 := by
    omega
  have hzero : boundedSLScalar M P hM hP i₀ D = 0 := by
    rwa [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at hdim
  apply slHilbert_eq_gl_of_scalar_obstruction M P hM hP i₀ d htrace
  intro X U c hX hU hs hcomm
  let z : boundedSLKernel M P D :=
    ⟨(boundedMatrixOf X (fun i j => (hX i j).trans hd),
      boundedMatrixOf U (fun i j => (hU i j).trans hd)), hs⟩
  have hz : boundedSLScalar M P hM hP i₀ D z = 0 := by rw [hzero]; rfl
  have hh := (boundedSLScalar_zero_iff M P hM hP i₀ D z).mp hz
  change M * X - X * M - U * P = 0 at hh
  rw [hcomm, add_sub_cancel_left] at hh
  have he := congrArg (fun A : Matrix n n K[X] => A i₀ i₀) hh
  simpa using he

theorem generic_middle_slHilbert_eq_gl_below_of_eq_at_degree
    (i₀ : n) (hmn : Fintype.card m < Fintype.card n)
    (hnm : Fintype.card n < 2 * Fintype.card m) (D d : ℕ) (hd : d ≤ D)
    (hH : slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) D =
      Module.finrank (AffineCoefficientField K (MatrixParameters n m))
        (polynomialKernelAtDegree
          (glEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m)) D)) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d =
      Module.finrank (AffineCoefficientField K (MatrixParameters n m))
        (polynomialKernelAtDegree
          (glEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m)) d) := by
  obtain ⟨r, B, a, hV, hVL, ha⟩ := generic_rows_minimal_degrees (K := K) hmn
  obtain ⟨R, _, hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n (by omega) hmn
  exact slHilbert_eq_gl_below_of_eq_at_degree _ _
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) i₀
    (middle_gl_trace_zero _ _ B R hPR (generic_middle_kernel_transfer_injective hnm.le B))
    D d hd hH

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] in
theorem generic_family_sl_minimal_degrees_of_degree_five
    (k : ℕ) (hk : 0 < k) (i₀ : Fin (11 * k))
    (h5 : slHilbert (genericAffineSquare K (Fin (11 * k)) (Fin (8 * k)))
      (genericAffineRows K (Fin (11 * k)) (Fin (8 * k))) 5 = k ^ 2) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (11 * k)) (Fin (8 * k)))
      (genericAffineRows K (Fin (11 * k)) (Fin (8 * k))) i₀)
      (List.replicate (k ^ 2) 5 ++ List.replicate (6 * k ^ 2 + 8) 6 ++
        List.replicate (8 * k ^ 2 - 7) 7) := by
  have hGL := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
    (generic_family_gl_minimal_degrees (K := K) k hk)
  have h5' : slHilbert (genericAffineSquare K (Fin (11 * k)) (Fin (8 * k)))
      (genericAffineRows K (Fin (11 * k)) (Fin (8 * k))) 5 =
      Module.finrank (AffineCoefficientField K (MatrixParameters (Fin (11 * k)) (Fin (8 * k))))
        (polynomialKernelAtDegree (glEquationMatrix
          (genericAffineSquare K (Fin (11 * k)) (Fin (8 * k)))
          (genericAffineRows K (Fin (11 * k)) (Fin (8 * k)))) 5) := by
    rw [h5, hGL 5]
    simp
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [← slHilbert_eq_matrix_kernel _ _ i₀]
  simp only [List.map_append, List.map_replicate, List.sum_append,
    List.sum_replicate, smul_eq_mul]
  by_cases hd : d ≤ 5
  · rw [generic_middle_slHilbert_eq_gl_below_of_eq_at_degree i₀
      (by simp; omega) (by simp; omega) 5 d hd h5', hGL d]
    have h6 : d + 1 - 6 = 0 := by omega
    have h7 : d + 1 - 7 = 0 := by omega
    simp [h6, h7]
  · rw [generic_family_slHilbert_high k hk d (by omega)]
    have h4 : d + 1 - 5 = d - 4 := by omega
    have h5d : d + 1 - 6 = d - 5 := by omega
    have h6 : d + 1 - 7 = d - 6 := by omega
    rw [h4, h5d, h6]
    have hk2 : 1 ≤ k ^ 2 := by nlinarith
    have hsub : 8 * k ^ 2 - 7 + 7 = 8 * k ^ 2 := Nat.sub_add_cancel (by omega)
    have hd5 : d - 5 = d - 6 + 1 := by omega
    have hd2 : d + 2 = d - 6 + 8 := by omega
    rw [hd5, hd2]
    conv_lhs => rw [← hsub]
    ring

end FD56
