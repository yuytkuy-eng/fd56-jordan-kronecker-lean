/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericMiddleSLHigh

/-! Low-degree vanishing and sharp scalar surjectivity when the first
generic kernel has uniform minimal degree. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

theorem uniform_minimal_kernel_basis {u v : Type*} [Fintype v] [DecidableEq v]
    (A : Matrix u v K[X]) (r a : ℕ)
    (h : HasMinimalKernelDegrees A (List.replicate r a)) :
    ∃ B : Basis (Fin r) K[X] (LinearMap.ker (Matrix.toLin' A)),
      (∀ x i, (polynomialKernelBasisMatrix A B x i).natDegree ≤ a) ∧
      Function.Injective (Matrix.mulVec
        (fun x i => (polynomialKernelBasisMatrix A B x i).coeff a)) := by
  obtain ⟨s, B, e, hB, hL, hp⟩ := h
  have hs : s = r := by simpa using hp.length_eq
  subst s
  have he : ∀ i, e i = a := by
    intro i
    have hi : e i ∈ List.replicate r a := hp.mem_iff.mp (List.mem_ofFn.mpr ⟨i, rfl⟩)
    exact (List.mem_replicate.mp hi).2
  exact ⟨B, by simpa only [he] using hB, by simpa only [he] using hL⟩

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem generic_uniform_kernel_basis (a r : ℕ) (hr : 0 < r)
    (hm : Fintype.card m = a * r) (hn : Fintype.card n = (a + 1) * r) :
    ∃ B : Basis (Fin r) (Polynomial (AffineCoefficientField K (MatrixParameters n m)))
      (LinearMap.ker (Matrix.toLin' (genericAffineRows K n m))),
      (∀ x i, (polynomialKernelBasisMatrix (genericAffineRows K n m) B x i).natDegree ≤ a) ∧
      Function.Injective (Matrix.mulVec
        (fun x i => (polynomialKernelBasisMatrix (genericAffineRows K n m) B x i).coeff a)) := by
  have hmn : Fintype.card m < Fintype.card n := by rw [hm, hn]; nlinarith
  have hdiff : Fintype.card n - Fintype.card m = r := by
    rw [hm, hn, Nat.add_mul, one_mul, Nat.add_sub_cancel_left]
  apply uniform_minimal_kernel_basis
  have h := generic_rows_minimal_degrees (K := K) hmn
  rw [hdiff, hm] at h
  simpa [balancedDegreeList, Nat.ne_of_gt hr] using h

theorem middle_uniform_slHilbert_low {r : Type*} [Fintype r] [DecidableEq r]
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (a d : ℕ) (hd : d ≤ a) (hP : DegreeBound P 1)
    (hB : ∀ x i, (polynomialKernelBasisMatrix P B x i).natDegree ≤ a)
    (hBlead : Function.Injective
      (Matrix.mulVec (fun x i => (polynomialKernelBasisMatrix P B x i).coeff a)))
    (hPlead : Function.Injective (matrixCoeff P 1).transpose.mulVec) (i₀ : n) (j₀ : r) :
    slHilbert M P d = 0 := by
  letI : Nonempty n := ⟨i₀⟩
  have hbot : boundedSLKernel M P d = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro z hz
    obtain ⟨E, c, hEG, hX, hU⟩ := (middle_sl_radical_iff M P B R hPR hG
      (entries z.1) (entries z.2)).mp hz
    have hweight := (middle_product_degree_iff (polynomialKernelBasisMatrix P B) P E
      (fun _ => a) d hB hBlead hP hPlead).mp (by
        change DegreeBound (middleSLX P B E) d
        rw [← hX]
        exact entries_degree z.1)
    have hE : E = 0 := by
      funext i j
      rcases hweight i j with he | ⟨hle, _⟩
      · exact he
      · omega
    have hc : c = 0 := by
      have hh := congrArg (fun A : Matrix r r K[X] => A j₀ j₀) hEG
      simpa [hE] using hh.symm
    apply Prod.ext
    · apply entries_injective d
      simpa [middleSLX, hE] using hX
    · apply entries_injective d
      simpa [middleSLTranslation, middleSLX, hE, hc] using hU
  simp [slHilbert, hbot]

theorem generic_uniform_slHilbert_low (a r : ℕ) (ha : 1 ≤ a) (hr : 0 < r)
    (hm : Fintype.card m = a * r) (hn : Fintype.card n = (a + 1) * r)
    (i₀ : n) (d : ℕ) (hd : d ≤ a) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d = 0 := by
  have hmn : Fintype.card m < Fintype.card n := by rw [hm, hn]; nlinarith
  have hnm : Fintype.card n ≤ 2 * Fintype.card m := by rw [hm, hn]; nlinarith
  obtain ⟨B, hB, hBL⟩ := generic_uniform_kernel_basis (K := K) a r hr hm hn
  obtain ⟨R, _, hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n (by omega) hmn
  exact middle_uniform_slHilbert_low _ _ B R hPR
    (generic_middle_kernel_transfer_injective hnm B) a d hd
    (genericAffineRows_degree K n m) hB hBL
    (matrix_transpose_injective_of_surjective _
      (generic_affine_rows_leading_surjective K m n hmn.le)) i₀ ⟨0, hr⟩

theorem generic_uniform_slHilbert_high (a r : ℕ) (ha : 4 ≤ a) (hr : 0 < r)
    (hm : Fintype.card m = a * r) (hn : Fintype.card n = (a + 1) * r)
    (i₀ : n) (d : ℕ) (hd : a + 2 ≤ d) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d =
      Module.finrank (AffineCoefficientField K (MatrixParameters n m))
        (polynomialKernelAtDegree
          (glEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m)) d) +
        (d + 2) := by
  letI : Nonempty n := ⟨i₀⟩
  have hmn : Fintype.card m < Fintype.card n := by rw [hm, hn]; nlinarith
  have hnm : Fintype.card n < 2 * Fintype.card m := by rw [hm, hn]; nlinarith
  obtain ⟨B, hB, hBL⟩ := generic_uniform_kernel_basis (K := K) a r hr hm hn
  obtain ⟨R, _, hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n (by omega) hmn
  have hlead := matrix_transpose_injective_of_surjective _
    (generic_affine_rows_leading_surjective K m n hmn.le)
  have hsum : ∑ _ : Fin r, a = Fintype.card m := by simp [hm, Nat.mul_comm]
  have hsize : Fintype.card n = Fintype.card m + Fintype.card (Fin r) := by
    simp only [Fintype.card_fin]
    rw [hm, hn]
    ring
  apply middle_slHilbert_of_scalar_lifts _ _ B R hPR
    (generic_middle_kernel_transfer_injective hnm.le B)
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) i₀ d
  intro c hc
  have hs : ∀ i : Fin r, Function.Surjective (weightedCoefficientMatrix
      (genericAffineRows K n m * genericAffineSquare K n m *
        polynomialKernelBasisMatrix (genericAffineRows K n m) B).transpose
      (fun _ => d - (a + 1)) (fun _ => d - (a + 1) + a + 2)).mulVec := by
    intro i
    apply generic_middle_column_coefficient_surjective B (fun _ => a) hB hsum hsize hmn hnm
    simp only [Fintype.card_fin, hm]
    have hrle : r ≤ a * r := by nlinarith
    have hsub := Nat.sub_add_cancel hrle
    have ht : 2 ≤ d - (a + 1) + 1 := by omega
    have hsmall : a * r + 2 * r ≤ (a * r - r) * 2 := by nlinarith
    exact hsmall.trans (Nat.mul_le_mul_left _ ht)
  obtain ⟨X, U, hX, hU, htr, hPX, hcomm⟩ := middle_sl_scalar_lift _ _ B R hPR
    (fun _ => a) d (fun _ => by dsimp; omega) (genericAffineSquare_degree K n m)
    (genericAffineRows_degree K n m) hB hBL hlead hs c hc
  exact ⟨X, U, hX, hU, (slRadical_iff_equations _ _ _ _).mpr ⟨htr, hPX, c, hcomm⟩, hcomm⟩

end FD56
