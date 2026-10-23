/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformSL

/-! A finite coefficient relation embeds into the actual bounded SL radical.
Rank-nullity therefore gives a lower bound at the uniform critical degree. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m r : Type*} [Field K] [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m] [DecidableEq r]

def constantSLRelation (G : Matrix m r K[X]) (b : ℕ) (hG : DegreeBound G b) :
    (BoundedMatrix K r m 0 × BoundedPoly K b) →ₗ[K] BoundedMatrix K r r b where
  toFun z := boundedMatrixOf (entries z.1 * G + z.2.val • 1) (by
    intro i j
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · simpa using degreeBound_mul (entries_degree z.1) hG i j
    · by_cases hij : i = j
      · simpa [Matrix.one_apply, hij] using boundedPoly_degree b z.2
      · simp [Matrix.one_apply, hij])
  map_add' z w := by
    apply entries_injective b
    simp only [entries_boundedMatrixOf, entries_add]
    change (entries z.1 + entries w.1) * G + (z.2.val + w.2.val) • 1 = _
    rw [Matrix.add_mul, add_smul]
    abel
  map_smul' k z := by
    apply entries_injective b
    simp only [entries_boundedMatrixOf, entries_smul]
    change (k • entries z.1) * G + (k • z.2.val) • 1 = _
    rw [Matrix.smul_mul, smul_assoc, smul_add]
    rfl

omit [Fintype r] [DecidableEq m] in
theorem constantSLRelation_mem_ker (G : Matrix m r K[X]) (b : ℕ)
    (hG : DegreeBound G b) (z : BoundedMatrix K r m 0 × BoundedPoly K b) :
    z ∈ LinearMap.ker (constantSLRelation G b hG) ↔
      entries z.1 * G = (-z.2.val) • 1 := by
  change constantSLRelation G b hG z = 0 ↔ _
  rw [← (entries_injective b).eq_iff]
  change entries z.1 * G + z.2.val • 1 = 0 ↔ _
  rw [add_eq_zero_iff_eq_neg, neg_smul]

omit [DecidableEq m] in
theorem constantSLRelation_kernel_lower (G : Matrix m r K[X]) (b : ℕ)
    (hG : DegreeBound G b) :
    Fintype.card r * Fintype.card m + (b + 1) -
      Fintype.card r * Fintype.card r * (b + 1) ≤
      Module.finrank K (LinearMap.ker (constantSLRelation G b hG)) := by
  have hd := (constantSLRelation G b hG).finrank_range_add_finrank_ker
  have hr := Submodule.finrank_le (LinearMap.range (constantSLRelation G b hG))
  simp only [Module.finrank_prod, boundedMatrix_finrank, boundedPoly_finrank,
    zero_add, mul_one] at hd hr
  omega

variable (M : Matrix n n K[X]) (P : Matrix m n K[X])
  (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
  (R : Matrix n m K[X]) (hPR : P * R = 1) (a : ℕ)
  (hM : DegreeBound M 1) (hP : DegreeBound P 1)
  (hB : DegreeBound (polynomialKernelBasisMatrix P B) a)
  (hPlead : Function.Injective (matrixCoeff P 1).transpose.mulVec)

include hM hP hB in
omit [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r] in
theorem uniform_middle_matrix_degree :
    DegreeBound (P * M * polynomialKernelBasisMatrix P B) (a + 2) := by
  simpa only [Nat.add_comm 2 a] using degreeBound_mul (degreeBound_mul hP hM) hB

def constantSLRelationLift [Nonempty n] :
    LinearMap.ker (constantSLRelation (P * M * polynomialKernelBasisMatrix P B)
      (a + 2) (uniform_middle_matrix_degree M P B a hM hP hB)) →ₗ[K]
      boundedSLKernel M P (a + 1) where
  toFun z := by
    have hrel := (constantSLRelation_mem_ker _ _ _ z.val).mp z.property
    have he := middle_sl_reconstruct M P B R hPR (entries z.val.1) z.val.2.val hrel
    have hX : DegreeBound (middleSLX P B (entries z.val.1)) (a + 1) := by
      simpa only [Nat.add_zero] using degreeBound_mul
        (degreeBound_mul hB (entries_degree z.val.1)) hP
    have hU := middle_translation_degree M P _ _ _ (a + 1)
      hM hP hPlead hX (boundedPoly_degree _ z.val.2) he.2.2
    exact ⟨(boundedMatrixOf _ hX, boundedMatrixOf _ hU),
      (slRadical_iff_equations M P _ _).mpr ⟨he.1, he.2.1, z.val.2.val, he.2.2⟩⟩
  map_add' z w := by
    apply Subtype.ext
    apply Prod.ext
    · apply entries_injective (a + 1)
      change middleSLX P B (entries z.val.1 + entries w.val.1) =
        middleSLX P B (entries z.val.1) + middleSLX P B (entries w.val.1)
      simp only [middleSLX, Matrix.mul_add, Matrix.add_mul]
    · apply entries_injective (a + 1)
      change middleSLTranslation M P B R (entries z.val.1 + entries w.val.1)
        (z.val.2.val + w.val.2.val) =
        middleSLTranslation M P B R (entries z.val.1) z.val.2.val +
        middleSLTranslation M P B R (entries w.val.1) w.val.2.val
      simp only [middleSLTranslation, middleSLX, Matrix.mul_add, Matrix.add_mul,
        Matrix.sub_mul, add_smul]
      abel
  map_smul' k z := by
    apply Subtype.ext
    apply Prod.ext
    · apply entries_injective (a + 1)
      change middleSLX P B (k • entries z.val.1) = k • middleSLX P B (entries z.val.1)
      simp only [middleSLX, Matrix.mul_smul, Matrix.smul_mul]
    · apply entries_injective (a + 1)
      change middleSLTranslation M P B R (k • entries z.val.1) (k • z.val.2.val) =
        k • middleSLTranslation M P B R (entries z.val.1) z.val.2.val
      simp only [middleSLTranslation, middleSLX, Matrix.mul_smul, Matrix.smul_mul,
        smul_assoc, smul_sub]
      rw [← smul_sub, ← smul_sub, Matrix.smul_mul]

theorem constantSLRelationLift_injective [Nonempty n] (j₀ : r) :
    Function.Injective (constantSLRelationLift M P B R hPR a hM hP hB hPlead) := by
  intro z w h
  have hX := congrArg (fun y : boundedSLKernel M P (a + 1) => entries y.val.1) h
  change middleSLX P B (entries z.val.1) = middleSLX P B (entries w.val.1) at hX
  have hE := (entries_injective 0) (middleSLX_injective P B R hPR hX)
  apply Subtype.ext
  apply Prod.ext hE
  apply Subtype.ext
  have hz := (constantSLRelation_mem_ker _ _ _ z.val).mp z.property
  have hw := (constantSLRelation_mem_ker _ _ _ w.val).mp w.property
  rw [hE] at hz
  have hc := congrArg (fun A : Matrix r r K[X] => A j₀ j₀) (hz.symm.trans hw)
  simpa using hc

theorem constantSLRelationLift_surjective [Nonempty n] (j₀ : r)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (hBL : Function.Injective (Matrix.mulVec
      (fun x i => (polynomialKernelBasisMatrix P B x i).coeff a))) :
    Function.Surjective (constantSLRelationLift M P B R hPR a hM hP hB hPlead) := by
  intro z
  obtain ⟨E, c, hrel, hX, hU⟩ := (middle_sl_radical_iff M P B R hPR hG
    (entries z.val.1) (entries z.val.2)).mp z.property
  have hweight := (middle_product_degree_iff (polynomialKernelBasisMatrix P B) P E
    (fun _ => a) (a + 1) hB hBL hP hPlead).mp (by
      change DegreeBound (middleSLX P B E) (a + 1)
      rw [← hX]
      exact entries_degree z.val.1)
  have hE : DegreeBound E 0 := by
    intro i j
    rcases hweight i j with hz | ⟨_, hb⟩
    · simp [hz]
    · simpa using hb
  have hc : c.natDegree ≤ a + 2 := middle_scalar_degree_of_weighted M P
    (polynomialKernelBasisMatrix P B) E (fun _ => a) c j₀ (a + 1) hM hP hB hweight hrel
  let w : LinearMap.ker (constantSLRelation (P * M * polynomialKernelBasisMatrix P B)
      (a + 2) (uniform_middle_matrix_degree M P B a hM hP hB)) :=
    ⟨(boundedMatrixOf E hE, boundedPolyOf c hc),
      (constantSLRelation_mem_ker _ _ _ _).mpr hrel⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply entries_injective (a + 1)
    exact hX.symm
  · apply entries_injective (a + 1)
    exact hU.symm

def constantSLRelationEquiv [Nonempty n] (j₀ : r)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (hBL : Function.Injective (Matrix.mulVec
      (fun x i => (polynomialKernelBasisMatrix P B x i).coeff a))) :
    LinearMap.ker (constantSLRelation (P * M * polynomialKernelBasisMatrix P B)
      (a + 2) (uniform_middle_matrix_degree M P B a hM hP hB)) ≃ₗ[K]
      boundedSLKernel M P (a + 1) :=
  LinearEquiv.ofBijective (constantSLRelationLift M P B R hPR a hM hP hB hPlead)
    ⟨constantSLRelationLift_injective M P B R hPR a hM hP hB hPlead j₀,
      constantSLRelationLift_surjective M P B R hPR a hM hP hB hPlead j₀ hG hBL⟩

include R hPR hM hP hPlead in
theorem uniform_middle_slHilbert_critical_eq [Nonempty n] (j₀ : r)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (hBL : Function.Injective (Matrix.mulVec
      (fun x i => (polynomialKernelBasisMatrix P B x i).coeff a))) :
    slHilbert M P (a + 1) = Module.finrank K
      (LinearMap.ker (constantSLRelation (P * M * polynomialKernelBasisMatrix P B)
        (a + 2) (uniform_middle_matrix_degree M P B a hM hP hB))) :=
  (constantSLRelationEquiv M P B R hPR a hM hP hB hPlead j₀ hG hBL).finrank_eq.symm

include B R hPR hM hP hB hPlead in
theorem uniform_middle_slHilbert_critical_lower [Nonempty n] (j₀ : r) :
    Fintype.card r * Fintype.card m + (a + 3) -
      Fintype.card r * Fintype.card r * (a + 3) ≤ slHilbert M P (a + 1) := by
  have hi := LinearMap.finrank_le_finrank_of_injective
    (constantSLRelationLift_injective M P B R hPR a hM hP hB hPlead j₀)
  exact (constantSLRelation_kernel_lower _ _
    (uniform_middle_matrix_degree M P B a hM hP hB)).trans hi

theorem generic_uniform_slHilbert_critical_lower (a r : ℕ) (ha : 1 ≤ a) (hr : 0 < r)
    (hm : Fintype.card m = a * r) (hn : Fintype.card n = (a + 1) * r) (i₀ : n) :
    a + 3 - 3 * r ^ 2 ≤
      slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) (a + 1) := by
  letI : Nonempty n := ⟨i₀⟩
  have hmn : Fintype.card m < Fintype.card n := by rw [hm, hn]; nlinarith
  obtain ⟨B, hB, _⟩ := generic_uniform_kernel_basis (K := K) a r hr hm hn
  obtain ⟨R, _, hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n
    (by rw [hm]; positivity) hmn
  have hh := uniform_middle_slHilbert_critical_lower _ _ B R hPR a
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) hB
    (matrix_transpose_injective_of_surjective _
      (generic_affine_rows_leading_surjective K m n hmn.le)) (⟨0, hr⟩ : Fin r)
  simp only [Fintype.card_fin, hm] at hh
  have he : r * r * (a + 3) = r * (a * r) + 3 * r ^ 2 := by ring
  rw [he, Nat.add_sub_add_left] at hh
  exact hh

end FD56
