/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.Adjugate
import FD56.Hilbert.UniformSLRelationDegree
import FD56.LinearAlgebra.ClearDenominators

/-! Adjugate multiples provide bounded scalar relations for a square cubic
auxiliary matrix, and hence actual SL radical vectors in dimensions (2r,r). -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem matrix_det_ne_zero_of_injective {R a : Type*} [CommRing R] [IsDomain R]
    [Fintype a] [DecidableEq a] (A : Matrix a a R)
    (hA : Function.Injective A.mulVec) : A.det ≠ 0 := by
  let F := FractionRing R
  let φ := algebraMap R F
  have hi : Function.Injective (A.map φ).mulVec := by
    intro v w h
    have hz : A.map φ *ᵥ (v - w) = 0 := by rw [Matrix.mulVec_sub, h, sub_self]
    obtain ⟨c, u, hc, hu, he⟩ := kernel_clear_denominators A (v - w) hz
    have hu0 : u = 0 := hA (hu.trans (Matrix.mulVec_zero A).symm)
    have hc' : φ c ≠ 0 := by
      intro h0
      exact hc ((IsFractionRing.injective R F) (h0.trans (map_zero φ).symm))
    apply sub_eq_zero.mp
    funext i
    have hh := he i
    rw [hu0] at hh
    have hp : φ c * (v - w) i = 0 := hh.symm.trans (map_zero φ)
    exact (mul_eq_zero.mp hp).resolve_left hc'
  obtain ⟨L, hL⟩ := matrix_left_inverse_of_injective (A.map φ) hi
  intro hz
  have hd := congrArg Matrix.det hL
  have hz' : (A.map φ).det = 0 := by
    calc
      _ = φ A.det := (φ.map_det A).symm
      _ = 0 := by rw [hz, map_zero]
  rw [Matrix.det_mul, hz', mul_zero, Matrix.det_one] at hd
  exact zero_ne_one hd

variable {K : Type*} [Field K]

theorem cubic_adjugate_scalar_degree (r : ℕ) (hr : 0 < r)
    (G : Matrix (Fin r) (Fin r) K[X]) (hG : DegreeBound G 3) (k : ℕ)
    (f : Polynomial.degreeLT K (k + 1 - (r - 1) * 3)) :
    (-(f.val * G.det)).natDegree ≤ k + 3 := by
  rw [Polynomial.natDegree_neg]
  rcases (mem_degreeLT_shift_iff f.val k ((r - 1) * 3)).mp f.property with
    hf | ⟨he, hf⟩
  · simp [hf]
  · have hd := polynomial_det_degree G 3 hG
    have hm := Polynomial.natDegree_mul_le (p := f.val) (q := G.det)
    simp only [Fintype.card_fin] at hd
    have hr' : (r - 1) * 3 + 3 = r * 3 := by omega
    omega

def cubicAdjugateRelationMap (r : ℕ) (hr : 0 < r)
    (G : Matrix (Fin r) (Fin r) K[X]) (hG : DegreeBound G 3) (k : ℕ) :
    Polynomial.degreeLT K (k + 1 - (r - 1) * 3) →ₗ[K]
      LinearMap.ker (uniformSLRelation G k 3 hG) where
  toFun f := ⟨(boundedMatrixOf (f.val • G.adjugate)
      (adjugate_multiple_degree G ((r - 1) * 3) k (polynomial_adjugate_degree r 3 G hG) f),
      boundedPolyOf (-(f.val * G.det)) (cubic_adjugate_scalar_degree r hr G hG k f)), by
    apply (uniformSLRelation_mem_ker G k 3 hG _).mpr
    change (f.val • G.adjugate) * G = _
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul]
    change (f.val * G.det) • (1 : Matrix (Fin r) (Fin r) K[X]) =
      (-(-(f.val * G.det))) • 1
    rw [neg_neg]⟩
  map_add' f g := by
    apply Subtype.ext
    apply Prod.ext
    · apply entries_injective k
      exact add_smul f.val g.val G.adjugate
    · apply Subtype.ext
      change -((f.val + g.val) * G.det) = -(f.val * G.det) + -(g.val * G.det)
      ring
  map_smul' c f := by
    apply Subtype.ext
    apply Prod.ext
    · apply entries_injective k
      exact smul_assoc c f.val G.adjugate
    · apply Subtype.ext
      change -((c • f.val) * G.det) = c • -(f.val * G.det)
      rw [smul_mul_assoc, smul_neg]

theorem cubicAdjugateRelationMap_injective (r : ℕ) (hr : 0 < r)
    (G : Matrix (Fin r) (Fin r) K[X]) (hG : DegreeBound G 3) (k : ℕ)
    (hdet : G.det ≠ 0) : Function.Injective (cubicAdjugateRelationMap r hr G hG k) := by
  intro f g h
  apply Subtype.ext
  have hh := congrArg (fun z : LinearMap.ker (uniformSLRelation G k 3 hG) => z.val.2.val) h
  change -(f.val * G.det) = -(g.val * G.det) at hh
  exact mul_right_cancel₀ hdet (neg_injective hh)

theorem cubic_adjugate_relation_lower (r : ℕ) (hr : 0 < r)
    (G : Matrix (Fin r) (Fin r) K[X]) (hG : DegreeBound G 3) (k : ℕ)
    (hdet : G.det ≠ 0) :
    k + 1 - (r - 1) * 3 ≤ Module.finrank K (LinearMap.ker (uniformSLRelation G k 3 hG)) := by
  have hh := LinearMap.finrank_le_finrank_of_injective
    (cubicAdjugateRelationMap_injective r hr G hG k hdet)
  rw [(Polynomial.degreeLTEquiv K (k + 1 - (r - 1) * 3)).finrank_eq] at hh
  simpa using hh

theorem generic_uniform_one_slHilbert_lower (r : ℕ) (hr : 0 < r) (d : ℕ) :
    d + 1 - (3 * r - 1) ≤
      slHilbert (genericAffineSquare K (Fin (2 * r)) (Fin r))
        (genericAffineRows K (Fin (2 * r)) (Fin r)) d := by
  by_cases hd : d < 2
  · have hz : d + 1 - (3 * r - 1) = 0 := by omega
    rw [hz]
    exact Nat.zero_le _
  let i₀ : Fin (2 * r) := ⟨0, by omega⟩
  letI : Nonempty (Fin (2 * r)) := ⟨i₀⟩
  obtain ⟨B, hB, _⟩ := generic_uniform_kernel_basis (K := K)
    (n := Fin (2 * r)) (m := Fin r) 1 r hr (by simp) (by simp)
  obtain ⟨R, _, hPR⟩ := generic_affine_rows_right_inverse_of_sizes K (Fin r) (Fin (2 * r))
    (by simpa using hr) (by simp; omega)
  let G := genericAffineRows K (Fin (2 * r)) (Fin r) *
    genericAffineSquare K (Fin (2 * r)) (Fin r) *
      polynomialKernelBasisMatrix (genericAffineRows K (Fin (2 * r)) (Fin r)) B
  have hG : DegreeBound G 3 := uniform_middle_matrix_degree _ _ B 1
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _) hB
  have hdet : G.det ≠ 0 := matrix_det_ne_zero_of_injective G
    (generic_middle_kernel_transfer_injective (by simp) B)
  have hl := cubic_adjugate_relation_lower r hr G hG (d - 2) hdet
  have hi := LinearMap.finrank_le_finrank_of_injective
    (uniformSLRelationLift_injective _ _ B R hPR 1 (d - 2)
      (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _) hB
      (matrix_transpose_injective_of_surjective _
        (generic_affine_rows_leading_surjective K (Fin r) (Fin (2 * r)) (by simp; omega)))
      (⟨0, hr⟩ : Fin r))
  have hh := hl.trans hi
  have hdeg : 1 + (d - 2) + 1 = d := by omega
  change _ ≤ slHilbert _ _ (1 + (d - 2) + 1) at hh
  rw [hdeg] at hh
  have hnum : d - 2 + 1 - (r - 1) * 3 = d + 1 - (3 * r - 1) := by omega
  rwa [hnum] at hh

end FD56
