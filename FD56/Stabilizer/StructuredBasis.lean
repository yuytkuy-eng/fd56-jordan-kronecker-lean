/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.Telescoping
import FD56.Stabilizer.GLBase

/-! The structured construction spans the entire field stabilizer once its
one-sided inverse conditions and the matching dimension are established. -/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators
variable {K n m r s : Type*} [Field K] [Fintype n] [Fintype m]
  [Fintype r] [Fintype s] [DecidableEq n] [DecidableEq r] [DecidableEq s]

def structuredStabilizerMap (M : Matrix n n K) (P : Matrix m n K)
    (V : Matrix n r K) (H : ℕ → Matrix s n K) (D : ℕ → Matrix s m K)
    (T : Matrix s m K) (q : ℕ)
    (hzero : H 0 * M = D 0 * P)
    (hstep : ∀ i < q, H (i + 1) * M = H i + D (i + 1) * P)
    (hend : H q = T * P)
    (hobs : ∀ i < q + 1, P * M ^ i * V = 0) :
    Matrix r s K →ₗ[K] glStabilizerSpace M P where
  toFun C := ⟨(∑ i ∈ Finset.range (q + 1), M ^ i * V * C * H i,
    M ^ (q + 1) * V * C * T - ∑ i ∈ Finset.range (q + 1), M ^ i * V * C * D i),
    structured_kernel M P V C H D T q hzero hstep hend hobs⟩
  map_add' C E := by
    apply Subtype.ext
    apply Prod.ext
    · simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
    · change (M ^ (q + 1) * V * (C + E) * T -
          ∑ i ∈ Finset.range (q + 1), M ^ i * V * (C + E) * D i) =
        (M ^ (q + 1) * V * C * T - ∑ i ∈ Finset.range (q + 1), M ^ i * V * C * D i) +
        (M ^ (q + 1) * V * E * T - ∑ i ∈ Finset.range (q + 1), M ^ i * V * E * D i)
      simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib,
        Prod.fst_add, Prod.snd_add]
      abel
  map_smul' c C := by
    apply Subtype.ext
    apply Prod.ext
    · simp [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
    · simp [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, smul_sub]

theorem structuredStabilizerMap_injective (M : Matrix n n K) (P : Matrix m n K)
    (V : Matrix n r K) (H : ℕ → Matrix s n K) (D : ℕ → Matrix s m K)
    (T : Matrix s m K) (q : ℕ)
    (hzero : H 0 * M = D 0 * P)
    (hstep : ∀ i < q, H (i + 1) * M = H i + D (i + 1) * P)
    (hend : H q = T * P)
    (hobs : ∀ i < q + 1, P * M ^ i * V = 0)
    (L : Matrix r m K) (B : Matrix n s K)
    (hL : L * (P * M ^ (q + 1) * V) = 1) (hB : (T * P) * B = 1) :
    Function.Injective (structuredStabilizerMap M P V H D T q hzero hstep hend hobs) := by
  intro C E h
  apply structured_kernel_injective M P V H T q hend hobs L B hL hB
  exact congrArg (fun z : glStabilizerSpace M P => z.val.1) h

theorem structuredStabilizerMap_bijective (M : Matrix n n K) (P : Matrix m n K)
    (V : Matrix n r K) (H : ℕ → Matrix s n K) (D : ℕ → Matrix s m K)
    (T : Matrix s m K) (q : ℕ)
    (hzero : H 0 * M = D 0 * P)
    (hstep : ∀ i < q, H (i + 1) * M = H i + D (i + 1) * P)
    (hend : H q = T * P)
    (hobs : ∀ i < q + 1, P * M ^ i * V = 0)
    (L : Matrix r m K) (B : Matrix n s K)
    (hL : L * (P * M ^ (q + 1) * V) = 1) (hB : (T * P) * B = 1)
    (hdim : Module.finrank K (glStabilizerSpace M P) = Fintype.card r * Fintype.card s) :
    Function.Bijective (structuredStabilizerMap M P V H D T q hzero hstep hend hobs) := by
  let f := structuredStabilizerMap M P V H D T q hzero hstep hend hobs
  have hinj : Function.Injective f :=
    structuredStabilizerMap_injective M P V H D T q hzero hstep hend hobs L B hL hB
  refine ⟨hinj, ?_⟩
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_of_le_of_finrank_eq le_top
  have h := f.finrank_range_add_finrank_ker
  rw [LinearMap.ker_eq_bot.mpr hinj] at h
  simpa [hdim, Module.finrank_matrix] using h

end FD56
