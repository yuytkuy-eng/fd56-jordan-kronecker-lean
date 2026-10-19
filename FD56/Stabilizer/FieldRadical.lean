/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GLWitness
import FD56.Stabilizer.TraceAnnihilator
import FD56.LinearAlgebra.HyperplaneRadical

/-! The field-valued Kirillov form connects matrix stabilizers with
hyperplane restriction and the SL radical dimension. -/

noncomputable section
namespace FD56
open Matrix
universe u
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

abbrev MatrixAlgebraSpace (K n m : Type*) := Matrix n n K × Matrix n m K

def matrixKirillov (M : Matrix n n K) (P : Matrix m n K)
    (z w : MatrixAlgebraSpace K n m) : K :=
  Matrix.trace (M * (z.1 * w.1 - w.1 * z.1)) +
    Matrix.trace (P * (z.1 * w.2 - w.1 * z.2))

def fieldKirillovForm (M : Matrix n n K) (P : Matrix m n K) :
    MatrixAlgebraSpace K n m →ₗ[K] MatrixAlgebraSpace K n m →ₗ[K] K where
  toFun z := {
    toFun := matrixKirillov M P z
    map_add' := by
      intro w v
      simp only [matrixKirillov, Prod.fst_add, Prod.snd_add, Matrix.add_mul,
        Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub]
      ring
    map_smul' := by
      intro c w
      simp [matrixKirillov, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub,
        Matrix.trace_smul, smul_add, mul_add] }
  map_add' := by
    intro z v
    apply LinearMap.ext
    intro w
    change matrixKirillov M P (z + v) w = matrixKirillov M P z w + matrixKirillov M P v w
    simp only [LinearMap.add_apply, matrixKirillov, Prod.fst_add, Prod.snd_add,
      Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub]
    ring
  map_smul' := by
    intro c z
    apply LinearMap.ext
    intro w
    simp [matrixKirillov, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub,
      Matrix.trace_smul, smul_add, mul_add]

omit [DecidableEq m] in
theorem fieldKirillovForm_alternating (M : Matrix n n K) (P : Matrix m n K)
    (z : MatrixAlgebraSpace K n m) : fieldKirillovForm M P z z = 0 := by
  change matrixKirillov M P z z = 0
  simp [matrixKirillov]

omit [DecidableEq m] in
theorem fieldKirillovForm_equations (M : Matrix n n K) (P : Matrix m n K)
    (z w : MatrixAlgebraSpace K n m) :
    fieldKirillovForm M P z w =
      Matrix.trace ((M * z.1 - z.1 * M - z.2 * P) * w.1) +
        Matrix.trace ((P * z.1) * w.2) := by
  change matrixKirillov M P z w = _
  have h1 : Matrix.trace (M * (w.1 * z.1)) = Matrix.trace ((z.1 * M) * w.1) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle M w.1 z.1]
  have h2 : Matrix.trace (P * (w.1 * z.2)) = Matrix.trace ((z.2 * P) * w.1) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle P w.1 z.2]
  simp only [matrixKirillov, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]
  rw [h1, h2]
  simp only [Matrix.mul_assoc]
  ring

theorem fieldKirillovForm_ker (M : Matrix n n K) (P : Matrix m n K) :
    LinearMap.ker (fieldKirillovForm M P) = glStabilizerSpace M P := by
  ext z
  constructor
  · intro hz
    have hz' : ∀ w, fieldKirillovForm M P z w = 0 := by
      intro w
      exact congrArg (fun f : MatrixAlgebraSpace K n m →ₗ[K] K => f w) hz
    have hP : P * z.1 = 0 := by
      apply trace_pairing_nondegenerate
      intro W
      simpa [fieldKirillovForm_equations] using hz' (0, W)
    have hM : M * z.1 - z.1 * M - z.2 * P = 0 := by
      apply trace_pairing_nondegenerate
      intro Y
      simpa [fieldKirillovForm_equations] using hz' (Y, 0)
    exact ⟨hP, sub_eq_zero.mp hM⟩
  · rintro ⟨hP, hM⟩
    apply LinearMap.ext
    intro w
    simp [fieldKirillovForm_equations, hP, hM]

def matrixTraceFunctional : MatrixAlgebraSpace K n m →ₗ[K] K :=
  (Matrix.traceLinearMap n K K).comp (LinearMap.fst K (Matrix n n K) (Matrix n m K))

omit [Fintype m] [DecidableEq m] in
theorem matrixTraceFunctional_ne_zero [Nonempty n] :
    (matrixTraceFunctional : MatrixAlgebraSpace K n m →ₗ[K] K) ≠ 0 := by
  intro h
  let i : n := Classical.choice inferInstance
  have hh := congrArg (fun f : MatrixAlgebraSpace K n m →ₗ[K] K =>
    f (Matrix.stdBasisMatrix i i 1, 0)) h
  simp [matrixTraceFunctional] at hh

def fieldSLRadical (M : Matrix n n K) (P : Matrix m n K) :
    Submodule K (MatrixAlgebraSpace K n m) :=
  hyperplaneRadical (fieldKirillovForm M P) matrixTraceFunctional

theorem fieldSLRadical_finrank [Nonempty n]
    (M : Matrix n n K) (P : Matrix m n K)
    (htrace : ∀ z : glStabilizerSpace M P, Matrix.trace z.val.1 = 0) :
    Module.finrank K (fieldSLRadical M P) =
      Module.finrank K (glStabilizerSpace M P) + 1 := by
  have hk : LinearMap.ker (fieldKirillovForm M P) ≤ LinearMap.ker matrixTraceFunctional := by
    rw [fieldKirillovForm_ker]
    intro z hz
    exact htrace ⟨z, hz⟩
  have h := hyperplane_radical_finrank (fieldKirillovForm M P) matrixTraceFunctional
    matrixTraceFunctional_ne_zero (fieldKirillovForm_alternating M P) hk
  rw [fieldKirillovForm_ker M P] at h
  exact h

theorem fieldSLRadical_iff_equations [Nonempty n]
    (M : Matrix n n K) (P : Matrix m n K) (z : MatrixAlgebraSpace K n m) :
    z ∈ fieldSLRadical M P ↔ Matrix.trace z.1 = 0 ∧ P * z.1 = 0 ∧
      ∃ c : K, M * z.1 - z.1 * M = z.2 * P + c • (1 : Matrix n n K) := by
  constructor
  · rintro ⟨ht, hz⟩
    have hP : P * z.1 = 0 := by
      apply trace_pairing_nondegenerate
      intro W
      have h := hz (0, W) (by simp [matrixTraceFunctional])
      simpa [fieldKirillovForm_equations] using h
    have hA : ∀ Y : Matrix n n K, Matrix.trace Y = 0 →
        Matrix.trace ((M * z.1 - z.1 * M - z.2 * P) * Y) = 0 := by
      intro Y hY
      have h := hz (Y, 0) hY
      simpa [fieldKirillovForm_equations] using h
    obtain ⟨c, hc⟩ := (trace_zero_annihilator _).mp hA
    exact ⟨ht, hP, c, (sub_eq_iff_eq_add.mp hc).trans (add_comm _ _)⟩
  · rintro ⟨ht, hP, c, hc⟩
    refine ⟨ht, ?_⟩
    intro w hw
    change Matrix.trace w.1 = 0 at hw
    rw [fieldKirillovForm_equations, hc, add_sub_cancel_left, hP]
    simp [Matrix.smul_mul, Matrix.trace_smul, hw]

theorem exists_gl_sl_radical_witness {r s : Type u} [Fintype r] [Fintype s]
    [Nonempty r] (q : ℕ) :
    ∃ (M : Matrix (blockIndex (r ⊕ s) r (q + 1))
        (blockIndex (r ⊕ s) r (q + 1)) K)
      (P : Matrix (r ⊕ s) (blockIndex (r ⊕ s) r (q + 1)) K),
      Function.Surjective P.mulVec ∧
      Module.finrank K (glStabilizerSpace M P) = Fintype.card r * Fintype.card s ∧
      Module.finrank K (fieldSLRadical M P) = Fintype.card r * Fintype.card s + 1 := by
  classical
  letI : Nonempty (blockIndex (r ⊕ s) r (q + 1)) :=
    inferInstanceAs (Nonempty ((r ⊕ s) ⊕ blockIndex (r ⊕ s) r q))
  obtain ⟨M, P, hP, hd, ht⟩ := exists_gl_stabilizer_witness (K := K) (r := r) (s := s) q
  exact ⟨M, P, hP, hd, (fieldSLRadical_finrank M P ht).trans (congrArg (· + 1) hd)⟩

end FD56
