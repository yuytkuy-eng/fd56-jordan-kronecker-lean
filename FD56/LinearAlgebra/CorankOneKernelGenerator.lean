/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.RectangularMinorDivisors
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Fin.Basic

/-! A primitive left-kernel generator with a prescribed row-deletion coordinate. -/

noncomputable section
namespace FD56
open Matrix

variable {R a n : Type*} [CommRing R] [IsPrincipalIdealRing R]
  [Fintype a] [Fintype n] [DecidableEq n]

theorem corank_one_kernel_generator (A : Matrix a n R) (j : a)
    (e : n ≃ {i : a // i ≠ j})
    (hp : ∀ d : R, (∀ r : n → a, d ∣ (A.submatrix r id).det) → IsUnit d) :
    ∃ c : a → R,
      c j = (A.submatrix (fun x => (e x).val) id).det ∧
      A.transpose *ᵥ c = 0 ∧
      ∀ y : a → R, A.transpose *ᵥ y = 0 ↔ ∃! h : R, y = h • c := by
  classical
  let ε : Fin (Fintype.card n) ≃ n := (Fintype.equivFin n).symm
  let ρ : Fin (Fintype.card n + 1) ≃ a :=
    (finSuccEquiv (Fintype.card n)).trans
      ((Equiv.optionCongr (ε.trans e)).trans (Equiv.optionSubtypeNe j))
  have hρ0 : ρ 0 = j := by simp [ρ]
  have hρs (i : Fin (Fintype.card n)) : ρ i.succ = (e (ε i)).val := by simp [ρ]
  have hρj : ρ.symm j = 0 := by apply ρ.injective; simp [hρ0]
  let B : Matrix (Fin (Fintype.card n + 1)) (Fin (Fintype.card n)) R :=
    A.submatrix ρ ε
  have hB : ∀ d : R,
      (∀ r : Fin (Fintype.card n) → Fin (Fintype.card n + 1),
        d ∣ (B.submatrix r id).det) → IsUnit d := by
    intro d hd
    apply hp d
    intro r
    have heq : B.submatrix (fun x => ρ.symm (r (ε x))) id =
        (A.submatrix r id).submatrix ε ε := by
      ext x y
      simp [B]
    have h := hd (fun x => ρ.symm (r (ε x)))
    rw [heq, Matrix.det_submatrix_equiv_self] at h
    exact h
  let c : a → R := rectangularCofactors B ∘ ρ.symm
  have hcρ : c ∘ ρ = rectangularCofactors B := by funext i; simp [c]
  have hker (y : a → R) :
      B.transpose *ᵥ (y ∘ ρ) = 0 ↔ A.transpose *ᵥ y = 0 := by
    have heq : B.transpose *ᵥ (y ∘ ρ) = (A.transpose *ᵥ y) ∘ ε := by
      change (A.transpose.submatrix ε ρ) *ᵥ (y ∘ ρ) = _
      simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using
        Matrix.submatrix_mulVec_equiv A.transpose (y ∘ ρ) ε ρ
    rw [heq]
    constructor
    · intro h
      funext x
      obtain ⟨i, rfl⟩ := ε.surjective x
      exact congrFun h i
    · intro h
      rw [h]
      rfl
  have hcrel : A.transpose *ᵥ c = 0 := by
    apply (hker c).mp
    rw [hcρ]
    exact rectangularCofactors_relation B
  refine ⟨c, ?_, hcrel, ?_⟩
  · have heq : B.submatrix Fin.succ id =
        (A.submatrix (fun x => (e x).val) id).submatrix ε ε := by
      ext x y
      change A (ρ x.succ) (ε y) = A (e (ε x)).val (ε y)
      rw [hρs]
    change rectangularCofactors B (ρ.symm j) = _
    rw [hρj]
    simp only [rectangularCofactors, Fin.val_zero, pow_zero, one_mul,
      Fin.succAbove_zero, heq, Matrix.det_submatrix_equiv_self]
  · intro y
    constructor
    · intro hy
      obtain ⟨h, hh, hu⟩ :=
        (rectangularCofactors_kernel_iff_unique_of_maximal_minors_units B hB (y ∘ ρ)).mp
          ((hker y).mpr hy)
      refine ⟨h, ?_, ?_⟩
      · funext i
        simpa [c, Function.comp_def] using congrFun hh (ρ.symm i)
      · intro k hk
        apply hu k
        funext i
        simpa [c, Function.comp_def] using congrFun hk (ρ i)
    · rintro ⟨h, rfl, _⟩
      rw [Matrix.mulVec_smul, hcrel, smul_zero]

end FD56
