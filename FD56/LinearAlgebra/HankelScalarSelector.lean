/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.GenericHankelFamily
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! The last coefficients select the generic stacked Hankel kernel injectively. -/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators
variable {K : Type*} [Field K] {b c t : ℕ}

def hankelTailSelector {K : Type*} [Zero K] [One K] (S N : ℕ) : Matrix (Fin (N-S)) (Fin N) K :=
  fun q s => if S+q.val=s.val then 1 else 0

theorem hankelTailSelector_mulVec (S N : ℕ) (v : Fin N → K) (q : Fin (N-S)) :
    (hankelTailSelector S N *ᵥ v) q=v ⟨S+q.val,by have := q.isLt; omega⟩ := by
  simp only [hankelTailSelector,Matrix.mulVec,dotProduct]
  rw [Finset.sum_eq_single (⟨S+q.val,by have := q.isLt; omega⟩ : Fin N)]
  · simp
  · intro s _ hs
    have he : S+q.val≠s.val := by
      intro he
      apply hs
      exact Fin.ext he.symm
    simp [he]
  · simp

theorem hankelInterval_with_tail_injective (f : Fin t → ℕ) (N : ℕ) :
    Function.Injective (Matrix.fromRows (stackedHankel f N (hankelIntervalCoefficients (K := K) f))
      (hankelTailSelector (∑ l, f l) N)).mulVec := by
  intro x y hxy
  funext s
  by_cases hs : s.val<∑ l, f l
  · let lr := (hankelRowEquiv f).symm ⟨s.val,hs⟩
    have hr : (hankelRowEquiv f lr).val<N := by simpa [lr] using s.isLt
    have he := congrFun hxy (Sum.inl lr)
    change (stackedHankel f N (hankelIntervalCoefficients f) *ᵥ x) lr =
      (stackedHankel f N (hankelIntervalCoefficients f) *ᵥ y) lr at he
    rw [hankelInterval_mulVec f N x lr hr,hankelInterval_mulVec f N y lr hr] at he
    simpa [lr] using he
  · let q : Fin (N-∑ l, f l) := ⟨s.val-(∑ l, f l),by have := s.isLt; omega⟩
    have he := congrFun hxy (Sum.inr q)
    change (hankelTailSelector (∑ l, f l) N *ᵥ x) q =
      (hankelTailSelector (∑ l, f l) N *ᵥ y) q at he
    rw [hankelTailSelector_mulVec,hankelTailSelector_mulVec] at he
    have hq : (∑ l, f l)+q.val=s.val := by dsimp [q]; omega
    simpa only [hq] using he

theorem universalHankelStack_with_tail_injective (e : Fin t ≃ Fin b × Fin c)
    (f : Fin t → ℕ) (N : ℕ) :
    Function.Injective (Matrix.fromRows
      ((universalHankelStackPolynomial K e f N).map (algebraMap _ (HankelCoefficientField K b c)))
      (hankelTailSelector (∑ l, f l) N)).mulVec := by
  let ψ := MvPolynomial.eval₂Hom (RingHom.id K)
    (fun z : Fin b × Fin c × ℕ => hankelIntervalCoefficients (K := K) f (e.symm (z.1,z.2.1)) z.2.2)
  let A := Matrix.fromRows (universalHankelStackPolynomial K e f N)
    (hankelTailSelector (K := MvPolynomial (Fin b × Fin c × ℕ) K) (∑ l, f l) N)
  have hspec : A.map ψ = Matrix.fromRows (stackedHankel f N (hankelIntervalCoefficients f))
      (hankelTailSelector (∑ l, f l) N) := by
    ext w s
    cases w with
    | inl lr => simp [A,ψ,universalHankelStackPolynomial,stackedHankel]
    | inr q => simp [A,hankelTailSelector,apply_ite]
  have hi := matrix_injective_of_specialization MvPolynomial.C ψ
    (fun k => by simp [ψ]) (algebraMap _ (HankelCoefficientField K b c))
    (IsFractionRing.injective _ _) A (hspec ▸ hankelInterval_with_tail_injective f N)
  have he : A.map (algebraMap _ (HankelCoefficientField K b c)) = Matrix.fromRows
      ((universalHankelStackPolynomial K e f N).map (algebraMap _ (HankelCoefficientField K b c)))
      (hankelTailSelector (∑ l, f l) N) := by
    ext w s
    cases w <;> simp [A,hankelTailSelector,apply_ite]
  rwa [he] at hi

end FD56
