/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.RankSpecialization
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Stacked Hankel matrices with independent coefficients have maximal rank.
The specialization places one nonzero coefficient in each block, assigning
successive disjoint intervals of columns to the reversed rows of that block. -/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators

variable {K : Type*} [Field K] {b : ℕ}

def stackedHankel (h : Fin b → ℕ) (N : ℕ) (c : Fin b → ℕ → K) :
    Matrix (Σ i, Fin (h i)) (Fin N) K := fun i j => c i.1 (i.2.val+j.val)

def hankelRowEquiv (h : Fin b → ℕ) : (Σ i, Fin (h i)) ≃ Fin (∑ i, h i) :=
  (Equiv.sigmaCongrRight (fun i => Fin.revPerm)).trans finSigmaFinEquiv

def hankelBlockOffset (h : Fin b → ℕ) (i : Fin b) : ℕ :=
  ∑ j : Fin i.val, h (Fin.castLE i.isLt.le j)

theorem hankelRowEquiv_val (h : Fin b → ℕ) (i : Σ j, Fin (h j)) :
    (hankelRowEquiv h i).val = hankelBlockOffset h i.1 + (h i.1 - 1 - i.2.val) := by
  simp only [hankelRowEquiv, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
    finSigmaFinEquiv_apply, hankelBlockOffset]
  simp only [Fin.revPerm_apply, Fin.val_rev]
  omega

def hankelIntervalCoefficients (h : Fin b → ℕ) : Fin b → ℕ → K :=
  fun i k => if k = hankelBlockOffset h i + (h i - 1) then 1 else 0

theorem hankelInterval_entry (h : Fin b → ℕ) (N : ℕ)
    (i : Σ j, Fin (h j)) (j : Fin N) :
    stackedHankel h N (hankelIntervalCoefficients (K := K) h) i j =
      if (hankelRowEquiv h i).val = j.val then 1 else 0 := by
  have hi := i.2.isLt
  have he : i.2.val+j.val = hankelBlockOffset h i.1+(h i.1-1) ↔
      (hankelRowEquiv h i).val=j.val := by
    rw [hankelRowEquiv_val]
    omega
  simp only [stackedHankel, hankelIntervalCoefficients, he]

theorem hankelInterval_mulVec (h : Fin b → ℕ) (N : ℕ)
    (x : Fin N → K) (i : Σ j, Fin (h j))
    (hi : (hankelRowEquiv h i).val < N) :
    (stackedHankel h N (hankelIntervalCoefficients (K := K) h) *ᵥ x) i =
      x ⟨(hankelRowEquiv h i).val,hi⟩ := by
  simp only [Matrix.mulVec, dotProduct, hankelInterval_entry]
  rw [Finset.sum_eq_single (⟨(hankelRowEquiv h i).val,hi⟩ : Fin N)]
  · simp
  · intro j _ hj
    have hne : (hankelRowEquiv h i).val ≠ j.val := by
      intro hh
      apply hj
      exact Fin.ext hh.symm
    simp [hne]
  · simp

theorem hankelInterval_injective (h : Fin b → ℕ) (N : ℕ)
    (hN : N ≤ ∑ i, h i) :
    Function.Injective (stackedHankel h N (hankelIntervalCoefficients (K := K) h)).mulVec := by
  intro x y hxy
  funext j
  let i := (hankelRowEquiv h).symm (Fin.castLE hN j)
  have hi : (hankelRowEquiv h i).val < N := by simpa [i] using j.isLt
  have hh := congrFun hxy i
  rw [hankelInterval_mulVec h N x i hi, hankelInterval_mulVec h N y i hi] at hh
  simpa [i] using hh

theorem hankelInterval_surjective (h : Fin b → ℕ) (N : ℕ)
    (hN : (∑ i, h i) ≤ N) :
    Function.Surjective (stackedHankel h N (hankelIntervalCoefficients (K := K) h)).mulVec := by
  intro y
  let x : Fin N → K := fun j => if hj : j.val < ∑ i, h i then
    y ((hankelRowEquiv h).symm ⟨j.val,hj⟩) else 0
  refine ⟨x, ?_⟩
  funext i
  have hi : (hankelRowEquiv h i).val < N := lt_of_lt_of_le (hankelRowEquiv h i).isLt hN
  rw [hankelInterval_mulVec h N x i hi]
  simp [x, (hankelRowEquiv h i).isLt]

def genericStackedHankel (h : Fin b → ℕ) (N : ℕ) :
    Matrix (Σ i, Fin (h i)) (Fin N) (MvPolynomial (Fin b × ℕ) K) :=
  fun i j => MvPolynomial.X (i.1,i.2.val+j.val)

theorem genericStackedHankel_specialization (h : Fin b → ℕ) (N : ℕ)
    (c : Fin b → ℕ → K) :
    (genericStackedHankel (K := K) h N).map
      (MvPolynomial.eval₂Hom (RingHom.id K) (fun z => c z.1 z.2)) =
      stackedHankel h N c := by
  ext i j
  simp [genericStackedHankel, stackedHankel]

theorem genericStackedHankel_injective (h : Fin b → ℕ) (N : ℕ)
    (hN : N ≤ ∑ i, h i) :
    Function.Injective ((genericStackedHankel (K := K) h N).map
      (algebraMap _ (FractionRing (MvPolynomial (Fin b × ℕ) K)))).mulVec := by
  apply matrix_injective_of_specialization MvPolynomial.C
    (MvPolynomial.eval₂Hom (RingHom.id K)
      (fun z => hankelIntervalCoefficients (K := K) h z.1 z.2))
    (fun c => by simp) _ (IsFractionRing.injective _ _)
  rw [genericStackedHankel_specialization]
  exact hankelInterval_injective h N hN

theorem genericStackedHankel_surjective (h : Fin b → ℕ) (N : ℕ)
    (hN : (∑ i, h i) ≤ N) :
    Function.Surjective ((genericStackedHankel (K := K) h N).map
      (algebraMap _ (FractionRing (MvPolynomial (Fin b × ℕ) K)))).mulVec := by
  apply matrix_surjective_of_specialization MvPolynomial.C
    (MvPolynomial.eval₂Hom (RingHom.id K)
      (fun z => hankelIntervalCoefficients (K := K) h z.1 z.2))
    (fun c => by simp) _ (IsFractionRing.injective _ _)
  rw [genericStackedHankel_specialization]
  exact hankelInterval_surjective h N hN

theorem genericStackedHankel_kernel_finrank (h : Fin b → ℕ) (N : ℕ) :
    Module.finrank (FractionRing (MvPolynomial (Fin b × ℕ) K))
      (LinearMap.ker (Matrix.toLin' ((genericStackedHankel (K := K) h N).map
        (algebraMap _ (FractionRing (MvPolynomial (Fin b × ℕ) K)))))) =
      N - ∑ i, h i := by
  by_cases hN : N ≤ ∑ i, h i
  · rw [LinearMap.ker_eq_bot.mpr (genericStackedHankel_injective h N hN)]
    simp [Nat.sub_eq_zero_of_le hN]
  · have hs := genericStackedHankel_surjective (K := K) h N (by omega)
    have hd := (Matrix.toLin' ((genericStackedHankel (K := K) h N).map
      (algebraMap _ (FractionRing (MvPolynomial (Fin b × ℕ) K))))).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hs, finrank_top] at hd
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sigma,
      Fintype.card_fin] at hd
    omega

end FD56
