/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.StackedHankel

/-! Square block Hankel matrices have an explicit permutation specialization. -/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators

variable {K : Type*} [Field K] {b c : ℕ}

def blockHankel (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K) :
    Matrix (Σ i, Fin (h i)) (Σ j, Fin (g j)) K :=
  fun i j => a i.1 j.1 (i.2.val+j.2.val)

def blockHankelCoefficients (h : Fin b → ℕ) (g : Fin c → ℕ) :
    Fin b → Fin c → ℕ → K :=
  fun i j k => if hankelBlockOffset h i+k = hankelBlockOffset g j+(g j-1)
    then 1 else 0

def blockHankelEquiv (h : Fin b → ℕ) (g : Fin c → ℕ)
    (hs : (∑ i, h i) = ∑ j, g j) : (Σ i, Fin (h i)) ≃ (Σ j, Fin (g j)) :=
  finSigmaFinEquiv.trans ((finCongr hs).trans (hankelRowEquiv g).symm)

theorem blockHankelEquiv_val (h : Fin b → ℕ) (g : Fin c → ℕ)
    (hs : (∑ i, h i) = ∑ j, g j) (i : Σ j, Fin (h j)) :
    (hankelRowEquiv g (blockHankelEquiv h g hs i)).val =
      hankelBlockOffset h i.1+i.2.val := by
  simp [blockHankelEquiv, finSigmaFinEquiv_apply, hankelBlockOffset]

theorem blockHankel_interval_entry (h : Fin b → ℕ) (g : Fin c → ℕ)
    (hs : (∑ i, h i) = ∑ j, g j)
    (i : Σ j, Fin (h j)) (j : Σ k, Fin (g k)) :
    blockHankel h g (blockHankelCoefficients (K := K) h g) i j =
      if blockHankelEquiv h g hs i=j then 1 else 0 := by
  have he : blockHankelEquiv h g hs i=j ↔
      hankelBlockOffset h i.1+i.2.val =
        hankelBlockOffset g j.1+(g j.1-1-j.2.val) := by
    rw [← (hankelRowEquiv g).injective.eq_iff, ← Fin.val_inj,
      blockHankelEquiv_val, hankelRowEquiv_val]
  have hj := j.2.isLt
  have hc : hankelBlockOffset h i.1+(i.2.val+j.2.val) =
      hankelBlockOffset g j.1+(g j.1-1) ↔ blockHankelEquiv h g hs i=j := by
    rw [he]
    omega
  simp only [blockHankel, blockHankelCoefficients, hc]

theorem blockHankel_interval_mulVec (h : Fin b → ℕ) (g : Fin c → ℕ)
    (hs : (∑ i, h i) = ∑ j, g j)
    (x : (Σ j, Fin (g j)) → K) (i : Σ j, Fin (h j)) :
    (blockHankel h g (blockHankelCoefficients (K := K) h g) *ᵥ x) i =
      x (blockHankelEquiv h g hs i) := by
  simp [Matrix.mulVec, dotProduct, blockHankel_interval_entry h g hs]

theorem blockHankel_interval_injective (h : Fin b → ℕ) (g : Fin c → ℕ)
    (hs : (∑ i, h i) = ∑ j, g j) :
    Function.Injective (blockHankel h g (blockHankelCoefficients (K := K) h g)).mulVec := by
  intro x y hxy
  funext j
  have hh := congrFun hxy ((blockHankelEquiv h g hs).symm j)
  simpa only [blockHankel_interval_mulVec h g hs, Equiv.apply_symm_apply] using hh

def genericBlockHankel (h : Fin b → ℕ) (g : Fin c → ℕ) :
    Matrix (Σ i, Fin (h i)) (Σ j, Fin (g j)) (MvPolynomial (Fin b × Fin c × ℕ) K) :=
  fun i j => MvPolynomial.X (i.1,j.1,i.2.val+j.2.val)

theorem genericBlockHankel_injective (h : Fin b → ℕ) (g : Fin c → ℕ)
    (hs : (∑ i, h i) = ∑ j, g j) :
    Function.Injective ((genericBlockHankel (K := K) h g).map
      (algebraMap _ (FractionRing (MvPolynomial (Fin b × Fin c × ℕ) K)))).mulVec := by
  apply matrix_injective_of_specialization MvPolynomial.C
    (MvPolynomial.eval₂Hom (RingHom.id K)
      (fun z => blockHankelCoefficients (K := K) h g z.1 z.2.1 z.2.2))
    (fun k => by simp) _ (IsFractionRing.injective _ _)
  have he : (genericBlockHankel (K := K) h g).map
      (MvPolynomial.eval₂Hom (RingHom.id K)
        (fun z => blockHankelCoefficients (K := K) h g z.1 z.2.1 z.2.2)) =
      blockHankel h g (blockHankelCoefficients (K := K) h g) := by
    ext i j
    simp [genericBlockHankel, blockHankel]
  rw [he]
  exact blockHankel_interval_injective h g hs

end FD56
