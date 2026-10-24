/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.BlockHankel

/-! The block matrix and every stacked obstruction use the same independent coefficients. -/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators
variable (K : Type*) [Field K] {b c t : ℕ}

abbrev HankelCoefficientField (b c : ℕ) := FractionRing (MvPolynomial (Fin b × Fin c × ℕ) K)

def universalHankelCoefficients (b c : ℕ) : Fin b → Fin c → ℕ → HankelCoefficientField K b c :=
  fun j i r => algebraMap (MvPolynomial (Fin b × Fin c × ℕ) K) (HankelCoefficientField K b c) (MvPolynomial.X (j,i,r))

theorem universalHankel_inverse (h : Fin b → ℕ) (g : Fin c → ℕ)
    (hs : ∑ j, h j=∑ i, g i) :
    ∃ B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) (HankelCoefficientField K b c),
      B*blockHankel h g (universalHankelCoefficients K b c)=1 ∧
      blockHankel h g (universalHankelCoefficients K b c)*B=1 := by
  obtain ⟨B,hB⟩ := matrix_left_inverse_of_injective _ (genericBlockHankel_injective (K := K) h g hs)
  refine ⟨B,hB,?_⟩
  exact (Matrix.mul_eq_one_comm_of_equiv (blockHankelEquiv h g hs)).mpr hB

def universalHankelStackPolynomial (e : Fin t ≃ Fin b × Fin c) (f : Fin t → ℕ) (N : ℕ) :
    Matrix (Σ l, Fin (f l)) (Fin N) (MvPolynomial (Fin b × Fin c × ℕ) K) :=
  fun lr s => MvPolynomial.X ((e lr.1).1,(e lr.1).2,lr.2.val+s.val)

theorem universalHankelStack_specialization (e : Fin t ≃ Fin b × Fin c)
    (f : Fin t → ℕ) (N : ℕ) (v : Fin t → ℕ → K) :
    (universalHankelStackPolynomial K e f N).map
      (MvPolynomial.eval₂Hom (RingHom.id K) (fun z => v (e.symm (z.1,z.2.1)) z.2.2)) =
      stackedHankel f N v := by
  ext lr s
  simp [universalHankelStackPolynomial,stackedHankel]

theorem universalHankelStack_injective (e : Fin t ≃ Fin b × Fin c)
    (f : Fin t → ℕ) (N : ℕ) (hN : N≤∑ l, f l) :
    Function.Injective ((universalHankelStackPolynomial K e f N).map
      (algebraMap _ (HankelCoefficientField K b c))).mulVec := by
  apply matrix_injective_of_specialization MvPolynomial.C
    (MvPolynomial.eval₂Hom (RingHom.id K)
      (fun z => hankelIntervalCoefficients (K := K) f (e.symm (z.1,z.2.1)) z.2.2))
    (fun k => by simp) _ (IsFractionRing.injective _ _)
  rw [universalHankelStack_specialization]
  exact hankelInterval_injective f N hN

theorem universalHankelStack_surjective (e : Fin t ≃ Fin b × Fin c)
    (f : Fin t → ℕ) (N : ℕ) (hN : (∑ l, f l)≤N) :
    Function.Surjective ((universalHankelStackPolynomial K e f N).map
      (algebraMap _ (HankelCoefficientField K b c))).mulVec := by
  apply matrix_surjective_of_specialization MvPolynomial.C
    (MvPolynomial.eval₂Hom (RingHom.id K)
      (fun z => hankelIntervalCoefficients (K := K) f (e.symm (z.1,z.2.1)) z.2.2))
    (fun k => by simp) _ (IsFractionRing.injective _ _)
  rw [universalHankelStack_specialization]
  exact hankelInterval_surjective f N hN

theorem universalHankelStack_kernel_finrank (e : Fin t ≃ Fin b × Fin c)
    (f : Fin t → ℕ) (N : ℕ) :
    Module.finrank (HankelCoefficientField K b c)
      (LinearMap.ker (Matrix.toLin' ((universalHankelStackPolynomial K e f N).map
        (algebraMap _ (HankelCoefficientField K b c))))) = N-∑ l, f l := by
  by_cases hN : N≤∑ l, f l
  · rw [LinearMap.ker_eq_bot.mpr (universalHankelStack_injective K e f N hN)]
    simp [Nat.sub_eq_zero_of_le hN]
  · have hs := universalHankelStack_surjective K e f N (by omega)
    have hd := (Matrix.toLin' ((universalHankelStackPolynomial K e f N).map
      (algebraMap _ (HankelCoefficientField K b c)))).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hs,finrank_top] at hd
    simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_sigma,Fintype.card_fin] at hd
    omega

end FD56
