/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ScalarCrossVanishing
import Mathlib.RingTheory.Coprime.Basic

/-! A coprime linear functional on one scalar lift forces divisibility of every scalar image. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem scalar_solution_dvd_of_coprime_functional
    {R V W : Type*} [CommRing R] [AddCommGroup V] [AddCommGroup W]
    [Module R V] [Module R W]
    (A : V →ₗ[R] W) (hA : Function.Injective A) (ℓ : V →ₗ[R] R)
    (w : W) (Z : V) (p q : R) (hZ : A Z = p • w) (hℓ : ℓ Z = q)
    (hcp : IsCoprime p q) (z : V) (f : R) (hz : A z = f • w) : p ∣ f := by
  have hc : p • z = f • Z := by
    apply hA
    simp only [map_smul,hz,hZ,smul_smul,mul_comm]
  have hh : p * ℓ z = f * q := by
    simpa only [map_smul,smul_eq_mul,hℓ] using congrArg ℓ hc
  exact hcp.dvd_of_dvd_mul_right ⟨ℓ z,hh.symm⟩

theorem polynomial_scalar_solution_zero_of_degree
    {K V W : Type*} [Field K] [AddCommGroup V] [AddCommGroup W]
    [Module K[X] V] [Module K[X] W]
    (A : V →ₗ[K[X]] W) (hA : Function.Injective A) (ℓ : V →ₗ[K[X]] K[X])
    (w : W) (Z : V) (p q : K[X]) (hZ : A Z = p • w) (hℓ : ℓ Z = q)
    (hcp : IsCoprime p q) (z : V) (f : K[X]) (hz : A z = f • w)
    (hdegree : f.natDegree < p.natDegree) : z = 0 := by
  have hdvd := scalar_solution_dvd_of_coprime_functional A hA ℓ w Z p q hZ hℓ hcp z f hz
  have hf : f = 0 := by
    by_contra hne
    exact (not_le_of_gt hdegree) (Polynomial.natDegree_le_of_dvd hdvd hne)
  apply hA
  simpa only [hf,zero_smul,map_zero] using hz

end FD56
