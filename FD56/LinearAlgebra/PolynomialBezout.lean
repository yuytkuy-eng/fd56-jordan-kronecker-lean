/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.KernelDescent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! A finite polynomial family with no common zero generates the unit ideal
over an algebraically closed field. This supplies polynomial matrix inverses. -/

namespace FD56
open Polynomial Matrix
open scoped BigOperators

theorem polynomial_span_eq_top_of_no_common_zero {K ι : Type*}
    [Field K] [IsAlgClosed K] (p : ι → K[X])
    (h : ∀ x : K, ∃ i, (p i).eval x ≠ 0) :
    Ideal.span (Set.range p) = ⊤ := by
  classical
  let I : Ideal K[X] := Ideal.span (Set.range p)
  let g := Submodule.IsPrincipal.generator I
  have hdvd (i : ι) : g ∣ p i := by
    exact (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp
      (Ideal.subset_span (Set.mem_range_self i))
  have hdegree : g.degree = 0 := by
    by_contra hn
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root g hn
    obtain ⟨i, hi⟩ := h x
    obtain ⟨f, hf⟩ := hdvd i
    apply hi
    rw [hf, Polynomial.eval_mul, hx, zero_mul]
  have hu : IsUnit g := Polynomial.isUnit_iff_degree_eq_zero.mpr hdegree
  exact Ideal.eq_top_of_isUnit_mem I
    (Submodule.IsPrincipal.generator_mem I) hu

theorem polynomial_bezout_of_no_common_zero {K ι : Type*}
    [Field K] [IsAlgClosed K] [Fintype ι] (p : ι → K[X])
    (h : ∀ x : K, ∃ i, (p i).eval x ≠ 0) :
    ∃ w : ι → K[X], ∑ i, w i * p i = 1 := by
  apply Ideal.mem_span_range_iff_exists_fun.mp
  rw [polynomial_span_eq_top_of_no_common_zero p h]
  trivial

theorem matrix_left_inverse_of_injective {K b k : Type*}
    [Field K] [Fintype b] [Fintype k] [DecidableEq b] [DecidableEq k]
    (Z : Matrix b k K) (h : Function.Injective Z.mulVec) :
    ∃ L : Matrix k b K, L * Z = 1 := by
  obtain ⟨g, hg⟩ := (Matrix.toLin' Z).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr h)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
    LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' hg

/-- Pointwise full column rank over an algebraically closed field supplies
a polynomial left inverse, without assuming a polynomial Bezout certificate. -/
theorem polynomial_left_inverse_of_pointwise_injective {K b k : Type*}
    [Field K] [IsAlgClosed K] [Fintype b] [Fintype k]
    [DecidableEq b] [DecidableEq k] (Z : Matrix b k K[X])
    (h : ∀ x : K, Function.Injective (Z.map (Polynomial.evalRingHom x)).mulVec) :
    ∃ L : Matrix k b K[X], L * Z = 1 := by
  classical
  choose E hE using fun x => matrix_left_inverse_of_injective
    (Z.map (Polynomial.evalRingHom x)) (h x)
  let D : K → Matrix k b K[X] := fun x => (E x).map Polynomial.C
  let p : K → K[X] := fun x => Matrix.det (D x * Z)
  have hp : ∀ x : K, ∃ i, (p i).eval x ≠ 0 := by
    intro x
    refine ⟨x, ?_⟩
    have hd : (D x).map (Polynomial.evalRingHom x) = E x := by
      ext i j
      simp [D]
    change (Polynomial.evalRingHom x) (Matrix.det (D x * Z)) ≠ 0
    rw [RingHom.map_det]
    change Matrix.det ((D x * Z).map (Polynomial.evalRingHom x)) ≠ 0
    rw [Matrix.map_mul, hd, hE x, Matrix.det_one]
    exact one_ne_zero
  have hunit : (1 : K[X]) ∈ Ideal.span (Set.range p) := by
    rw [polynomial_span_eq_top_of_no_common_zero p hp]
    trivial
  obtain ⟨w, hw⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp hunit
  refine ⟨∑ i ∈ w.support, w i • (Matrix.adjugate (D i * Z) * D i), ?_⟩
  rw [Matrix.sum_mul]
  simp_rw [Matrix.smul_mul, Matrix.mul_assoc, Matrix.adjugate_mul, smul_smul]
  rw [← Finset.sum_smul]
  change (w.sum (fun i a => a * p i)) • (1 : Matrix k k K[X]) = 1
  rw [hw, one_smul]

/-- Nullity and a left inverse turn independent kernel columns into a spanning family. -/
theorem matrix_kernel_spanning_of_nullity {F a b k : Type*}
    [Field F] [Fintype a] [Fintype b] [Fintype k]
    [DecidableEq a] [DecidableEq b] [DecidableEq k]
    (A : Matrix a b F) (Z : Matrix b k F) (L : Matrix k b F)
    (hL : L * Z = 1) (hAZ : A * Z = 0)
    (hdim : Module.finrank F (LinearMap.ker (Matrix.toLin' A)) = Fintype.card k)
    (Y : Matrix b Unit F) (hY : A * Y = 0) :
    ∃ c : Matrix k Unit F, Y = Z * c := by
  have hinj : Function.Injective (Matrix.toLin' Z) := by
    intro x y hxy
    have hh := congrArg (fun v => L *ᵥ v) hxy
    simpa only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hL, Matrix.one_mulVec] using hh
  have hle : LinearMap.range (Matrix.toLin' Z) ≤ LinearMap.ker (Matrix.toLin' A) := by
    apply LinearMap.range_le_ker_iff.mpr
    rw [← Matrix.toLin'_mul, hAZ]
    exact map_zero _
  have hdimZ := (Matrix.toLin' Z).finrank_range_add_finrank_ker
  rw [LinearMap.ker_eq_bot.mpr hinj] at hdimZ
  have heq : LinearMap.range (Matrix.toLin' Z) = LinearMap.ker (Matrix.toLin' A) := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    simpa [hdim] using hdimZ
  have hy : (fun i => Y i ()) ∈ LinearMap.ker (Matrix.toLin' A) := by
    change A *ᵥ (fun i => Y i ()) = 0
    ext i
    exact congrArg (fun B => B i ()) hY
  rw [← heq] at hy
  obtain ⟨c, hc⟩ := hy
  refine ⟨fun i _ => c i, ?_⟩
  ext i j
  cases j
  exact (congrArg (fun v => v i) hc).symm

/-- A polynomial kernel basis follows from pointwise full column rank and
the expected nullity over any field containing the polynomial ring. -/
theorem polynomial_kernel_basis_of_pointwise_rank_and_nullity
    {K F a b k : Type*} [Field K] [IsAlgClosed K] [Field F]
    [Fintype a] [Fintype b] [Fintype k]
    [DecidableEq a] [DecidableEq b] [DecidableEq k]
    (φ : K[X] →+* F) (hφ : Function.Injective φ)
    (A : Matrix a b K[X]) (Z : Matrix b k K[X])
    (hAZ : A * Z = 0)
    (hpoint : ∀ x : K, Function.Injective (Z.map (Polynomial.evalRingHom x)).mulVec)
    (hdim : Module.finrank F (LinearMap.ker (Matrix.toLin' (A.map φ))) = Fintype.card k) :
    ∀ Y : Matrix b Unit K[X], A * Y = 0 ↔ ∃! c : Matrix k Unit K[X], Y = Z * c := by
  obtain ⟨L, hL⟩ := polynomial_left_inverse_of_pointwise_injective Z hpoint
  apply kernel_basis_of_left_inverse_and_spanning φ hφ A Z L hL hAZ
  intro Y hY
  refine matrix_kernel_spanning_of_nullity (A.map φ) (Z.map φ) (L.map φ) ?_ ?_ hdim (Y.map φ) ?_
  · simpa using congrArg (fun B => B.map φ) hL
  · simpa using congrArg (fun B => B.map φ) hAZ
  · simpa using congrArg (fun B => B.map φ) hY

end FD56
