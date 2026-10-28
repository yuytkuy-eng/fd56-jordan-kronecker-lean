/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialMatrix

/-! The coprime Plucker chart is reconstructed by a finite linear system.
The first four polynomials and one leading coefficient determine the last
two polynomials uniquely, and every such choice has a solution. -/

noncomputable section
namespace FD56
open Polynomial

variable {K : Type*} [Field K]

def pluckerChartReconstructionMap (W : ℕ) (f g : K[X])
    (hf : f.natDegree≤W) (hg : g.natDegree≤W) :
    (BoundedPoly K W × BoundedPoly K W) →ₗ[K] (BoundedPoly K (2*W) × K) where
  toFun z := (boundedPolyOf (f*z.2.val-g*z.1.val) (by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · exact Polynomial.natDegree_mul_le.trans (by have := boundedPoly_degree W z.2; omega)
    · exact Polynomial.natDegree_mul_le.trans (by have := boundedPoly_degree W z.1; omega)),
    z.1.val.coeff W)
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [Prod.fst_add,Prod.snd_add,Submodule.coe_add]
      dsimp [boundedPolyOf]
      ring
    · exact Polynomial.coeff_add _ _ _
  map_smul' c x := by
    apply Prod.ext
    · apply Subtype.ext
      change f*(c • x.2.val)-g*(c • x.1.val)=c • (f*x.2.val-g*x.1.val)
      simp only [Polynomial.smul_eq_C_mul]
      ring
    · exact Polynomial.coeff_smul _ _ _

theorem pluckerChartReconstructionMap_injective (W : ℕ) (f g : K[X])
    (hf : f.natDegree≤W) (hg : g.natDegree≤W)
    (hf0 : f≠0) (hdegree : f.natDegree=W) (hcoprime : IsCoprime f g) :
    Function.Injective (pluckerChartReconstructionMap W f g hf hg) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  rintro ⟨p,q⟩ h
  have hrel : f*q.val=g*p.val := by
    have hh := congrArg (fun z : BoundedPoly K (2*W) × K => z.1.val) h
    exact sub_eq_zero.mp hh
  have hcoeff : p.val.coeff W=0 := congrArg Prod.snd h
  have hdvd : f∣p.val := hcoprime.dvd_of_dvd_mul_left ⟨q.val,hrel.symm⟩
  have hp : p.val=0 := by
    by_contra hn
    have hge : W≤p.val.natDegree := by
      have hle := Polynomial.natDegree_le_of_dvd hdvd hn
      simpa only [hdegree] using hle
    have heq : p.val.natDegree=W := Nat.le_antisymm (boundedPoly_degree W p) hge
    have hlead : p.val.leadingCoeff=0 := by
      simpa only [Polynomial.leadingCoeff,heq] using hcoeff
    exact (Polynomial.leadingCoeff_ne_zero.mpr hn) hlead
  have hq : q.val=0 := by
    rw [hp,mul_zero] at hrel
    exact (mul_eq_zero.mp hrel).resolve_left hf0
  exact Prod.ext (Subtype.ext hp) (Subtype.ext hq)

theorem pluckerChartReconstructionMap_bijective (W : ℕ) (f g : K[X])
    (hf : f.natDegree≤W) (hg : g.natDegree≤W)
    (hf0 : f≠0) (hdegree : f.natDegree=W) (hcoprime : IsCoprime f g) :
    Function.Bijective (pluckerChartReconstructionMap W f g hf hg) := by
  have hi := pluckerChartReconstructionMap_injective W f g hf hg hf0 hdegree hcoprime
  refine ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hi⟩
  simp only [Module.finrank_prod,boundedPoly_finrank,Module.finrank_self]
  omega

theorem exists_unique_pluckerChartCompletion (W : ℕ) (f g a b : K[X]) (c : K)
    (hf : f.natDegree≤W) (hg : g.natDegree≤W)
    (ha : a.natDegree≤W) (hb : b.natDegree≤W)
    (hf0 : f≠0) (hdegree : f.natDegree=W) (hcoprime : IsCoprime f g) :
    ∃! z : BoundedPoly K W × BoundedPoly K W,
      f*z.2.val-g*z.1.val+a*b=0 ∧ z.1.val.coeff W=c := by
  let v : BoundedPoly K (2*W) × K :=
    (boundedPolyOf (-(a*b)) (by
      rw [Polynomial.natDegree_neg]
      exact Polynomial.natDegree_mul_le.trans (by omega)),c)
  obtain ⟨z,hz⟩ := (pluckerChartReconstructionMap_bijective W f g hf hg hf0 hdegree hcoprime).2 v
  have hrel : f*z.2.val-g*z.1.val=-(a*b) :=
    congrArg (fun x : BoundedPoly K (2*W) × K => x.1.val) hz
  have hc : z.1.val.coeff W=c := congrArg Prod.snd hz
  refine ⟨z,⟨by rw [hrel]; ring,hc⟩,?_⟩
  intro y hy
  apply pluckerChartReconstructionMap_injective W f g hf hg hf0 hdegree hcoprime
  rw [hz]
  apply Prod.ext
  · apply Subtype.ext
    exact eq_neg_of_add_eq_zero_left hy.1
  · exact hy.2

end FD56
