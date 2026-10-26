/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SLMatrix

/-! A constant coordinate chart for traceless matrices and the translation
coordinates. One diagonal entry is reconstructed from the trace equation. -/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators

def SLChartInput (n m : Type*) (i₀ : n) :=
  {i : SLInput n m // i ≠ Sum.inl (i₀,i₀)}

variable {n m : Type*} [Fintype n] [DecidableEq n] [DecidableEq m]

instance (i₀ : n) [Fintype m] : Fintype (SLChartInput n m i₀) := inferInstanceAs
  (Fintype {i : SLInput n m // i ≠ Sum.inl (i₀,i₀)})

instance (i₀ : n) : DecidableEq (SLChartInput n m i₀) := inferInstanceAs
  (DecidableEq {i : SLInput n m // i ≠ Sum.inl (i₀,i₀)})

variable (R V : Type*) [Ring R] [AddCommGroup V] [Module R V]

def slInputTrace : (SLInput n m → V) →ₗ[R] V where
  toFun v := ∑ i, v (Sum.inl (i,i))
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum]

def slChartZeroExtend (i₀ : n) : (SLChartInput n m i₀ → V) →ₗ[R] (SLInput n m → V) where
  toFun v i := if h : i = Sum.inl (i₀,i₀) then 0 else v ⟨i,h⟩
  map_add' x y := by funext i; by_cases h : i = Sum.inl (i₀,i₀) <;> simp [h]
  map_smul' c v := by funext i; by_cases h : i = Sum.inl (i₀,i₀) <;> simp [h]

def slChartRetract (i₀ : n) : (SLInput n m → V) →ₗ[R] (SLChartInput n m i₀ → V) where
  toFun v i := v i.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def slChartEmbed (i₀ : n) : (SLChartInput n m i₀ → V) →ₗ[R] (SLInput n m → V) :=
  slChartZeroExtend R V i₀ -
    (LinearMap.single R (fun _ : SLInput n m => V) (Sum.inl (i₀,i₀))).comp
      ((slInputTrace R V).comp (slChartZeroExtend R V i₀))

theorem slInputTrace_single (i₀ : n) (v : V) :
    slInputTrace (m := m) R V (Pi.single (Sum.inl (i₀,i₀)) v) = v := by
  simp [slInputTrace, Pi.single_apply, Prod.mk.injEq]

theorem slChartEmbed_trace (i₀ : n) (v : SLChartInput n m i₀ → V) :
    slInputTrace R V (slChartEmbed R V i₀ v) = 0 := by
  simp only [slChartEmbed, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.single_apply, map_sub, slInputTrace_single, sub_self]

theorem slChartRetract_embed (i₀ : n) (v : SLChartInput n m i₀ → V) :
    slChartRetract R V i₀ (slChartEmbed R V i₀ v) = v := by
  funext i
  simp [slChartRetract, slChartEmbed, slChartZeroExtend, i.property, Pi.single_eq_of_ne]

omit [Fintype n] in
theorem slChartZeroExtend_retract (i₀ : n) (v : SLInput n m → V) :
    slChartZeroExtend R V i₀ (slChartRetract R V i₀ v) =
      v - Pi.single (Sum.inl (i₀,i₀)) (v (Sum.inl (i₀,i₀))) := by
  funext i
  by_cases hi : i = Sum.inl (i₀,i₀)
  · subst i
    simp [slChartZeroExtend, slChartRetract]
  · simp [slChartZeroExtend, slChartRetract, hi, Pi.single_eq_of_ne]

theorem slChartEmbed_retract (i₀ : n) (v : SLInput n m → V)
    (hv : slInputTrace R V v = 0) :
    slChartEmbed R V i₀ (slChartRetract R V i₀ v) = v := by
  simp only [slChartEmbed, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.single_apply, slChartZeroExtend_retract, map_sub, slInputTrace_single, hv, zero_sub]
  simp only [Pi.single_neg, sub_neg_eq_add]
  abel

theorem slChartEmbed_injective (i₀ : n) : Function.Injective (slChartEmbed (m := m) R V i₀) :=
  Function.LeftInverse.injective (slChartRetract_embed R V i₀)

variable {R V}

theorem slChartEmbed_map {S W : Type*} [Ring S] [AddCommGroup W] [Module S W]
    (f : V →+ W) (i₀ : n) (v : SLChartInput n m i₀ → V) :
    (fun i => f (slChartEmbed R V i₀ v i)) = slChartEmbed S W i₀ (fun i => f (v i)) := by
  funext i
  simp only [slChartEmbed, slChartZeroExtend, slInputTrace, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.single_apply, Pi.sub_apply, Pi.single_apply,
    map_sub, map_sum]
  by_cases hi : i = Sum.inl (i₀,i₀)
  · simp [hi, apply_ite f, apply_dite f, map_zero]
  · simp [hi, apply_ite f, map_zero]

section Matrix
variable [Fintype m] {R : Type*} [CommRing R]

def slChartEmbeddingMatrix (i₀ : n) : Matrix (SLInput n m) (SLChartInput n m i₀) R :=
  LinearMap.toMatrix' (slChartEmbed R R i₀)

def slChartRetractionMatrix (i₀ : n) : Matrix (SLChartInput n m i₀) (SLInput n m) R :=
  LinearMap.toMatrix' (slChartRetract R R i₀)

theorem slChartEmbeddingMatrix_mulVec (i₀ : n) (v : SLChartInput n m i₀ → R) :
    slChartEmbeddingMatrix i₀ *ᵥ v = slChartEmbed R R i₀ v := by
  exact congrArg (fun f => f v) (Matrix.toLin'_toMatrix' (slChartEmbed R R i₀))

theorem slChartRetractionMatrix_mulVec (i₀ : n) (v : SLInput n m → R) :
    slChartRetractionMatrix i₀ *ᵥ v = slChartRetract R R i₀ v := by
  exact congrArg (fun f => f v) (Matrix.toLin'_toMatrix' (slChartRetract R R i₀))

theorem slChartRetractionMatrix_embedding (i₀ : n) :
    slChartRetractionMatrix (R := R) (m := m) i₀ *
      slChartEmbeddingMatrix (R := R) (m := m) i₀ = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_one,
    LinearMap.id_apply, Matrix.toLin'_apply, slChartEmbeddingMatrix_mulVec,
    slChartRetractionMatrix_mulVec, slChartRetract_embed]

theorem slChartEmbeddingMatrix_map {S : Type*} [CommRing S]
    (f : R →+* S) (i₀ : n) :
    (slChartEmbeddingMatrix (R := R) (m := m) i₀).map f = slChartEmbeddingMatrix i₀ := by
  funext i j
  have h := congrFun (slChartEmbed_map (R := R) (S := S) f.toAddMonoidHom i₀ (Pi.single j 1)) i
  have hR : (fun a : SLChartInput n m i₀ => if a = j then (1 : R) else 0) = Pi.single j 1 := by
    funext a
    simp [Pi.single_apply]
  have hS : (fun a : SLChartInput n m i₀ => if a = j then (1 : S) else 0) = Pi.single j 1 := by
    funext a
    simp [Pi.single_apply]
  have hf : (fun a : SLChartInput n m i₀ =>
      f ((Pi.single j (1 : R) : SLChartInput n m i₀ → R) a)) = Pi.single j (1 : S) := by
    funext a
    simp [Pi.single_apply]
  simp only [slChartEmbeddingMatrix, Matrix.map_apply, LinearMap.toMatrix'_apply, hR, hS]
  change f (slChartEmbed R R i₀ (Pi.single j 1) i) =
    slChartEmbed S S i₀ (fun a => f ((Pi.single j (1 : R) : SLChartInput n m i₀ → R) a)) i at h
  rw [hf] at h
  exact h

theorem slChartInput_card (i₀ : n) :
    Fintype.card (SLChartInput n m i₀) = Fintype.card (SLInput n m) - 1 := by
  change Fintype.card {i : SLInput n m // ¬ i = Sum.inl (i₀,i₀)} = _
  rw [Fintype.card_subtype_compl]
  simp

end Matrix
end FD56
