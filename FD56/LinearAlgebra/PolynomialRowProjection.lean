/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialRowAvoidance

/-! Constant projections of a split two-column polynomial matrix. Finite
avoidance over an infinite field supplies a primitive projected row. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

private theorem affine_line_submodule_parameters_subsingleton
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (S : Submodule K V) (v w : V) (h : v∉S ∨ w∉S) :
    {t : K | v+t•w∈S}.Subsingleton := by
  intro t ht u hu
  by_contra htu
  have hdiff : (t-u)•w∈S := by
    convert S.sub_mem ht hu using 1
    simp [sub_smul]
  have hw : w∈S := by
    have hscaled := S.smul_mem ((t-u)⁻¹) hdiff
    simpa only [smul_smul,inv_mul_cancel₀ (sub_ne_zero.mpr htu),one_smul] using hscaled
  have hv : v∈S := by
    simpa only [add_sub_cancel_right] using S.sub_mem ht (S.smul_mem t hw)
  exact h.elim (fun hn => hn hv) (fun hn => hn hw)

theorem exists_avoiding_finite_submodules
    {K V : Type*} [Field K] [Infinite K] [AddCommGroup V] [Module K V]
    (s : Finset (Submodule K V)) (hs : ∀ S∈s, S≠⊤) :
    ∃ v : V, ∀ S∈s, v∉S := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0,by simp⟩
  | @insert S s hS ih =>
    obtain ⟨v,hv⟩ := ih (fun T hT => hs T (Finset.mem_insert_of_mem hT))
    obtain ⟨w,hw⟩ : ∃ w : V, w∉S := by
      by_contra! h
      apply hs S (Finset.mem_insert_self _ _)
      exact top_unique (fun x _ => h x)
    let bad (T : Submodule K V) : Set K := {t | v+t•w∈T}
    have hfinite : (⋃ T∈((insert S s : Finset (Submodule K V)) : Set (Submodule K V)), bad T).Finite := by
      apply (insert S s).finite_toSet.biUnion
      intro T hT
      apply (affine_line_submodule_parameters_subsingleton T v w ?_).finite
      rcases Finset.mem_insert.mp hT with rfl | hT
      · exact Or.inr hw
      · exact Or.inl (hv T hT)
    obtain ⟨t,ht⟩ := hfinite.exists_not_mem
    refine ⟨v+t•w,?_⟩
    intro T hT hmem
    apply ht
    exact Set.mem_iUnion.mpr ⟨T,Set.mem_iUnion.mpr ⟨hT,hmem⟩⟩

variable {K m : Type*} [Field K] [Fintype m]

private def constantRowEntry (G : Matrix m (Fin 2) K[X]) (j : Fin 2) :
    (m → K) →ₗ[K] K[X] where
  toFun u := ∑ i, u i • G i j
  map_add' u v := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' c u := by simp [smul_smul,Finset.smul_sum]

private theorem constantRowEntry_single [DecidableEq m] (G : Matrix m (Fin 2) K[X])
    (i : m) (j : Fin 2) : constantRowEntry G j (Pi.single i 1)=G i j := by
  classical
  simp [constantRowEntry,Pi.single_apply]

private def rowDivisibilitySubmodule (G : Matrix m (Fin 2) K[X]) (p : K[X]) :
    Submodule K (m → K) :=
  ((Ideal.span ({p} : Set K[X])).restrictScalars K).comap (constantRowEntry G 0)

private theorem rowDivisibility_mem (G : Matrix m (Fin 2) K[X]) (p : K[X]) (u : m → K) :
    u∈rowDivisibilitySubmodule G p ↔ p∣constantRowEntry G 0 u := by
  exact Ideal.mem_span_singleton

private theorem rowDivisibility_ne_top (G : Matrix m (Fin 2) K[X])
    (L : Matrix (Fin 2) m K[X]) (hLG : L*G=1) (p : K[X]) (hp : ¬IsUnit p) :
    rowDivisibilitySubmodule G p≠⊤ := by
  classical
  intro he
  have hrows (i : m) : p∣G i 0 := by
    have hmem : Pi.single i (1:K)∈rowDivisibilitySubmodule G p := by rw [he]; trivial
    simpa only [constantRowEntry_single] using (rowDivisibility_mem G p _).mp hmem
  have hdvd : p∣(L*G) 0 0 := by
    exact Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_right (hrows i) (L 0 i))
  rw [hLG,Matrix.one_apply_eq] at hdvd
  exact hp (isUnit_of_dvd_one hdvd)

theorem exists_coprime_constant_row_projection [Infinite K]
    (G : Matrix m (Fin 2) K[X]) (L : Matrix (Fin 2) m K[X]) (hLG : L*G=1) :
    ∃ u : m → K, IsCoprime (∑ i, C (u i)*G i 0) (∑ i, C (u i)*G i 1) := by
  classical
  obtain ⟨i₀,hi₀⟩ : ∃ i : m, G i 0≠0 := by
    by_contra! hz
    have h := congrFun (congrFun hLG 0) 0
    simp [Matrix.mul_apply,hz] at h
  let f₀ := G i₀ 0
  let f₁ := G i₀ 1
  let wedge : (m → K) →ₗ[K] K[X] :=
    (LinearMap.mulLeft K f₀).comp (constantRowEntry G 1)-
      (LinearMap.mulLeft K f₁).comp (constantRowEntry G 0)
  have hwedge : LinearMap.ker wedge≠⊤ := by
    intro he
    have hz (i : m) : f₀*G i 1-f₁*G i 0=0 := by
      have hmem : Pi.single i (1:K)∈LinearMap.ker wedge := by rw [he]; trivial
      change f₀*constantRowEntry G 1 (Pi.single i 1)-
        f₁*constantRowEntry G 0 (Pi.single i 1)=0 at hmem
      simpa only [constantRowEntry_single] using hmem
    apply hi₀
    change f₀=0
    calc
      f₀=f₀*(L*G) 1 1-f₁*(L*G) 1 0 := by simp [hLG]
      _=∑ i, L 1 i*(f₀*G i 1-f₁*G i 0) := by
        simp only [Matrix.mul_apply,Finset.mul_sum,← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _=0 := by simp [hz]
  let factors := (UniqueFactorizationMonoid.normalizedFactors f₀).toFinset
  let forbidden := insert (LinearMap.ker wedge) (factors.image (rowDivisibilitySubmodule G))
  obtain ⟨v,hv⟩ := exists_avoiding_finite_submodules forbidden (by
    intro S hS
    rcases Finset.mem_insert.mp hS with rfl | hS
    · exact hwedge
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hS
      exact rowDivisibility_ne_top G L hLG p
        (UniqueFactorizationMonoid.irreducible_of_normalized_factor p
          (Multiset.mem_toFinset.mp hp)).not_isUnit)
  let g₀ := constantRowEntry G 0 v
  let g₁ := constantRowEntry G 1 v
  have hdet : f₀*g₁-f₁*g₀≠0 := by
    exact hv (LinearMap.ker wedge) (Finset.mem_insert_self _ _)
  have hfg : IsCoprime f₀ g₀ := by
    apply isCoprime_of_irreducible_dvd (fun h => hi₀ h.1)
    intro p hp hpf hpg
    obtain ⟨d,hd,hpd⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd
      hi₀ hp hpf
    apply hv (rowDivisibilitySubmodule G d)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d,Multiset.mem_toFinset.mpr hd,rfl⟩))
    exact (rowDivisibility_mem G d v).mpr (hpd.dvd_iff_dvd_left.mp hpg)
  obtain ⟨t,ht⟩ := exists_coprime_constant_row_combination f₀ f₁ g₀ g₁ hdet
    (fun d hd₀ _ hd₁ _ => hfg.isUnit_of_dvd' hd₀ hd₁)
  refine ⟨Pi.single i₀ 1+t•v,?_⟩
  have hresult : IsCoprime
      (constantRowEntry G 0 (Pi.single i₀ 1+t•v))
      (constantRowEntry G 1 (Pi.single i₀ 1+t•v)) := by
    simpa only [map_add,map_smul,constantRowEntry_single,Polynomial.smul_eq_C_mul] using ht
  simpa only [constantRowEntry,LinearMap.coe_mk,AddHom.coe_mk,Polynomial.smul_eq_C_mul] using hresult

end FD56
