/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.NatDotCertificate

/-! A selected square residue certificate proves injectivity of a rectangular matrix. -/

namespace FD56
open Matrix

theorem selected_inverse_of_natListDot {m : Type*} (p n : ℕ)
    (E : Matrix m (Fin n) ℕ) (select : Fin n → m)
    (rows cols : Fin n → List ℕ)
    (hr : ∀ i, (rows i).length=n) (hc : ∀ j, (cols j).length=n)
    (he : ∀ i j, (cols j).getD i.val 0=E (select i) j)
    (hcert : ∀ i j, natListDot (rows i) (cols j)%p=if i=j then 1 else 0) :
    (show Matrix (Fin n) (Fin n) (ZMod p) from
      fun i k => (rows i).getD k.val 0) *
      (E.map (fun a => (a : ZMod p))).submatrix select id=1 := by
  have h := matrix_inverse_of_natListDot p n rows cols hr hc hcert
  have hcols : (show Matrix (Fin n) (Fin n) (ZMod p) from
      fun k j => (cols j).getD k.val 0)=
      (E.map (fun a => (a : ZMod p))).submatrix select id := by
    funext i j
    exact congrArg (fun a : ℕ => (a : ZMod p)) (he i j)
  rwa [hcols] at h

theorem mulVec_injective_of_selected_left_inverse {m n : Type*}
    [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (E : Matrix m n R) (select : n → m) (L : Matrix n n R)
    (hL : L * E.submatrix select id=1) : Function.Injective E.mulVec := by
  intro v w h
  have hs : (E.submatrix select id).mulVec v=(E.submatrix select id).mulVec w := by
    funext i
    exact congrFun h (select i)
  have h' := congrArg L.mulVec hs
  simpa only [Matrix.mulVec_mulVec,hL,Matrix.one_mulVec] using h'

end FD56
