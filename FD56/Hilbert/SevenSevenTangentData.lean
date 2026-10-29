/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.NatDotCertificate

/-! Exact degree-seven columns and a degree-three tangent coefficient test.
Rows use polynomial-row*18+coefficient; columns use variable*4+shift. -/

namespace FD56
open Matrix
set_option Elab.async false

private def uRow0 : List ℤ := [0,0,0,0,0,0,0,1]
private def uRow1 : List ℤ := [0,1,0,0,0,0,0,0]
private def uRow2 : List ℤ := [-1,0,0,0,0,0,0,0]
private def uRow3 : List ℤ := [0,0,0,1,0,0,0,0]
private def uRow4 : List ℤ := [0,0,0,0,0,0,-1,0]
private def uRowTable : List (List ℤ) := [uRow0,uRow1,uRow2,uRow3,uRow4]
def sevenSevenTangentUData (i : Fin 5) : List ℤ := uRowTable.getD i.val []

private def vRow0 : List ℤ := [1,0,0,0,0,0,0,0]
private def vRow1 : List ℤ := [0,0,0,0,0,0,0,-1]
private def vRow2 : List ℤ := [0,0,0,0,0,-1,0,0]
private def vRow3 : List ℤ := [-1,0,0,0,0,0,0,0]
private def vRow4 : List ℤ := [0,0,0,1,0,0,0,0]
private def vRowTable : List (List ℤ) := [vRow0,vRow1,vRow2,vRow3,vRow4]
def sevenSevenTangentVData (i : Fin 5) : List ℤ := vRowTable.getD i.val []

private def inverseRow0 : List ℕ := [100,0,0,0,100,0,0,0,50,51,50,51,100,0,0,0,0,1,51,50,1,100,0,0,0,0,0,0,0,49,51,50,51,100,1,0,0,0,0,51]
private def inverseRow1 : List ℕ := [0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0]
private def inverseRow2 : List ℕ := [49,51,50,51,49,52,49,52,100,1,100,2,49,51,50,51,50,52,52,49,1,100,0,100,1,100,1,100,1,49,52,49,52,100,1,0,0,0,0,50]
private def inverseRow3 : List ℕ := [52,50,51,50,52,49,52,49,1,100,1,100,52,50,51,50,51,49,49,52,100,1,0,0,100,1,100,1,100,52,49,52,49,1,100,0,0,0,0,51]
private def inverseRow4 : List ℕ := [100,1,100,1,100,2,100,1,100,1,100,1,100,1,100,1,100,1,2,100,1,100,0,100,1,100,1,100,1,100,2,100,1,100,1,0,0,0,0,0]
private def inverseRow5 : List ℕ := [52,50,51,50,52,49,52,49,1,100,1,99,52,50,51,50,51,49,49,52,100,1,0,0,100,1,100,1,100,52,49,52,49,1,100,0,0,0,0,51]
private def inverseRow6 : List ℕ := [99,0,0,0,100,0,0,0,50,51,50,51,99,0,0,0,0,1,51,50,1,100,0,0,0,0,0,0,0,49,51,50,51,100,1,0,0,0,0,51]
private def inverseRow7 : List ℕ := [100,0,0,0,0,0,0,0,50,51,50,51,100,0,0,0,0,0,51,50,1,100,0,0,0,0,0,0,0,50,51,50,51,100,1,0,0,0,0,51]
private def inverseRow8 : List ℕ := [51,51,50,51,51,51,50,50,51,50,51,50,51,51,50,51,50,50,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0]
private def inverseRow9 : List ℕ := [0,0,0,0,0,0,0,0,50,51,50,51,0,0,0,0,0,0,51,50,0,0,0,0,0,0,0,0,0,50,51,50,51,0,0,0,0,0,0,50]
private def inverseRow10 : List ℕ := [0,0,0,0,0,0,0,0,50,50,51,50,0,0,0,0,0,0,50,51,0,0,0,0,0,0,0,0,0,50,50,51,50,0,0,0,0,0,0,51]
private def inverseRow11 : List ℕ := [0,0,0,0,0,0,0,0,51,50,50,51,0,0,0,0,0,0,50,50,0,0,0,0,0,0,0,0,0,51,50,50,51,0,0,0,0,0,0,50]
private def inverseRow12 : List ℕ := [0,0,0,0,100,1,100,1,50,51,50,51,0,0,0,0,0,1,51,50,0,0,0,0,0,100,1,100,1,50,51,50,51,0,0,0,0,0,0,50]
private def inverseRow13 : List ℕ := [0,0,0,0,0,100,1,100,51,50,51,50,0,0,0,0,0,0,50,51,0,0,0,0,0,0,100,1,100,51,50,51,50,0,0,0,0,0,0,51]
private def inverseRow14 : List ℕ := [0,0,0,0,0,0,100,1,50,51,50,51,0,0,0,0,0,0,51,50,0,0,0,0,0,0,0,100,1,50,51,50,51,0,0,0,0,0,0,50]
private def inverseRow15 : List ℕ := [50,50,51,50,50,50,51,50,0,0,0,0,50,50,51,50,51,51,50,51,0,0,0,0,0,0,0,0,100,50,50,51,50,0,0,0,0,0,0,51]
private def inverseRow16 : List ℕ := [50,50,51,50,50,50,51,50,0,0,0,0,50,50,51,50,51,51,50,51,0,0,0,0,0,0,0,0,0,50,50,51,50,0,0,0,0,0,0,51]
private def inverseRow17 : List ℕ := [100,0,0,0,100,0,0,0,50,51,50,51,100,0,0,0,0,1,51,50,1,100,0,0,0,0,0,0,0,50,51,50,51,100,1,0,0,0,0,51]
private def inverseRow18 : List ℕ := [0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def inverseRow19 : List ℕ := [50,50,51,50,50,50,50,51,50,51,50,51,50,50,51,50,51,51,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0]
private def inverseRow20 : List ℕ := [99,0,0,0,100,0,0,0,50,51,50,51,100,0,0,0,0,1,51,50,1,100,0,0,0,0,0,0,0,49,51,50,51,100,1,0,0,0,0,51]
private def inverseRow21 : List ℕ := [100,0,0,0,0,0,0,0,50,51,50,51,100,1,0,0,0,0,51,50,1,100,0,0,0,0,0,0,0,50,51,50,51,100,1,0,0,0,0,51]
private def inverseRow22 : List ℕ := [0,0,100,1,100,1,100,1,50,51,50,51,0,0,0,1,100,1,51,50,0,0,0,100,1,100,1,100,1,50,51,50,51,0,0,0,0,0,0,50]
private def inverseRow23 : List ℕ := [0,0,0,100,1,100,1,100,51,50,51,50,0,0,0,0,1,100,50,51,0,0,0,0,100,1,100,1,100,51,50,51,50,0,0,0,0,0,0,51]
private def inverseRow24 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def inverseRow25 : List ℕ := [0,0,0,0,0,0,0,0,51,50,51,51,0,0,0,0,0,0,50,50,0,0,0,0,0,0,0,0,0,51,50,51,51,0,0,0,0,0,0,50]
private def inverseRow26 : List ℕ := [0,0,0,0,0,0,0,0,50,51,50,51,0,0,0,0,0,0,51,50,0,0,0,0,0,0,0,0,0,50,51,50,51,0,0,0,0,0,0,51]
private def inverseRow27 : List ℕ := [2,0,0,0,1,0,0,0,1,100,1,100,2,0,0,0,0,100,100,1,99,1,0,0,0,0,0,0,0,2,100,1,100,2,100,0,0,0,0,100]
private def inverseRow28 : List ℕ := [0,0,100,1,100,1,100,1,50,51,50,51,0,0,100,1,100,1,51,50,0,0,0,100,1,100,1,100,1,50,51,50,51,0,0,0,0,0,0,50]
private def inverseRow29 : List ℕ := [0,0,0,100,1,100,1,100,51,50,51,50,0,0,0,100,1,100,50,51,0,0,0,0,100,1,100,1,100,51,50,51,50,0,0,0,0,0,0,51]
private def inverseRow30 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def inverseRow31 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def inverseRow32 : List ℕ := [0,0,0,0,0,0,0,0,50,51,50,50,0,0,0,0,0,0,51,50,0,0,0,0,0,0,0,0,0,50,51,50,50,0,0,0,0,0,0,51]
private def inverseRow33 : List ℕ := [0,0,0,0,0,0,0,0,51,50,51,50,0,0,0,0,0,0,50,51,100,0,0,0,0,0,0,0,0,51,50,51,50,0,0,0,0,0,0,50]
private def inverseRow34 : List ℕ := [100,0,0,0,0,0,0,0,50,51,50,51,100,0,0,0,0,0,51,50,1,100,0,0,0,0,0,0,0,50,51,50,51,100,0,0,0,0,0,51]
private def inverseRow35 : List ℕ := [1,100,1,100,1,100,1,100,1,100,1,100,1,100,1,100,1,100,100,1,100,1,100,1,100,1,100,1,100,1,100,1,100,1,100,0,0,0,0,0]
private def inverseRow36 : List ℕ := [0,0,0,0,1,100,1,100,51,50,51,50,0,0,0,0,0,100,50,51,0,0,0,0,0,1,100,1,100,51,50,51,50,0,0,100,0,0,0,51]
private def inverseRow37 : List ℕ := [0,0,0,0,0,1,100,1,50,51,50,51,0,0,0,0,0,0,51,50,0,0,0,0,0,0,1,100,1,50,51,50,51,0,0,0,100,0,0,50]
private def inverseRow38 : List ℕ := [0,0,0,0,0,0,1,100,51,50,51,50,0,0,0,0,0,0,49,51,0,0,0,0,0,0,0,1,100,51,50,51,50,0,0,0,0,100,0,51]
private def inverseRow39 : List ℕ := [0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,100,100]
private def inverseRowTable : List (List ℕ) := [inverseRow0,inverseRow1,inverseRow2,inverseRow3,inverseRow4,inverseRow5,inverseRow6,inverseRow7,inverseRow8,inverseRow9,inverseRow10,inverseRow11,inverseRow12,inverseRow13,inverseRow14,inverseRow15,inverseRow16,inverseRow17,inverseRow18,inverseRow19,inverseRow20,inverseRow21,inverseRow22,inverseRow23,inverseRow24,inverseRow25,inverseRow26,inverseRow27,inverseRow28,inverseRow29,inverseRow30,inverseRow31,inverseRow32,inverseRow33,inverseRow34,inverseRow35,inverseRow36,inverseRow37,inverseRow38,inverseRow39]
def sevenSevenTangentInverseRows (i : Fin 40) : List ℕ := inverseRowTable.getD i.val []

private def selectedColumn0 : List ℕ := [1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn1 : List ℕ := [0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0]
private def selectedColumn2 : List ℕ := [0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0]
private def selectedColumn3 : List ℕ := [0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0]
private def selectedColumn4 : List ℕ := [0,1,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0]
private def selectedColumn5 : List ℕ := [0,0,1,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0]
private def selectedColumn6 : List ℕ := [0,0,0,1,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0]
private def selectedColumn7 : List ℕ := [0,0,0,0,1,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,1,0,0,0,0,0]
private def selectedColumn8 : List ℕ := [0,0,0,0,0,0,100,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,0]
private def selectedColumn9 : List ℕ := [0,0,0,0,0,0,0,100,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100]
private def selectedColumn10 : List ℕ := [0,0,0,0,0,0,0,0,100,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn11 : List ℕ := [0,0,0,0,0,0,0,0,0,100,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn12 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,100,0,0,0,0,0,0,0,0,0,100,0,0,0,0]
private def selectedColumn13 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,100,0,0,0,0,0,0,0,0,0,100,0,0,0]
private def selectedColumn14 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,100,0,0,0,0,0,0,0,0,0,100,0,0]
private def selectedColumn15 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,100,0,0,0,0,0,0,0,0,0,100,0]
private def selectedColumn16 : List ℕ := [0,0,0,100,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn17 : List ℕ := [0,0,0,0,100,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn18 : List ℕ := [0,0,0,0,0,100,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0]
private def selectedColumn19 : List ℕ := [0,0,0,0,0,0,100,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0]
private def selectedColumn20 : List ℕ := [100,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn21 : List ℕ := [0,100,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn22 : List ℕ := [0,0,100,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn23 : List ℕ := [0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn24 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0]
private def selectedColumn25 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0]
private def selectedColumn26 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1]
private def selectedColumn27 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0]
private def selectedColumn28 : List ℕ := [0,100,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn29 : List ℕ := [0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn30 : List ℕ := [0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn31 : List ℕ := [0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn32 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0]
private def selectedColumn33 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0]
private def selectedColumn34 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0]
private def selectedColumn35 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn36 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0]
private def selectedColumn37 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0]
private def selectedColumn38 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0]
private def selectedColumn39 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,0]
private def selectedColumnTable : List (List ℕ) := [selectedColumn0,selectedColumn1,selectedColumn2,selectedColumn3,selectedColumn4,selectedColumn5,selectedColumn6,selectedColumn7,selectedColumn8,selectedColumn9,selectedColumn10,selectedColumn11,selectedColumn12,selectedColumn13,selectedColumn14,selectedColumn15,selectedColumn16,selectedColumn17,selectedColumn18,selectedColumn19,selectedColumn20,selectedColumn21,selectedColumn22,selectedColumn23,selectedColumn24,selectedColumn25,selectedColumn26,selectedColumn27,selectedColumn28,selectedColumn29,selectedColumn30,selectedColumn31,selectedColumn32,selectedColumn33,selectedColumn34,selectedColumn35,selectedColumn36,selectedColumn37,selectedColumn38,selectedColumn39]
def sevenSevenTangentSelectedColumns (i : Fin 40) : List ℕ := selectedColumnTable.getD i.val []

def sevenSevenTangentSelectedRows : Fin 40 → Fin 90 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,37,38,39,40,41]

def sevenSevenTangentSelectedData : Matrix (Fin 40) (Fin 40) ℕ :=
  fun i j => (sevenSevenTangentSelectedColumns j).getD i.val 0

def sevenSevenTangentSelected : Matrix (Fin 40) (Fin 40) (ZMod 101) :=
  fun i j => sevenSevenTangentSelectedData i j

end FD56
