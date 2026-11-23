import MOC.ThreeSharedRepeatedFiveData

/-! Impose coefficient evaluation 27 in cut 20. -/

open MOC.IntegerRayCut

namespace MOC.ThreeSharedRepeatedFive.Cut20

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage19.count := ⟨by decide +kernel⟩
local instance : NeZero stage20.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 0, 0, 4, 5, 0, 6, 7, 0, 8, 0, 0, 0, 9, 10, 0, 0, 0, 11, 12, 0, 0, 0, 13, 14, 0, 15, 16]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 3, 0, 0, 0, 4, 0, 0]

private def crossRows : Array ℕ :=
  #[5517788181, 1614839814, 1614839811, 1078001668, 809664518, 809615366, 1077968899, 809533443, 1648477190, 3225452684, 541179910, 1614905350, 809615366, 1656914054, 809615366, 1614839811, 1077968899]

private def masks : Array ℕ :=
  #[272962, 4718610, 135556, 4582252489, 2155913216, 293995513, 271847017, 5452660736, 1080047814, 361209856, 338690084, 6511133494, 6444523265, 276798465, 4649361153, 5385953225, 294109129, 298816921, 7541359609, 1373634809, 5391850697, 6444289915, 6452447033, 7546312089, 4649321270, 7520231273, 7586462694, 7524162561, 4649324411, 4657743673, 7587077925, 7519346669, 1349524717, 2432205881, 369067065, 7536451561, 4582219771, 1374141641]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 0, 25, 26, 27, 0, 0, 28, 29, 30, 0, 31, 32]

private def mask (p : Fin 38) : ℕ := masks.getD p.val 0
private def keep (p : Fin 38) : Fin 34 := Fin.ofNat' 34 (kept.getD p.val 0)
private def cross (p k : Fin 38) : Choice 38 34 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (7 * negativeIndex.getD k.val 0)) &&& 127
  if x < 38 then .skip (Fin.ofNat' 38 x)
  else .edge (Fin.ofNat' 34 (x-38)) (((x-38) / 34+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 38) := #[1, 3, 5, 9, 13, 14, 16, 17, 19, 23, 24, 28, 29, 33, 34, 36, 37]
private def negativeRows : Array (Fin 38) := #[25, 26, 30, 31, 35]
private def positiveRay (i : Fin 17) : Fin 38 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 5) : Fin 38 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 38) : Fin 17 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 38) : Fin 5 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 38) (hp : 0 < stage19.ray p 27)
    (hk : stage19.ray k 27 < 0) :
    CrossOK stage19 stage20 27 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage19.ray p 27 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage19.ray k 27 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage19 stage20 27 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[274794016872, 69073897731, 7600082180, 273586028648, 95326963746, 137295039584, 247333749097, 247038181676, 107238381612, 107229861993, 274793230408, 248540950857, 248278937868, 137506128657, 0, 164999950872, 259771331208, 224169030188, 258556031593, 96567719946, 137428499528, 205321151808, 167648043266, 163759194672, 258530591400, 0, 19142823552, 0, 237046031976, 0, 179560022400, 46420727824, 107373451400]
private def column (i : Fin 33) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 33)) :=
  #[[0, 26, 22, 31, 2], [0, 26, 13, 2], [0, 26, 13, 22], [5, 22, 13, 26, 31, 30, 2], [0, 26, 1, 2], [10, 26, 22, 31, 2, 13], [8, 22, 26, 13], [0, 2, 13, 22], [0, 26, 18, 31, 4, 17], [0, 2, 1, 31, 30], [0, 1, 23, 30, 17], [0, 13, 17, 22, 30, 21], [3, 26, 22, 13, 2], [3, 26, 31, 1, 2], [3, 2, 22, 13, 31, 30], [20, 23, 22, 26, 2, 13], [20, 30, 4, 26, 31, 2, 1], [20, 6, 26, 31, 2, 1], [10, 26, 22, 18, 2, 13], [10, 26, 13, 8, 1], [20, 23, 1, 17, 26], [16, 21, 23, 2, 22, 13], [16, 6, 2, 22, 13], [20, 6, 26, 18, 2, 13, 1], [0, 13, 22, 31, 30, 21, 7], [24, 2, 22, 23, 1, 17, 28], [0, 18, 22, 23, 4, 17, 16, 28], [3, 26, 18, 2, 23, 4], [12, 23, 2, 22, 31, 30, 21, 13], [11, 22, 31, 2, 30, 13, 6], [3, 18, 1, 22, 23, 17, 28, 24], [16, 4, 13, 28, 17], [8, 16, 23, 1, 26, 18], [8, 11, 26, 30, 13, 1], [8, 11, 31, 30, 2, 13, 1], [19, 28, 2, 23, 26, 22, 13, 17], [15, 30, 26, 22, 31, 2, 23, 21, 13], [20, 8, 1, 26, 31, 5, 32]]
private def zeros (k : Fin 38) : List (Fin 33) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 33,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 274877906943 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage19 stage20 27 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 33 → ℝ)} (h : Covered W stage19)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage20 :=
  valid.advance h fun _ => hm _

end MOC.ThreeSharedRepeatedFive.Cut20
