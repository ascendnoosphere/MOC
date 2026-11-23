import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 25 in cut 8. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut08

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 1, 0, 2, 3, 0, 0, 0, 4, 0, 5, 0, 0, 0, 0, 0, 6, 0, 0, 7, 8, 0, 9, 10, 0, 11, 12, 0, 0, 0, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 4, 0]

private def crossRows : Array ℕ :=
  #[69257396740, 413123742726, 757661438473, 68990534148, 757659603465, 1032809356964, 1445931260942, 137715000851, 1515187608590, 1926833905678, 137711853582, 137724700179, 2188017933326]

private def masks : Array ℕ :=
  #[4294967296, 8590196736, 1126037345802241, 141012366524416, 140737488617984, 1126174851868673, 1125899973962241, 74766857797633, 70368811554817, 4398046511106, 268290, 1130443982241793, 1271447758569473, 1271172880663041, 141012366270530, 140737488364098, 283467849794, 274877921346, 8589943362, 14914, 211381177557057, 211106299650625, 70514773069889, 70506250246209, 211518549397569, 211243671491137, 70652279136321, 70643689207873, 70377401229889, 70368811301441, 1267049712066625, 1266774834160193, 1126320813645889, 1126045935739457, 70506183137347]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 0, 15, 16, 0, 0, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 0, 28, 0, 29]

private def mask (p : Fin 35) : ℕ := masks.getD p.val 0
private def keep (p : Fin 35) : Fin 33 := Fin.ofNat' 33 (kept.getD p.val 0)
private def cross (p k : Fin 35) : Choice 35 33 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (9 * negativeIndex.getD k.val 0)) &&& 511
  if x < 35 then .skip (Fin.ofNat' 35 x)
  else .edge (Fin.ofNat' 33 (x-35)) (((x-35) / 33+1 : ℕ) : ℤ)

private theorem valid : Valid stage07 stage08 25 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage07)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage08 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut08
