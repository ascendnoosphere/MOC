import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 12 in cut 7. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut07

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 4, 0, 0, 5, 6, 7, 8, 0, 9, 0, 10, 0, 0, 0, 0, 11]

private def negativeIndex : Array ℕ :=
  #[0, 0, 1, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 4, 0, 0, 5, 0, 0, 0, 6, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[44541095215752, 13406825099653, 13406825099653, 31267363782664, 40065605075586, 40065611997767, 17869212500228, 28, 8798241032002, 31267363782664, 40065605075586, 17869212500228]

private def masks : Array ℕ :=
  #[1266912340222017, 4294967296, 1266637462315585, 8590196736, 1126037345798145, 141012366524416, 140737488617984, 1126183441801281, 1126174851868673, 1125908563894849, 1125899973962241, 74766857797633, 70368811550721, 1271310386733057, 4398046511106, 264194, 1271035508826625, 1130443982241793, 1271447758569473, 1271172880663041, 1130581488312321, 1130306610405889, 141012366270530, 140737488364098, 283467849794, 274877917250, 8589943362, 10818, 211381177557057, 211106299650625, 70514773065793, 70506250242113, 211518549393473, 211243671487041, 70652279136321, 70643689203777, 70377401229889, 70368811297345, 1267049712066625, 1266774834160193, 1126320813645889, 1126045935739457, 70506183133251]

private def kept : Array ℕ :=
  #[0, 0, 0, 1, 2, 3, 4, 0, 5, 0, 6, 7, 8, 0, 9, 10, 0, 11, 12, 13, 0, 0, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]

private def mask (p : Fin 43) : ℕ := masks.getD p.val 0
private def keep (p : Fin 43) : Fin 35 := Fin.ofNat' 35 (kept.getD p.val 0)
private def cross (p k : Fin 43) : Choice 43 35 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (6 * negativeIndex.getD k.val 0)) &&& 63
  if x < 43 then .skip (Fin.ofNat' 43 x)
  else .edge (Fin.ofNat' 35 (x-43)) (((x-43) / 35+1 : ℕ) : ℤ)

private theorem valid : Valid stage06 stage07 12 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage06)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage07 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut07
