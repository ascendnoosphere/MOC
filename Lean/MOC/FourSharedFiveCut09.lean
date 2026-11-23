import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 35 in cut 9. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut09

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 4, 5, 0, 0, 6, 7, 8, 9, 0, 10, 0, 0, 0, 0]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 4]

private def crossRows : Array ℕ :=
  #[275415569411, 825844830729, 137842136067, 894564303881, 1513847266831, 139318538256, 1170114616847, 139318557200, 1238968311311, 139318538256, 19243539891215]

private def masks : Array ℕ :=
  #[4294967296, 8590196736, 1126037345802241, 141012400078848, 140737488617984, 1126174885423105, 1125899973962241, 74766891352065, 70368845109249, 4398046511106, 268290, 1130443982241793, 1271447792123905, 1271172880663041, 141012399824962, 283467849794, 274877921346, 211381211111489, 211106299650625, 70514773069889, 70506283800641, 211518582952001, 211243671491137, 70652312690753, 70643722762305, 70377401229889, 70368844855873, 1267049745621057, 1126320813645889, 70506183137347, 141012366271042, 70368811301443, 1267049712067137]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 14, 0, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 0, 25, 26, 0, 27, 0]

private def mask (p : Fin 33) : ℕ := masks.getD p.val 0
private def keep (p : Fin 33) : Fin 31 := Fin.ofNat' 31 (kept.getD p.val 0)
private def cross (p k : Fin 33) : Choice 33 31 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (9 * negativeIndex.getD k.val 0)) &&& 511
  if x < 33 then .skip (Fin.ofNat' 33 x)
  else .edge (Fin.ofNat' 31 (x-33)) (((x-33) / 31+1 : ℕ) : ℤ)

private theorem valid : Valid stage08 stage09 35 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage08)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage09 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut09
