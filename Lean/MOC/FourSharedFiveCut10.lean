import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 19 in cut 10. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut10

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

private def positiveIndex : Array ℕ :=
  #[0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 3, 0, 4, 0, 0, 5, 0, 0, 0, 0, 0, 0, 6, 0, 7, 0, 0, 0, 0, 8]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 0, 0, 0, 4, 0, 5, 0, 0]

private def crossRows : Array ℕ :=
  #[8839177111555, 3341535086595, 5506232091141, 2207647531527, 2207647531532, 16578826409198, 15466530541840, 2207647859221, 2207648055824]

private def masks : Array ℕ :=
  #[4294967296, 42949935104, 1126037345802241, 141012400078848, 140737488617984, 1126174885423105, 1125899973962241, 74801251090433, 70403204847617, 4398046511106, 268290, 1130478341980161, 1271447792123905, 1271172880663041, 283467849794, 211381211111489, 211106299650625, 70549132808257, 70540643539009, 211518582952001, 211243671491137, 70686672429121, 70678082500673, 70411760968257, 70403204594241, 1126355173384257, 70506183137347, 70368811301443, 70643722762307, 1267058335555649, 1267058302001729]

private def kept : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 0, 15, 16, 0, 0, 17, 18, 0, 19, 20, 21, 0, 22, 0, 23, 24]

private def mask (p : Fin 31) : ℕ := masks.getD p.val 0
private def keep (p : Fin 31) : Fin 26 := Fin.ofNat' 26 (kept.getD p.val 0)
private def cross (p k : Fin 31) : Choice 31 26 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (8 * negativeIndex.getD k.val 0)) &&& 255
  if x < 31 then .skip (Fin.ofNat' 31 x)
  else .edge (Fin.ofNat' 26 (x-31)) (((x-31) / 26+1 : ℕ) : ℤ)

private theorem valid : Valid stage09 stage10 19 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage09)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage10 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut10
