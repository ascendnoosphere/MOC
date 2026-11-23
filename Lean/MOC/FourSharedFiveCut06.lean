import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 26 in cut 6. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut06

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

local instance : NeZero stage05.count := ⟨by decide +kernel⟩
local instance : NeZero stage06.count := ⟨by decide +kernel⟩

private def positiveIndex : Array ℕ :=
  #[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 3, 4, 5, 6, 7, 8, 0, 0, 9, 0, 0, 0, 10, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 13, 0, 14, 0, 0, 15, 16, 17, 18]

private def negativeIndex : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def crossRows : Array ℕ :=
  #[36240247252254726, 144115532176818184, 206561083778, 344000036869, 36029003580572035, 36029141019525125, 306844079505287700, 162377114678725124, 0, 36028934726877186, 206561083402, 36029003580571660, 451241293381632000, 469255760745332738, 505394303037868549, 451241431625891850, 451241774820622341, 469255830404333580, 469256310769582085]

private def masks : Array ℕ :=
  #[1266912273113153, 4294967296, 1266637395206721, 1126045935730753, 8590196736, 1126037345798145, 1267049712058433, 141012366524416, 1266774834152001, 140737488617984, 1126183374692417, 1126174784759809, 1125908496785985, 1125899906853377, 74766790688769, 70368744441857, 1271310319624193, 4398046511106, 264194, 1271035441717761, 1130443982241793, 1271447758569473, 1271172880663041, 1130581421203457, 1130306543297025, 141012366270530, 140737488364098, 146028888130, 137438955586, 141149805215810, 140874927309378, 283467849794, 274877917250, 8589943362, 10818, 211381110448193, 211106232541761, 70514773065793, 70506183133249, 211518549393473, 211243671487041, 70652212027457, 70643622094913, 70377334121025, 70368744188481]

private def kept : Array ℕ :=
  #[0, 1, 2, 0, 3, 4, 0, 5, 0, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 0, 0, 0, 0, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]

private def mask (p : Fin 45) : ℕ := masks.getD p.val 0
private def keep (p : Fin 45) : Fin 43 := Fin.ofNat' 43 (kept.getD p.val 0)
private def cross (p k : Fin 45) : Choice 45 43 :=
  let x := (crossRows.getD (positiveIndex.getD p.val 0) 0 >>>
    (9 * negativeIndex.getD k.val 0)) &&& 511
  if x < 45 then .skip (Fin.ofNat' 45 x)
  else .edge (Fin.ofNat' 43 (x-45)) (((x-45) / 43+1 : ℕ) : ℤ)

private def positiveRows : Array (Fin 45) := #[0, 2, 10, 11, 12, 13, 14, 15, 16, 19, 23, 24, 35, 36, 38, 41, 42, 43, 44]
private def negativeRows : Array (Fin 45) := #[3, 6, 8, 27, 28, 29, 30]
private def positiveRay (i : Fin 19) : Fin 45 := positiveRows.getD i.val 0
private def negativeRay (i : Fin 7) : Fin 45 := negativeRows.getD i.val 0
private def positiveOf (p : Fin 45) : Fin 19 := Fin.ofNat' _ (positiveIndex.getD p.val 0)
private def negativeOf (p : Fin 45) : Fin 7 := Fin.ofNat' _ (negativeIndex.getD p.val 0)

private theorem crossingFast (p k : Fin 45) (hp : 0 < stage05.ray p 26)
    (hk : stage05.ray k 26 < 0) :
    CrossOK stage05 stage06 26 mask p k (cross p k) := by
  have hitP : ∀ p, 0 < stage05.ray p 26 → positiveRay (positiveOf p) = p := by decide +kernel
  have hitN : ∀ k, stage05.ray k 26 < 0 → negativeRay (negativeOf k) = k := by decide +kernel
  have h : ∀ u v, CrossOK stage05 stage06 26 mask
      (positiveRay u) (negativeRay v) (cross (positiveRay u) (negativeRay v)) := by
    apply blocks
    intro b
    fin_cases b <;> decide +kernel
  simpa only [hitP p hp, hitN k hk] using h (positiveOf p) (negativeOf k)

private def columns : Array ℕ := #[35150045511021, 34326577152, 0, 0, 0, 0, 35184338539853, 0, 0, 27583442334468, 0, 22286854039584, 0, 33120766737413, 0, 0, 0, 0, 295568, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 11143453086744, 0, 0, 0, 2063604908392, 7188208749761, 0, 0, 0, 33243136, 0, 0, 0, 35150012399616, 1754064815045, 0, 0, 33111405]
private def column (i : Fin 51) : ℕ := columns.getD i.val 0
private def zeroRows : Array (List (Fin 51)) :=
  #[[9, 37, 33, 11, 42, 46, 32, 18, 1], [0, 1, 18], [38, 37, 33, 11, 42, 46, 32, 18, 1], [13, 47, 11, 42, 46, 32, 18, 1], [0, 1, 47, 32], [6, 42, 18, 13, 32], [13, 46, 1, 33, 9, 42, 11, 32, 18], [0, 1, 33, 32, 9], [13, 46, 1, 33, 38, 42, 11, 32, 18], [0, 1, 33, 38, 32], [47, 11, 42, 46, 1, 32, 37, 18, 9], [6, 42, 18, 32, 37, 9], [47, 11, 42, 46, 1, 38, 32, 37, 18], [6, 42, 18, 38, 32, 37], [6, 50, 18, 32, 1], [6, 50, 42, 47, 33, 32, 1], [6, 11, 33, 9, 46, 32, 37, 18, 1], [0, 6, 18, 32], [0, 6, 47, 33, 42, 32], [6, 11, 33, 38, 46, 32, 37, 18, 1], [6, 13, 18, 47, 46, 11, 32, 1], [6, 13, 18, 33, 46, 11, 32, 1, 9], [6, 13, 18, 33, 46, 11, 38, 32, 1], [6, 47, 11, 46, 32, 37, 18, 1, 9], [6, 47, 11, 46, 38, 32, 37, 18, 1], [0, 9, 33, 11, 42, 32, 37, 18], [0, 38, 33, 11, 42, 32, 37, 18], [0, 13, 18, 47, 42, 11, 32], [0, 13, 18, 47, 33, 42, 32], [0, 13, 18, 33, 42, 11, 32, 9], [0, 13, 18, 33, 42, 11, 38, 32], [0, 47, 11, 42, 32, 37, 18, 9], [0, 47, 33, 42, 32, 37, 18, 9], [0, 47, 11, 42, 38, 32, 37, 18], [0, 47, 33, 42, 38, 32, 37, 18], [50, 1, 9, 33, 11, 42, 32, 37, 18], [50, 1, 38, 33, 11, 42, 32, 37, 18], [13, 47, 11, 42, 32, 18, 1, 50], [13, 47, 33, 1, 42, 32, 18, 50], [13, 50, 1, 18, 33, 42, 11, 32, 9], [13, 50, 1, 18, 33, 42, 11, 38, 32], [47, 11, 50, 1, 42, 32, 37, 18, 9], [47, 33, 1, 50, 42, 32, 37, 18, 9], [47, 11, 50, 1, 42, 38, 32, 37, 18], [47, 33, 1, 50, 42, 38, 32, 37, 18]]
private def zeros (k : Fin 45) : List (Fin 51) := zeroRows.getD k.val []

private theorem separating : ∀ p k, p ≠ k → ∃ i : Fin 51,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  apply separates_of_cover mask column zeros 35184372088831 <;>
    apply blocks <;> intro b <;> fin_cases b <;> decide +kernel

private theorem valid : Valid stage05 stage06 26 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, separating, ?_, crossingFast⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage05)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage06 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut06
