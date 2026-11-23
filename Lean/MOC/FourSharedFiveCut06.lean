import MOC.FourSharedFiveData

/-! Impose coefficient evaluation 26 in cut 6. -/

open MOC.IntegerRayCut

namespace MOC.FourSharedFive.Cut06

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

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

private theorem valid : Valid stage05 stage06 26 mask keep cross := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply blocks <;>
    intro b <;> fin_cases b <;> decide +kernel

theorem covered {W : Submodule ℝ (Fin 51 → ℝ)} (h : Covered W stage05)
    (hm : ∀ r, realRow (poolRay r) ∈ W) : Covered W stage06 :=
  valid.advance h fun _ => hm _

end MOC.FourSharedFive.Cut06
