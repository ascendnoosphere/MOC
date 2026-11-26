import MOC.FourCliffordSubsetFrame
import MOC.ContactCensus

open BigOperators Matrix

namespace MOC.FourCliffordFrame

private def smallWord (a : Fin 8) : List (Fin 4) :=
  ![[], [0], [1], [0, 1], [2], [0, 2], [1, 2], [0, 1, 2]] a

/-- The labels specified by a mask on the first three coordinates. -/
def smallColumnSet (a : Fin 8) : Finset (Fin 4) := (smallWord a).toFinset

private def singleColumn (i : Fin 4) : Fin 8 := ![1, 2, 4, 0] i

private theorem smallWord_product (O : Matrix (Fin 4) (Fin 4) ℝ) (a : Fin 8) :
    ((smallWord a).map (generator O)).prod = smallFrame O a := by
  fin_cases a <;> simp [smallWord, smallFrame, Matrix.mul_assoc]

private theorem singleColumn_frame (O : Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 4) (hi : i ≠ 3) :
    smallFrame O (singleColumn i) = generator O i := by
  fin_cases i <;> first | contradiction | rfl

private theorem zero_xorSmall (a : Fin 8) : xorSmall 0 a = a := by
  apply Fin.ext
  exact Nat.zero_xor _

private theorem zero_sign_small (a : Fin 8) : sign (smallMask 0) (smallMask a) = 1 := by
  have h : ∀ x : Fin 8, sign (smallMask 0) (smallMask x) = 1 := by decide +kernel
  exact h a

private theorem sign_small_sq (a : Fin 8) : (sign (smallMask a) (smallMask a) : ℝ)^2 = 1 := by
  have h : ∀ x : Fin 8, (sign (smallMask x) (smallMask x))^2 = 1 := by decide +kernel
  exact_mod_cast h a

private theorem smallFrame_mul (O : Matrix (Fin 4) (Fin 4) ℝ) (hO : Oᵀ * O = 1)
    (a b : Fin 8) : smallFrame O a * smallFrame O b =
      (sign (smallMask a) (smallMask b) : ℝ) • smallFrame O (xorSmall a b) := by
  have h := smallFrame_mul_transpose O hO 0 b
  have hzero : smallFrame O 0 = 1 := rfl
  rw [hzero, one_mul, zero_xorSmall, zero_sign_small, one_mul] at h
  have ht := smallFrame_mul_transpose O hO a b
  rw [h, Matrix.mul_smul, Int.cast_mul] at ht
  have hbb := sign_small_sq b
  have he := congrArg (fun A : Matrix (Fin 16) (Fin 16) ℝ =>
    (sign (smallMask b) (smallMask b) : ℝ) • A) ht
  simpa only [smul_smul, ← pow_two, hbb, one_smul, mul_one, mul_left_comm,
    show ∀ u v : ℝ, u * (v * u) = v * u ^ 2 by intros; ring] using he

private def wordResult : List (Fin 4) → Fin 8 × ℤ
  | [] => (0, 1)
  | i :: l =>
    let r := wordResult l
    (xorSmall (singleColumn i) r.1, r.2 * sign (smallMask (singleColumn i)) (smallMask r.1))

private theorem wordResult_frame (O : Matrix (Fin 4) (Fin 4) ℝ) (hO : Oᵀ * O = 1)
    (l : List (Fin 4)) (hl : ∀ i ∈ l, i ≠ 3) :
    (l.map (generator O)).prod = ((wordResult l).2 : ℝ) • smallFrame O (wordResult l).1 := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, wordResult, Int.cast_one, one_smul]; rfl
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)), Matrix.mul_smul,
      ← singleColumn_frame O i (hl i List.mem_cons_self), smallFrame_mul O hO]
    simp only [wordResult, Int.cast_mul, smul_smul]

private def columnInversionSign (σ : FourPerm) (a : Fin 8) : ℤ :=
  let term (i j : Fin 4) := if i ∈ smallColumnSet a ∧ j ∈ smallColumnSet a ∧ σ j < σ i then -1 else 1
  term 0 1 * term 0 2 * term 1 2

private def columnMaskImage (σ : FourPerm) (a : Fin 8) : Fin 8 :=
  (wordResult ((smallWord a).map σ)).1

private theorem smallColumnSet_excludes_last (a : Fin 8) : (3 : Fin 4) ∉ smallColumnSet a := by
  have h : ∀ r : Fin 8, (3 : Fin 4) ∉ smallColumnSet r := by decide +kernel
  exact h a

private theorem smallColumnSet_injective : Function.Injective smallColumnSet := by
  have h : ∀ a b : Fin 8, smallColumnSet a = smallColumnSet b → a = b := by decide +kernel
  exact fun _ _ he => h _ _ he

set_option maxHeartbeats 1900000 in
private theorem relabeledWord_image : ∀ (p : Fin 24) (a : Fin 8),
    let σ := fourPerm p
    (3 : Fin 4) ∉ (smallColumnSet a).map σ.toEmbedding →
      (smallColumnSet a).map σ.toEmbedding = smallColumnSet (columnMaskImage σ a) ∧
      (wordResult ((smallWord a).map σ)).2 = columnInversionSign σ a := by
  intro p
  fin_cases p <;> decide +kernel

private theorem relabeledWord_result (p : Fin 24) (a b : Fin 8)
    (h : (smallColumnSet a).map (fourPerm p).toEmbedding = smallColumnSet b) :
    wordResult ((smallWord a).map (fourPerm p)) = (b, columnInversionSign (fourPerm p) a) := by
  have hn : (3 : Fin 4) ∉ (smallColumnSet a).map (fourPerm p).toEmbedding := by
    rw [h]
    exact smallColumnSet_excludes_last b
  obtain ⟨he, hs⟩ := relabeledWord_image p a hn
  exact Prod.ext (smallColumnSet_injective (he.symm.trans h)) hs

private theorem smallFrame_column_relabel (O : Matrix (Fin 4) (Fin 4) ℝ) (hO : Oᵀ * O = 1)
    (σ : FourPerm) (a b : Fin 8) (hb : (smallColumnSet a).map σ.toEmbedding = smallColumnSet b) :
    smallFrame (O.submatrix id σ) a = (columnInversionSign σ a : ℝ) • smallFrame O b := by
  have hgen : generator (O.submatrix id σ) = generator O ∘ σ := rfl
  rw [← smallWord_product, hgen, ← List.map_map]
  have hlast (j : Fin 4) (hj : j ∈ (smallWord a).map σ) : j ≠ 3 := by
    intro h
    subst j
    apply smallColumnSet_excludes_last b
    rw [← hb, Finset.mem_map]
    obtain ⟨i, hi, hie⟩ := List.mem_map.mp hj
    exact ⟨i, List.mem_toFinset.mpr hi, hie⟩
  rw [wordResult_frame O hO _ hlast]
  obtain ⟨p, rfl⟩ := fourPerm_surjective σ
  rw [relabeledWord_result p a b hb]

def traceColumnSign (a b c d : Fin 8) : ℤ :=
  sign (smallMask a) (smallMask c) * sign (smallMask c) (smallMask c) *
  sign (smallMask d) (smallMask b) * sign (smallMask b) (smallMask b) *
  sign (smallMask (xorSmall a c)) (smallMask (xorSmall a c))

set_option maxHeartbeats 4200000 in
private theorem relabeledWord_pair_table : ∀ (p : Fin 24) (a c : Fin 8),
    let σ := fourPerm p
    let b := columnMaskImage σ a
    let d := columnMaskImage σ c
    3 ∉ (smallColumnSet a).map σ.toEmbedding → 3 ∉ (smallColumnSet c).map σ.toEmbedding →
      (smallColumnSet (xorSmall a c)).map σ.toEmbedding = smallColumnSet (xorSmall d b) ∧
      columnInversionSign σ a * columnInversionSign σ c * columnInversionSign σ (xorSmall a c) =
        traceColumnSign a b c d := by
  intro p
  fin_cases p <;> decide +kernel

private theorem scaledBladeCoefficient (x : Fin 16) (A : Matrix (Fin 16) (Fin 16) ℝ) (r : ℝ) :
    bladeCoefficient x (r • A) = r * bladeCoefficient x A := by
  simp only [bladeCoefficient, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  ring

/-- The three minor factors in a compatible Gram entry can be aligned to
principal minor factors. The orientation signs give the trace multiplier. -/
theorem compatible_column_alignment (O : Matrix (Fin 4) (Fin 4) ℝ) (hO : Oᵀ * O = 1)
    (σ : FourPerm) (a b c d : Fin 8)
    (hab : (smallColumnSet a).map σ.toEmbedding = smallColumnSet b)
    (hcd : (smallColumnSet c).map σ.toEmbedding = smallColumnSet d) :
    let A := O.submatrix id σ
    let m (M : Matrix (Fin 4) (Fin 4) ℝ) (r s : Fin 8) :=
      bladeCoefficient (smallMask r) (smallFrame M s)
    m A a a * m A c c * m A (xorSmall a c) (xorSmall a c) =
      (traceColumnSign a b c d : ℝ) * m O a b * m O c d * m O (xorSmall a c) (xorSmall d b) := by
  intro A m
  obtain ⟨p, rfl⟩ := fourPerm_surjective σ
  let σ := fourPerm p
  have hB : columnMaskImage σ a = b := congrArg Prod.fst (relabeledWord_result p a b hab)
  have hD : columnMaskImage σ c = d := congrArg Prod.fst (relabeledWord_result p c d hcd)
  have hlast_a : 3 ∉ (smallColumnSet a).map σ.toEmbedding := by
    rw [hab]
    exact smallColumnSet_excludes_last b
  have hlast_c : 3 ∉ (smallColumnSet c).map σ.toEmbedding := by
    rw [hcd]
    exact smallColumnSet_excludes_last d
  obtain ⟨hxor, hsign⟩ := relabeledWord_pair_table p a c hlast_a hlast_c
  rw [hB, hD] at hxor hsign
  have halign (r s : Fin 8) (h : (smallColumnSet r).map σ.toEmbedding = smallColumnSet s) :
      m A r r = (columnInversionSign σ r : ℝ) * m O r s := by
    dsimp only [A, m]
    rw [smallFrame_column_relabel O hO σ r s h, scaledBladeCoefficient]
  rw [halign a b hab, halign c d hcd, halign _ _ hxor]
  have hreal := congrArg (Int.cast : ℤ → ℝ) hsign
  simp only [Int.cast_mul] at hreal
  rw [← hreal]
  ring

end MOC.FourCliffordFrame
