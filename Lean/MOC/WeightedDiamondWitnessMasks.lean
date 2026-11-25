import MOC.WeightedDiamondRayCertificate
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.FinRange

/-! Bitset checks for the skipped crossings and the support antichain. -/

namespace MOC.RayCoefficients

def unionMasks (masks : List ℕ) : ℕ := masks.foldr Nat.lor 0

theorem testBit_unionMasks (masks : List ℕ) (i : ℕ) :
    (unionMasks masks).testBit i = true ↔ ∃ b ∈ masks, b.testBit i = true := by
  induction masks with
  | nil => simp [unionMasks]
  | cons b masks ih =>
    change (b ||| unionMasks masks).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    simp only [List.mem_cons]
    exact ⟨fun h => h.elim (fun hb => ⟨b, Or.inl rfl, hb⟩)
        (fun ⟨c, hc, hi⟩ => ⟨c, Or.inr hc, hi⟩),
      fun ⟨c, hc, hi⟩ => hc.elim (fun he => Or.inl (he ▸ hi)) (fun hm => Or.inr ⟨c, hm, hi⟩)⟩

theorem testBit_meetMasks (base : ℕ) (masks : List ℕ) (i : ℕ) :
    (masks.foldr Nat.land base).testBit i = true ↔
      base.testBit i = true ∧ ∀ b ∈ masks, b.testBit i = true := by
  induction masks with
  | nil => simp
  | cons b masks ih =>
    change (b &&& masks.foldr Nat.land base).testBit i = true ↔ _
    simp only [Nat.testBit_and, Bool.and_eq_true, ih, List.mem_cons, forall_eq_or_imp]
    tauto

/-- Bits for positive rays covered by a single third-ray witness.
The ray's own bit is excluded. -/
def witnessMask {m : ℕ} (base : ℕ) (posAt : Fin 24 → ℕ)
    (record : Fin m × List (Fin 24)) : ℕ :=
  Nat.ldiff ((record.2.map posAt).foldr Nat.land base) (2 ^ record.1.val)

/-- Each positive ray at a fixed negative ray's crossing either has an
explicit crossing record or a third ray that certifies non-adjacency. -/
theorem crossing_cover_of_masks {m n : ℕ} (old : Fin m → Row) (next : Fin n → Row)
    (s : Finset (Fin 24)) (j : Fin 24) (base : ℕ) (posAt : Fin 24 → ℕ)
    (edges : Fin m → List (Fin m)) (records : Fin m → List (Fin m × List (Fin 24)))
    (hbase : ∀ p : Fin m, base.testBit p.val = positive (old p j))
    (hat : ∀ p i, i ∈ s → (posAt i).testBit p.val = positive (old p i))
    (hsign : ∀ p i, i ∈ s → zero (old p i) = true ∨ positive (old p i) = true)
    (hrecords : ∀ k rec, rec ∈ records k → rec.1 ≠ k ∧
      ∀ i ∈ s, zero (old k i) = true → positive (old rec.1 i) = true → i ∈ rec.2)
    (hcover : ∀ k, negative (old k j) = true →
      base &&& unionMasks ((edges k).map (fun p => 2 ^ p.val) ++
        (records k).map (witnessMask base posAt)) = base)
    (p k : Fin m) (hp : positive (old p j) = true) (hk : negative (old k j) = true) :
    p ∈ edges k ∨ ∃ q, RayCutPlan.CrossingValid old next s j p k (.skip q) := by
  have hbit := congrArg (fun a : ℕ => a.testBit p.val) (hcover k hk)
  have hp' : base.testBit p.val = true := (hbase p).trans hp
  simp only [Nat.testBit_and, hp', Bool.true_and] at hbit
  obtain ⟨b, hb, hbp⟩ := (testBit_unionMasks _ _).mp hbit
  rcases List.mem_append.mp hb with he | hr
  · obtain ⟨p', hp', rfl⟩ := List.mem_map.mp he
    have hpp : p' = p := Fin.ext (by simpa only [Nat.testBit_two_pow, decide_eq_true_eq] using hbp)
    exact Or.inl (hpp ▸ hp')
  · obtain ⟨r, hrec, rfl⟩ := List.mem_map.mp hr
    have hr' := hrecords k r hrec
    simp only [witnessMask, Nat.testBit_ldiff, Bool.and_eq_true, Bool.not_eq_true,
      Nat.testBit_two_pow, decide_eq_false_iff_not] at hbp
    have hne : r.1 ≠ p := by
      intro h
      have hfalse := hbp.2
      simp [h] at hfalse
    refine Or.inr ⟨r.1, hne, hr'.1, ?_⟩
    intro i hi hpz hkz
    rcases hsign r.1 i hi with hz | hpositive
    · exact hz
    have himem := hr'.2 i hi hkz hpositive
    have hpositiveP := ((testBit_meetMasks base _ p.val).mp hbp.1).2
      (posAt i) (List.mem_map.mpr ⟨i, himem, rfl⟩)
    rw [hat p i hi] at hpositiveP
    exact False.elim ((eval_pos_of_check zero_lt_one hpositiveP).ne'
      (eval_zero_of_check 1 hpz))

/-- An exact row-support cover supplies the separating-coordinate property. -/
theorem separates_of_maskCoverage {m : ℕ} (old : Fin m → Row)
    (s : Finset (Fin 24)) (posAt : Fin 24 → ℕ) (zeroCoords : Fin m → List (Fin 24))
    (hat : ∀ p i, i ∈ s → (posAt i).testBit p.val = positive (old p i))
    (hz : ∀ q i, i ∈ zeroCoords q → i ∈ s ∧ zero (old q i) = true)
    (hcover : ∀ q : Fin m, Nat.ldiff (2 ^ m - 1) (2 ^ q.val) &&&
      unionMasks ((zeroCoords q).map posAt) = Nat.ldiff (2 ^ m - 1) (2 ^ q.val))
    (p q : Fin m) (hpq : p ≠ q) :
    ∃ i ∈ s, positive (old p i) = true ∧ zero (old q i) = true := by
  have hbit := congrArg (fun a : ℕ => a.testBit p.val) (hcover q)
  have hp : (2 ^ m - 1 : ℕ).testBit p.val = true := by
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true p.isLt
  have hpq' : q.val ≠ p.val := fun h => hpq (Fin.ext h.symm)
  simp only [Nat.testBit_and, Nat.testBit_ldiff, hp, Nat.testBit_two_pow, hpq',
    decide_false, Bool.not_false, Bool.true_and] at hbit
  obtain ⟨b, hb, hpb⟩ := (testBit_unionMasks _ _).mp hbit
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  obtain ⟨his, hiz⟩ := hz q i hi
  exact ⟨i, his, (hat p i his).symm.trans hpb, hiz⟩

end MOC.RayCoefficients
