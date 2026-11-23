import MOC.WeightedDiamondTransitions
import MOC.WeightedDiamondWitnessMasks
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.FinCases

/-! Integer rays generate a cone of nonnegative evaluations. Each cut adds
one evaluation. A bit mask records the strictly positive evaluations. -/

open BigOperators

namespace MOC.IntegerRayCut

structure Stage (d : ℕ) where
  count : ℕ
  ray : Fin count → Fin d → ℤ
  imposed : Finset (Fin d)

def realRow {d : ℕ} (r : Fin d → ℤ) (i : Fin d) : ℝ := r i

structure Covered {d : ℕ} (W : Submodule ℝ (Fin d → ℝ)) (a : Stage d) : Prop where
  zero_of : ∀ v ∈ W, (∀ i ∈ a.imposed, v i = 0) → v = 0
  weights : ∀ v ∈ W, (∀ i ∈ a.imposed, 0 ≤ v i) → ∃ w : Fin a.count → ℝ,
    (∀ k, 0 ≤ w k) ∧ v = ∑ k, w k • realRow (a.ray k)

/-- Split a finite check into blocks. The last block can repeat the initial cases. -/
theorem blocks {n : ℕ} [NeZero n] {P : Fin n → Prop}
    (h : ∀ k : Fin (n / 8 + 1), ∀ r : Fin 8, P (Fin.ofNat' n (k.val * 8 + r.val))) :
    ∀ i, P i := by
  intro i
  let k : Fin (n / 8 + 1) := ⟨i.val / 8, by have := i.isLt; omega⟩
  let r : Fin 8 := ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
  have he : Fin.ofNat' n (k.val * 8 + r.val) = i := by
    apply Fin.ext
    change (i.val / 8 * 8 + i.val % 8) % n = i.val
    rw [show i.val / 8 * 8 + i.val % 8 = i.val by omega, Nat.mod_eq_of_lt i.isLt]
  simpa only [he] using h k r

inductive Choice (m n : ℕ)
  | skip (witness : Fin m)
  | edge (target : Fin n) (scale : ℤ)

def CrossOK {d : ℕ} (a b : Stage d) (j : Fin d) (mask : Fin a.count → ℕ)
    (p k : Fin a.count) : Choice a.count b.count → Prop
  | .skip q => q ≠ p ∧ q ≠ k ∧ (mask q &&& (mask p ||| mask k)) = mask q
  | .edge l c => 0 ≤ c ∧ ∀ i, a.ray p j * a.ray k i - a.ray k j * a.ray p i = c * b.ray l i

instance {d : ℕ} (a b : Stage d) (j : Fin d) (mask : Fin a.count → ℕ)
    (p k : Fin a.count) (c : Choice a.count b.count) : Decidable (CrossOK a b j mask p k c) := by
  cases c <;> unfold CrossOK <;> infer_instance

def bitUnion {d : ℕ} (column : Fin d → ℕ) (indices : List (Fin d)) : ℕ :=
  RayCoefficients.unionMasks (indices.map column)

/-- For each ray, the listed zero coordinates cover every other ray.
One bitwise union checks all the other rays at once. -/
theorem separates_of_cover {d m : ℕ} (mask : Fin m → ℕ) (column : Fin d → ℕ)
    (indices : Fin m → List (Fin d)) (allBits : ℕ)
    (hcol : ∀ p i, (column i).testBit p.val = (mask p).testBit i.val)
    (hz : ∀ k i, i ∈ indices k → (mask k).testBit i.val = false)
    (hc : ∀ k, bitUnion column (indices k) ||| 2 ^ k.val = allBits)
    (hall : ∀ p : Fin m, allBits.testBit p.val = true) :
    ∀ p k, p ≠ k → ∃ i : Fin d, (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false := by
  intro p k hpk
  have hne : p.val ≠ k.val := fun he => hpk (Fin.ext he)
  have hk : (2 ^ k.val : ℕ).testBit p.val = false := by
    exact Nat.testBit_two_pow_of_ne hne.symm
  have h := congrArg (fun b : ℕ => b.testBit p.val) (hc k)
  change (bitUnion column (indices k) ||| 2 ^ k.val).testBit p.val = allBits.testBit p.val at h
  rw [Nat.testBit_or, hk, Bool.or_false, hall] at h
  obtain ⟨b, hb, hp⟩ := (RayCoefficients.testBit_unionMasks _ _).mp h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact ⟨i, (hcol p i).symm.trans hp, hz k i hi⟩

structure Valid {d : ℕ} [NeZero d] (a b : Stage d) (j : Fin d)
    (mask : Fin a.count → ℕ) (keep : Fin a.count → Fin b.count)
    (cross : Fin a.count → Fin a.count → Choice a.count b.count) : Prop where
  imposed : b.imposed = insert j a.imposed
  nonnegative : ∀ p i, i ∈ a.imposed → 0 ≤ a.ray p i
  next_nonnegative : ∀ p i, i ∈ a.imposed → 0 ≤ b.ray p i
  next_positive : ∀ p, ∃ i ∈ a.imposed, 0 < b.ray p i
  bits : ∀ p i, (mask p).testBit i.val = (decide (i ∈ a.imposed) && decide (0 < a.ray p i))
  separates : ∀ p k, p ≠ k → ∃ i : Fin d,
    (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false
  kept : ∀ p, 0 ≤ a.ray p j → ∀ i, a.ray p i = b.ray (keep p) i
  crossing : ∀ p k, 0 < a.ray p j → a.ray k j < 0 → CrossOK a b j mask p k (cross p k)

theorem Valid.advance {d : ℕ} [NeZero d] {a b : Stage d} {j : Fin d}
    {mask : Fin a.count → ℕ} {keep : Fin a.count → Fin b.count}
    {cross : Fin a.count → Fin a.count → Choice a.count b.count}
    (h : Valid a b j mask keep cross) {W : Submodule ℝ (Fin d → ℝ)} (hc : Covered W a)
    (hm : ∀ k, realRow (a.ray k) ∈ W) : Covered W b := by
  have incl : a.imposed ⊆ b.imposed := by
    rw [h.imposed]
    exact Finset.subset_insert _ _
  refine ⟨fun v hv hz => hc.zero_of v hv fun i hi => hz i (incl hi), ?_⟩
  intro v hv hn
  have onbit (p i) : (mask p).testBit i.val = true ↔ i ∈ a.imposed ∧ 0 < a.ray p i := by
    simp only [h.bits, Bool.and_eq_true, decide_eq_true_eq]
  have offbit (p i) (hi : i ∈ a.imposed) (h0 : (mask p).testBit i.val = false) : a.ray p i = 0 := by
    refine le_antisymm ?_ (h.nonnegative p i hi)
    by_contra! hp
    exact Bool.noConfusion (h0.symm.trans ((onbit p i).mpr ⟨hi,hp⟩))
  refine exists_conic_weights_after_adjacent_cut W a.imposed j
    (fun p => realRow (a.ray p)) (fun k => realRow (b.ray k)) hc.zero_of hm
    (fun p i hi => by dsimp only [realRow]; exact_mod_cast h.nonnegative p i hi) ?_ hc.weights
    (fun p i hi => by dsimp only [realRow]; exact_mod_cast h.next_nonnegative p i hi) ?_ ?_ ?_ v hv
    (fun i hi => hn i (incl hi)) (hn j (by rw [h.imposed]; exact Finset.mem_insert_self _ _))
  · intro p k hk
    obtain ⟨i, hp, hz⟩ := h.separates p k hk
    obtain ⟨hi, hp'⟩ := (onbit p i).mp hp
    exact ⟨i, hi, by dsimp only [realRow]; exact_mod_cast hp',
      by dsimp only [realRow]; exact_mod_cast offbit k i hi hz⟩
  · intro p
    obtain ⟨i, hi, hx⟩ := h.next_positive p
    exact ⟨i, hi, by dsimp only [realRow]; exact_mod_cast hx⟩
  · intro p hp
    dsimp only [realRow] at hp
    refine ⟨keep p, 1, zero_le_one, ?_⟩
    rw [one_smul]
    funext i
    have hi := h.kept p (by exact_mod_cast hp) i
    dsimp only [realRow]
    exact_mod_cast hi
  · intro p k hp hk ha
    dsimp only [realRow] at hp hk
    have h' := h.crossing p k (by exact_mod_cast hp) (by exact_mod_cast hk)
    cases he : cross p k with
    | edge l c =>
      simp only [he, CrossOK] at h'
      refine ⟨l, c, by exact_mod_cast h'.1, ?_⟩
      funext i
      change (a.ray p j : ℝ) * a.ray k i - (a.ray k j : ℝ) * a.ray p i = (c : ℝ) * b.ray l i
      exact_mod_cast h'.2 i
    | skip q =>
      simp only [he, CrossOK] at h'
      obtain ⟨i, hi, hpi, hki, hqi⟩ := ha q h'.1 h'.2.1
      dsimp only [realRow] at hpi hki hqi
      have pz : a.ray p i = 0 := by exact_mod_cast hpi
      have kz : a.ray k i = 0 := by exact_mod_cast hki
      have qpos : 0 < a.ray q i := by exact_mod_cast hqi
      have bit := congrArg (fun z : ℕ => z.testBit i.val) h'.2.2
      simp [Nat.testBit_and, Nat.testBit_or, h.bits, hi, pz, kz, qpos] at bit

end MOC.IntegerRayCut
