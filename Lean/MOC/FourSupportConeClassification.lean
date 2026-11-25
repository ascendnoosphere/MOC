import MOC.FourMatchingRelations
import MOC.FourSupportCostProfiles
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! An exact halfspace-intersection proof for the order-four support-cost cone. -/

open BigOperators

namespace MOC
namespace FourSupportCone

private abbrev IntegerProfile := Fin 24 → ℤ
private abbrev Profile := Fin 24 → ℝ

private def castProfile (x : IntegerProfile) : Profile := fun k => x k

private def generated {ι : Type*} [Fintype ι] (r : ι → Profile) (x : Profile) : Prop :=
  ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i • r i = x

private def ray (r : List IntegerProfile) (i : Fin r.length) : Profile :=
  castProfile (r.get i)

private theorem generated_zero {ι : Type*} [Fintype ι] (r : ι → Profile) : generated r 0 :=
  ⟨fun _ => 0, fun _ => le_rfl, by simp⟩

private theorem generated_add {ι : Type*} [Fintype ι] {r : ι → Profile} {x y : Profile}
    (hx : generated r x) (hy : generated r y) : generated r (x + y) := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨fun i => u i + v i, fun i => add_nonneg (hu i) (hv i),
    by simp only [add_smul, Finset.sum_add_distrib]⟩

private theorem generated_smul {ι : Type*} [Fintype ι] {r : ι → Profile}
    {c : ℝ} {x : Profile} (hc : 0 ≤ c) (hx : generated r x) :
    generated r (c • x) := by
  obtain ⟨u, hu, rfl⟩ := hx
  exact ⟨fun i => c * u i, fun i => mul_nonneg hc (hu i),
    by simp only [Finset.smul_sum, smul_smul]⟩

private theorem generated_sum {ι κ : Type*} [Fintype ι] {r : ι → Profile}
    (s : Finset κ) (v : κ → Profile) (hv : ∀ j ∈ s, generated r (v j)) :
    generated r (∑ j ∈ s, v j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using generated_zero r
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact generated_add (hv j (Finset.mem_insert_self _ _))
      (ih fun k hk => hv k (Finset.mem_insert_of_mem hk))

private theorem generated_single {ι : Type*} [Fintype ι] (r : ι → Profile) (i : ι) :
    generated r (r i) := by
  classical
  refine ⟨fun j => if j = i then 1 else 0, fun j => by split <;> norm_num, ?_⟩
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ h
    simp [h]
  · simp

private theorem generated_of_mem {r : List IntegerProfile} {x : IntegerProfile} (hx : x ∈ r) :
    generated (ray r) (castProfile x) := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
  simpa only [ray, hi] using generated_single (ray r) i

private theorem generated_mono {ι κ : Type*} [Fintype ι] [Fintype κ]
    {r : ι → Profile} {s : κ → Profile} {x : Profile}
    (h : ∀ i, generated s (r i)) (hx : generated r x) : generated s x := by
  obtain ⟨w, hw, rfl⟩ := hx
  exact generated_sum Finset.univ _ (fun i _ => generated_smul (hw i) (h i))

private def crossing (k : Fin 24) (x y : IntegerProfile) : IntegerProfile :=
  fun j => x k * y j - y k * x j

-- Split a positive combination at the cutting coordinate. Cancel the
-- negative part by pairing it with an equal amount of positive mass.
private theorem generated_intersection {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : ι → IntegerProfile) (s : κ → Profile) (k : Fin 24) {x : Profile}
    (hx : generated (fun i => castProfile (r i)) x) (hk : 0 ≤ x k)
    (hkeep : ∀ i, 0 ≤ r i k → generated s (castProfile (r i)))
    (hcross : ∀ i j, 0 < r i k → r j k < 0 →
      generated s (castProfile (crossing k (r i) (r j)))) : generated s x := by
  obtain ⟨w, hw, hsum⟩ := hx
  let c (i : ι) : ℝ := r i k
  let plus (i : ι) := if 0 < r i k then w i else 0
  let minus (i : ι) := if r i k < 0 then w i else 0
  let zero (i : ι) := if r i k = 0 then w i else 0
  let p := ∑ i, plus i • castProfile (r i)
  let n := ∑ i, minus i • castProfile (r i)
  let z := ∑ i, zero i • castProfile (r i)
  let P := ∑ i, plus i * c i
  let N := ∑ i, minus i * (-c i)
  let pair := ∑ i, ∑ j, (plus i * minus j) • castProfile (crossing k (r i) (r j))
  have hplus (i : ι) : 0 ≤ plus i := by dsimp [plus]; split <;> simp [hw]
  have hminus (i : ι) : 0 ≤ minus i := by dsimp [minus]; split <;> simp [hw]
  have hsplit (i : ι) : w i = plus i + minus i + zero i := by
    rcases lt_trichotomy (r i k) 0 with h | h | h
    · simp [plus, minus, zero, h, not_lt_of_ge h.le, h.ne]
    · simp [plus, minus, zero, h]
    · simp [plus, minus, zero, h, not_lt_of_ge h.le, h.ne']
  have hparts : x = p + n + z := by
    calc
      x = ∑ i, w i • castProfile (r i) := hsum.symm
      _ = ∑ i, (plus i + minus i + zero i) • castProfile (r i) :=
        Finset.sum_congr rfl (fun i _ => congrArg (fun t : ℝ => t • castProfile (r i)) (hsplit i))
      _ = p + n + z := by simp only [p, n, z, add_smul, Finset.sum_add_distrib]
  have hpos : generated s p := by
    apply generated_sum Finset.univ
    intro i _
    by_cases hi : 0 < r i k
    · exact generated_smul (hplus i) (hkeep i hi.le)
    · simpa only [plus, if_neg hi, zero_smul] using generated_zero s
  have hzero : generated s z := by
    apply generated_sum Finset.univ
    intro i _
    by_cases hi : r i k = 0
    · rw [zero, if_pos hi]
      exact generated_smul (hw i) (hkeep i hi.ge)
    · simpa only [zero, if_neg hi, zero_smul] using generated_zero s
  have hpair : generated s pair := by
    apply generated_sum Finset.univ
    intro i _
    apply generated_sum Finset.univ
    intro j _
    by_cases hi : 0 < r i k
    · by_cases hj : r j k < 0
      · exact generated_smul (mul_nonneg (hplus i) (hminus j)) (hcross i j hi hj)
      · simpa only [minus, if_neg hj, mul_zero, zero_smul] using generated_zero s
    · simpa only [plus, if_neg hi, zero_mul, zero_smul] using generated_zero s
  have hNterm (i : ι) : 0 ≤ minus i * (-c i) := by
    by_cases hi : r i k < 0
    · have hci : (r i k : ℝ) ≤ 0 := by exact_mod_cast hi.le
      exact mul_nonneg (hminus i) (neg_nonneg.mpr hci)
    · simp [minus, hi]
  have hN : 0 ≤ N := Finset.sum_nonneg (fun i _ => hNterm i)
  have hNle : N ≤ P := by
    have hpk : p k = P := by simp only [p, P, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      castProfile, c]
    have hnk : n k = -N := by
      simp only [n, N, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, castProfile, c,
        mul_neg, Finset.sum_neg_distrib, neg_neg]
    have hzk : z k = 0 := by
      simp only [z, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, castProfile]
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : r i k = 0 <;> simp [zero, hi]
    have he := congrFun hparts k
    simp only [Pi.add_apply, hpk, hnk, hzk] at he
    linarith only [hk, he]
  by_cases hP : P = 0
  · have hNzero : N = 0 := le_antisymm (hNle.trans_eq hP) hN
    have hnzero : n = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : r i k < 0
      · have hterm : minus i * (-c i) ≤ N :=
          Finset.single_le_sum (fun j _ => hNterm j) (Finset.mem_univ i)
        have htermzero : minus i * (-c i) = 0 :=
          le_antisymm (hterm.trans_eq hNzero) (hNterm i)
        have hci : (r i k : ℝ) < 0 := by exact_mod_cast hi
        have hci' : -c i ≠ 0 := (neg_pos.mpr hci).ne'
        rw [(mul_eq_zero.mp htermzero).resolve_right hci', zero_smul]
      · simp [minus, hi]
    rw [hparts, hnzero, add_zero]
    exact generated_add hpos hzero
  · have hPpos : 0 < P := lt_of_le_of_ne (hN.trans hNle) (Ne.symm hP)
    have hpairSum : pair = P • n + N • p := by
      funext l
      simp only [pair, p, n, P, N, Finset.sum_apply, Pi.smul_apply, Pi.add_apply,
        castProfile, crossing, c, smul_eq_mul, Int.cast_sub, Int.cast_mul]
      calc
        _ = ∑ i, ((plus i * (r i k : ℝ)) * (∑ j, minus j * (r j l : ℝ))) +
                   ((plus i * (r i l : ℝ)) * (∑ j, minus j * -(r j k : ℝ))) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
          ring
    have heq : P • x = (P - N) • p + P • z + pair := by
      rw [hparts, hpairSum]
      funext l
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      ring
    have hscaled := generated_smul (inv_nonneg.mpr hPpos.le)
      (generated_add (generated_add (generated_smul (sub_nonneg.mpr hNle) hpos)
        (generated_smul hPpos.le hzero)) hpair)
    rwa [← heq, smul_smul, inv_mul_cancel₀ hP, one_smul] at hscaled

private def candidates (k : Fin 24) (r : List IntegerProfile) : List IntegerProfile :=
  r.filter (fun x => decide (0 ≤ x k)) ++
    (r.filter (fun x => decide (0 < x k))).flatMap (fun x =>
      (r.filter (fun y => decide (y k < 0))).map (crossing k x))

private def sameProfile (x y : IntegerProfile) : Bool :=
  decide (∀ k, x k = y k)

private theorem sameProfile_sound {x y : IntegerProfile} (h : sameProfile x y = true) : x = y :=
  funext (of_decide_eq_true h)

-- All rows have nonnegative entries at the active coordinates. Ignore
-- rows whose strictly smaller active support occurs in the same list.
private def supportMask (active : List (Fin 24)) (x : IntegerProfile) : Nat :=
  active.foldl (fun m k => if x k = 0 then m else m ||| (1 <<< k.val)) 0

private def maskLe (x y : Nat) : Bool := (x &&& y) == x

private def supportLe (active : List (Fin 24)) (x y : IntegerProfile) : Bool :=
  maskLe (supportMask active x) (supportMask active y)

private def primitive (x : IntegerProfile) : IntegerProfile :=
  let gcd := (List.ofFn (fun k : Fin 24 => (x k).natAbs)).foldl Nat.gcd 0
  if gcd = 0 then x else fun k => x k / (gcd : ℤ)

private def supportMinimal (active : List (Fin 24)) (r : List IntegerProfile) :
    List IntegerProfile :=
  let rows := (r.map (fun x => (x, supportMask active x))).foldl
    (fun acc x => if acc.any (fun y => y.2 == x.2) then acc else x :: acc) []
  (rows.filter (fun x => !(rows.any (fun y => maskLe y.2 x.2 && (y.2 != x.2))))).map
    (fun x => primitive x.1)

-- Select a positive coordinate with least residual-to-ray ratio.
private def pivot (active : List (Fin 24)) (v r : IntegerProfile) : Option (Fin 24) :=
  (active.filter (fun k => decide (0 < r k))).foldl
    (fun best k => match best with
      | none => some k
      | some j => if v k * r j < v j * r k then some k else best) none

-- The checker accepts a subtraction only with a positive divisor and
-- a nonnegative coefficient. It checks that the final residual is zero.
private def reduces (r : List IntegerProfile) (active : List (Fin 24)) :
    ℕ → IntegerProfile → Bool
  | 0, v => sameProfile v 0
  | fuel + 1, v =>
    if sameProfile v 0 then true else
      match r.find? (fun y => supportLe active y v) with
      | none => false
      | some y =>
        match pivot active v y with
        | none => false
        | some k =>
          decide (0 < y k ∧ 0 ≤ v k) &&
            reduces r active fuel (fun l => y k * v l - v k * y l)

private theorem reduces_sound (r : List IntegerProfile) (active : List (Fin 24))
    (fuel : ℕ) (v : IntegerProfile) (h : reduces r active fuel v = true) :
    generated (ray r) (castProfile v) := by
  induction fuel generalizing v with
  | zero =>
    have hv := sameProfile_sound h
    rw [hv]
    simpa only [castProfile, Pi.zero_apply, Int.cast_zero] using generated_zero (ray r)
  | succ fuel ih =>
    by_cases hz : sameProfile v 0 = true
    · rw [sameProfile_sound hz]
      simpa only [castProfile, Pi.zero_apply, Int.cast_zero] using generated_zero (ray r)
    · cases he : r.find? (fun y => supportLe active y v) with
      | none => simp [reduces, hz, he] at h
      | some y =>
        cases hp : pivot active v y with
        | none => simp [reduces, hz, he, hp] at h
        | some k =>
          simp only [reduces, if_neg hz, he, hp, Bool.and_eq_true, decide_eq_true_eq] at h
          have hg := generated_of_mem (List.mem_of_find?_eq_some he)
          have hr := ih _ h.2
          have hy : (0 : ℝ) < y k := by exact_mod_cast h.1.1
          have hv : (0 : ℝ) ≤ v k := by exact_mod_cast h.1.2
          have hscaled := generated_smul (inv_nonneg.mpr hy.le)
            (generated_add (generated_smul hv hg) hr)
          have heq : (v k : ℝ) • castProfile y +
              castProfile (fun l => y k * v l - v k * y l) = (y k : ℝ) • castProfile v := by
            funext l
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, castProfile,
              Int.cast_sub, Int.cast_mul]
            ring
          rwa [heq, smul_smul, inv_mul_cancel₀ hy.ne', one_smul] at hscaled

private theorem advance {r s : List IntegerProfile} (k : Fin 24) (active : List (Fin 24))
    (hc : (candidates k r).all (reduces s active 24) = true)
    {x : Profile} (hx : generated (ray r) x) (hk : 0 ≤ x k) :
    generated (ray s) x := by
  have hy (y : IntegerProfile) (h : y ∈ candidates k r) :
      generated (ray s) (castProfile y) :=
    reduces_sound s active 24 y (List.all_eq_true.mp hc y h)
  apply generated_intersection (fun i => r.get i) (ray s) k hx hk
  · intro i hi
    exact hy _ (List.mem_append_left _ (List.mem_filter.mpr
      ⟨List.get_mem r i, decide_eq_true hi⟩))
  · intro i j hi hj
    apply hy
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨r.get i, List.mem_filter.mpr ⟨List.get_mem r i, decide_eq_true hi⟩, ?_⟩
    exact List.mem_map_of_mem (List.mem_filter.mpr ⟨List.get_mem r j, decide_eq_true hj⟩)

private def baseLabels : Fin 14 → Fin 24 :=
  ![0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 12, 13, 16, 18]

private def baseRay (i : Fin 14) : IntegerProfile :=
  fourMatchingEvaluation (fourMatchingCoordinatesOfValues
    (fun k => if k = baseLabels i then (1 : ℤ) else 0))

private def base : List IntegerProfile := List.ofFn baseRay

private def cuts : List (Fin 24) := [5, 11, 14, 15, 17, 19, 20, 21, 22, 23]

private def active (t : ℕ) : List (Fin 24) :=
  List.ofFn baseLabels ++ cuts.take t

private def stage : ℕ → List IntegerProfile
  | 0 => base
  | t + 1 => supportMinimal (active (t + 1)) (candidates (cuts[t]?.getD 0) (stage t))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3000000 in
private theorem basis_evaluation (m : Fin 14 → ℝ) :
    (∑ i, fourMatchingEvaluation m (baseLabels i) • castProfile (baseRay i)) =
      fourMatchingEvaluation m := by
  funext k
  fin_cases k <;>
    simp [Fin.sum_univ_succ, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      baseRay, baseLabels, castProfile, fourMatchingCoordinatesOfValues, fourMatchingEvaluation] <;>
    ring

private theorem basis_representation (m : Fin 14 → ℝ)
    (hn : ∀ i, 0 ≤ fourMatchingEvaluation m i) :
    generated (ray base) (fourMatchingEvaluation m) :=
  generated_mono (fun i => generated_of_mem (List.mem_ofFn'.mpr ⟨i, rfl⟩))
    ⟨fun i => fourMatchingEvaluation m (baseLabels i), fun i => hn _, basis_evaluation m⟩

private def stepCheck (t : ℕ) : Bool :=
  (candidates (cuts[t]?.getD 0) (stage t)).all (reduces (stage (t + 1)) (active (t + 1)) 24)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 50000000 in
private theorem verifiedSteps : ∀ t : Fin 10, stepCheck t = true := by
  fin_cases t <;> decide

private theorem stage_generated (t : ℕ) (ht : t ≤ 10) (m : Fin 14 → ℝ)
    (hn : ∀ i, 0 ≤ fourMatchingEvaluation m i) :
    generated (ray (stage t)) (fourMatchingEvaluation m) := by
  induction t with
  | zero => exact basis_representation m hn
  | succ t ih =>
    exact advance (cuts[t]?.getD 0) (active (t + 1))
      (verifiedSteps ⟨t, ht⟩) (ih (Nat.le_of_succ_le ht)) (hn _)

private def listedInt : Fin 34 ⊕ Fin 48 → IntegerProfile :=
  Sum.elim ordinaryCostRayInt mixedCostRayInt

private def listed : Fin 34 ⊕ Fin 48 → Profile :=
  Sum.elim ordinaryCostRay mixedCostRay

set_option maxRecDepth 32768 in
set_option maxHeartbeats 50000000 in
private theorem stage_final_check :
    (stage 10).all (fun r =>
      (List.ofFn ordinaryCostRayInt ++ List.ofFn mixedCostRayInt).any (sameProfile r)) = true := by
  decide

private theorem listed_of_stage {x : Profile} (hx : generated (ray (stage 10)) x) :
    generated listed x := by
  apply generated_mono _ hx
  intro i
  have hi := List.all_eq_true.mp stage_final_check ((stage 10).get i) (List.get_mem _ i)
  obtain ⟨y, hy, hsame⟩ := List.any_eq_true.mp hi
  have hxy := sameProfile_sound hsame
  rcases List.mem_append.mp hy with h | h
  · obtain ⟨j, hj⟩ := List.mem_ofFn'.mp h
    rw [ray, hxy, ← hj]
    exact generated_single listed (Sum.inl j)
  · obtain ⟨j, hj⟩ := List.mem_ofFn'.mp h
    rw [ray, hxy, ← hj]
    exact generated_single listed (Sum.inr j)

private noncomputable def evaluation : (Fin 14 → ℝ) →ₗ[ℝ] Profile where
  toFun := fourMatchingEvaluation
  map_add' x y := by
    funext i
    fin_cases i <;> simp [fourMatchingEvaluation, Pi.add_apply] <;> ring
  map_smul' t x := by
    funext i
    fin_cases i <;> simp [fourMatchingEvaluation, Pi.smul_apply, smul_eq_mul] <;> ring

private def listedCoordinates (i : Fin 34 ⊕ Fin 48) : Fin 14 → ℤ :=
  fourMatchingCoordinatesOfValues (listedInt i)

private theorem listed_cast_eval (m : Fin 14 → ℤ) :
    fourMatchingEvaluation (fun i => (m i : ℝ)) = castProfile (fourMatchingEvaluation m) := by
  funext i
  fin_cases i <;> simp [castProfile, fourMatchingEvaluation, Int.cast_add, Int.cast_mul]

set_option maxHeartbeats 3000000 in
private theorem listed_evaluation (i : Fin 34 ⊕ Fin 48) :
    evaluation (fun k => (listedCoordinates i k : ℝ)) = listed i := by
  have he : ∀ j : Fin 34 ⊕ Fin 48,
      sameProfile (fourMatchingEvaluation (listedCoordinates j)) (listedInt j) = true := by
    decide
  change fourMatchingEvaluation (fun k => (listedCoordinates i k : ℝ)) = listed i
  rw [listed_cast_eval, sameProfile_sound (he i)] <;> cases i <;> rfl

private theorem listed_nonneg (i : Fin 34 ⊕ Fin 48) (k : Fin 24) : 0 ≤ listed i k := by
  have h : ∀ (j : Fin 34 ⊕ Fin 48) (l : Fin 24), 0 ≤ listedInt j l := by decide
  have hi : listed i k = (listedInt i k : ℝ) := by cases i <;> rfl
  rw [hi]
  exact_mod_cast h i k

private theorem listed_ne_zero (i : Fin 34 ⊕ Fin 48) : listed i ≠ 0 := by
  have hl : ∀ j : Fin 34 ⊕ Fin 48, ∃ k : Fin 24, listedInt j k ≠ 0 := by decide
  obtain ⟨k, hk⟩ := hl i
  intro he
  have hv := congrFun he k
  have hi : listed i k = (listedInt i k : ℝ) := by cases i <;> rfl
  rw [hi, Pi.zero_apply] at hv
  exact hk (by exact_mod_cast hv)

private theorem listed_unique_support (i j : Fin 34 ⊕ Fin 48)
    (h : ∀ k, listed i k = 0 → listed j k = 0) : j = i := by
  have hs : ∀ (a b : Fin 34 ⊕ Fin 48),
      (∀ k : Fin 24, listedInt a k = 0 → listedInt b k = 0) → b = a := by decide
  apply hs i j
  intro k hk
  have hi : listed i k = (listedInt i k : ℝ) := by cases i <;> rfl
  have hj : listed j k = (listedInt j k : ℝ) := by cases j <;> rfl
  have hic : (listedInt i k : ℝ) = 0 := by exact_mod_cast hk
  have hjc : (listedInt j k : ℝ) = 0 := hj.symm.trans (h k (hi.trans hic))
  exact_mod_cast hjc

private theorem nonneg_of_listed {x : Profile} (hx : generated listed x) (k : Fin 24) :
    0 ≤ x k := by
  obtain ⟨w, hw, rfl⟩ := hx
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (listed_nonneg i k))

private theorem listed_of_zero_support {x : Profile} (i : Fin 34 ⊕ Fin 48)
    (hx : generated listed x) (hz : ∀ k, listed i k = 0 → x k = 0) :
    ∃ c : ℝ, 0 ≤ c ∧ x = c • listed i := by
  classical
  obtain ⟨w, hw, hsum⟩ := hx
  have hwzero (j : Fin 34 ⊕ Fin 48) (hji : j ≠ i) : w j = 0 := by
    by_contra hn
    apply hji
    apply listed_unique_support i j
    intro k hk
    have htotal : (∑ l, w l * listed l k) = 0 := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hz k hk] using congrFun hsum k
    have hterm : w j * listed j k ≤ 0 := by
      rw [← htotal]
      exact Finset.single_le_sum (fun l _ => mul_nonneg (hw l) (listed_nonneg l k))
        (Finset.mem_univ j)
    exact (mul_eq_zero.mp (le_antisymm hterm (mul_nonneg (hw j) (listed_nonneg j k)))).resolve_left hn
  refine ⟨w i, hw i, hsum.symm.trans ?_⟩
  rw [Finset.sum_eq_single i]
  · intro j _ h
    rw [hwzero j h, zero_smul]
  · simp

end FourSupportCone

open FourSupportCone

/-- A support cost is an evaluation of a real noncrossing coordinate
vector with nonnegative values at all twenty-four matchings. -/
def FourSupportCost (x : Fin 24 → ℝ) : Prop :=
  (∃ m : Fin 14 → ℝ, fourMatchingEvaluation m = x) ∧ ∀ i, 0 ≤ x i

private theorem fourSupportCost_iff_listed (x : Fin 24 → ℝ) :
    FourSupportCost x ↔ generated listed x := by
  constructor
  · rintro ⟨⟨m, rfl⟩, hn⟩
    exact listed_of_stage (stage_generated 10 le_rfl m hn)
  · intro h
    refine ⟨?_, nonneg_of_listed h⟩
    obtain ⟨w, _, rfl⟩ := h
    refine ⟨∑ i, w i • (fun k => (listedCoordinates i k : ℝ)), ?_⟩
    change evaluation _ = _
    rw [map_sum]
    simp only [map_smul, listed_evaluation]

/-- Every nonnegative order-four cost in the noncrossing matching space is
a nonnegative sum of the thirty-four ordinary and forty-eight mixed profiles. -/
theorem four_cost_cone_decomposition (m : Fin 14 → ℝ)
    (hn : ∀ i, 0 ≤ fourMatchingEvaluation m i) :
    ∃ (u : Fin 34 → ℝ) (v : Fin 48 → ℝ), (∀ i, 0 ≤ u i) ∧ (∀ j, 0 ≤ v j) ∧
      fourMatchingEvaluation m =
        (∑ i, u i • ordinaryCostRay i) + ∑ j, v j • mixedCostRay j := by
  obtain ⟨w, hw, hsum⟩ := listed_of_stage (stage_generated 10 le_rfl m hn)
  refine ⟨fun i => w (Sum.inl i), fun j => w (Sum.inr j), fun i => hw _, fun j => hw _, ?_⟩
  simpa only [Fintype.sum_sum_type, listed, Sum.elim_inl, Sum.elim_inr] using hsum.symm

/-- A nonzero support cost spans an extreme ray if every summand in a
decomposition into two support costs is a nonnegative multiple of it. -/
def FourExtremeSupportCost (x : Fin 24 → ℝ) : Prop :=
  x ≠ 0 ∧ FourSupportCost x ∧ ∀ u v : Fin 24 → ℝ,
    FourSupportCost u → FourSupportCost v → u + v = x →
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ u = a • x ∧ v = b • x

/-- The extreme rays are the positive multiples of the listed ordinary
and mixed profiles. -/
theorem four_cost_cone_extreme_rays (x : Fin 24 → ℝ) :
    FourExtremeSupportCost x ↔
      ∃ (r : Fin 34 ⊕ Fin 48) (a : ℝ), 0 < a ∧
        x = a • Sum.elim ordinaryCostRay mixedCostRay r := by
  classical
  constructor
  · rintro ⟨hx, hcone, hextreme⟩
    obtain ⟨w, hw, hsum⟩ := (fourSupportCost_iff_listed x).mp hcone
    have hpos : ∃ i, 0 < w i := by
      by_contra h
      push_neg at h
      have hw0 (i : Fin 34 ⊕ Fin 48) : w i = 0 := le_antisymm (h i) (hw i)
      exact hx (by simpa only [hw0, zero_smul, Finset.sum_const_zero] using hsum.symm)
    obtain ⟨i, hi⟩ := hpos
    let rem (j : Fin 34 ⊕ Fin 48) : ℝ := if j = i then 0 else w j
    let y := ∑ j, rem j • listed j
    have hy : generated listed y :=
      ⟨rem, fun j => by dsimp only [rem]; split <;> simp [hw], rfl⟩
    have hu : generated listed (w i • listed i) :=
      generated_smul hi.le (generated_single _ _)
    have hdecomp : w i • listed i + y = x := by
      rw [← hsum]
      let keep (j : Fin 34 ⊕ Fin 48) : ℝ := if j = i then w i else 0
      have hsingle : (∑ j, keep j • listed j) = w i • listed i := by
        rw [Finset.sum_eq_single i]
        · simp [keep]
        · intro j _ h
          simp [keep, h]
        · simp
      rw [← hsingle, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = i <;> simp [keep, rem, h]
    obtain ⟨a, _, ha, _, huEq, _⟩ := hextreme _ _ ((fourSupportCost_iff_listed _).mpr hu)
      ((fourSupportCost_iff_listed _).mpr hy) hdecomp
    have ha' : 0 < a := by
      refine lt_of_le_of_ne ha ?_
      intro hz
      rw [← hz, zero_smul] at huEq
      exact (smul_ne_zero hi.ne' (listed_ne_zero i)) huEq
    refine ⟨i, w i / a, div_pos hi ha', ?_⟩
    change x = (w i / a) • listed i
    calc
      x = a⁻¹ • (a • x) := by rw [smul_smul, inv_mul_cancel₀ ha'.ne', one_smul]
      _ = (w i / a) • listed i := by rw [← huEq, smul_smul, div_eq_mul_inv, mul_comm]
  · rintro ⟨i, a, ha, rfl⟩
    change FourExtremeSupportCost (a • listed i)
    refine ⟨smul_ne_zero ha.ne' (listed_ne_zero i), ?_, ?_⟩
    · exact (fourSupportCost_iff_listed _).mpr (generated_smul ha.le (generated_single _ _))
    · intro u v hu hv he
      have hgu := (fourSupportCost_iff_listed _).mp hu
      have hgv := (fourSupportCost_iff_listed _).mp hv
      have hzero (k : Fin 24) (hk : listed i k = 0) : u k = 0 ∧ v k = 0 := by
        have hv0 := congrFun he k
        simp only [Pi.add_apply, Pi.smul_apply, hk, smul_zero] at hv0
        have hu0 := nonneg_of_listed hgu k
        have hv1 := nonneg_of_listed hgv k
        exact ⟨by linarith only [hv0, hu0, hv1], by linarith only [hv0, hu0, hv1]⟩
      obtain ⟨b, hb, huEq⟩ := listed_of_zero_support i hgu (fun k hk => (hzero k hk).1)
      obtain ⟨c, hc, hvEq⟩ := listed_of_zero_support i hgv (fun k hk => (hzero k hk).2)
      refine ⟨b / a, c / a, div_nonneg hb ha.le, div_nonneg hc ha.le, ?_, ?_⟩
      · rw [huEq, smul_smul, div_mul_cancel₀ b ha.ne']
      · rw [hvEq, smul_smul, div_mul_cancel₀ c ha.ne']

/-- Different entries in the combined list span different extreme rays. -/
theorem four_cost_cone_ray_index_unique (i j : Fin 34 ⊕ Fin 48) {a : ℝ}
    (_ha : 0 < a)
    (hf : Sum.elim ordinaryCostRay mixedCostRay j =
      a • Sum.elim ordinaryCostRay mixedCostRay i) : j = i := by
  apply listed_unique_support i j
  intro k hk
  change listed j = a • listed i at hf
  rw [hf, Pi.smul_apply, hk, smul_zero]

private def ordinaryBasisIndices : Fin 14 → Fin 34 :=
  ![0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 16, 17, 22, 23]

-- Row i expresses baseRay i in the selected ordinary indicators.
private def ordinaryBasisCoefficients : Fin 14 → Fin 14 → ℤ :=
  ![![0, 0, -1, -1, 1, 1, 0, 0, 0, 0, -1, 0, 0, 1],
    ![0, 0, 1, 1, -1, 0, 0, 0, 0, 0, 1, 0, 0, -1],
    ![-1, 0, 1, 2, -2, -1, 0, -1, 0, 0, 2, 1, 1, 0],
    ![1, 0, -1, -1, 1, 0, 0, 1, 0, 0, -1, 0, -1, 0],
    ![1, 0, 0, -1, 1, 0, 0, 0, 0, 0, -1, -1, 0, 0],
    ![0, 0, 1, 1, -1, -1, 0, 0, 0, 1, 1, 0, 0, -1],
    ![0, 0, -1, -1, 1, 0, 0, 0, 0, -1, 0, 0, 0, 1],
    ![0, -1, -1, -2, 2, 1, 1, 1, 0, 0, -1, -1, 0, 0],
    ![0, 1, 1, 1, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, -1, -2, 1, 1, 0, 1, 1, 0, -1, 0, -1, 0],
    ![0, 0, 1, 1, 0, 0, 0, -1, -1, 0, 0, 0, 1, 0],
    ![0, 0, 1, 1, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

set_option maxHeartbeats 3000000 in
private theorem ordinary_basis_relation (i : Fin 14) :
    castProfile (baseRay i) =
      ∑ j, (ordinaryBasisCoefficients i j : ℝ) • ordinaryCostRay (ordinaryBasisIndices j) := by
  have he : ∀ (i : Fin 14) (k : Fin 24), baseRay i k =
      ∑ j, ordinaryBasisCoefficients i j * ordinaryCostRayInt (ordinaryBasisIndices j) k := by
    decide
  funext k
  change (baseRay i k : ℝ) = _
  rw [he i k]
  simp only [Int.cast_sum, Int.cast_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    ordinaryCostRay]

/-- The evaluated matching space is exactly the real span of the
ordinary graded-minor indicators. -/
theorem four_matching_space_eq_ordinary_span :
    Set.range (fourMatchingEvaluation : (Fin 14 → ℝ) → (Fin 24 → ℝ)) =
      (Submodule.span ℝ (Set.range ordinaryCostRay) : Set (Fin 24 → ℝ)) := by
  let W := Submodule.span ℝ (Set.range ordinaryCostRay)
  have hm (i : Fin 14) : castProfile (baseRay i) ∈ W := by
    rw [ordinary_basis_relation]
    exact W.sum_mem (fun j _ => W.smul_mem _ (Submodule.subset_span ⟨ordinaryBasisIndices j, rfl⟩))
  ext x
  constructor
  · rintro ⟨m, rfl⟩
    change fourMatchingEvaluation m ∈ W
    rw [← basis_evaluation m]
    exact W.sum_mem (fun i _ => W.smul_mem _ (hm i))
  · intro hx
    have hle : W ≤ evaluation.range := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact ⟨fun k => (listedCoordinates (Sum.inl j) k : ℝ), listed_evaluation (Sum.inl j)⟩
    exact hle hx

end MOC
