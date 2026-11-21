import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Tactic.Linarith

/-! Finite weighted Hall inequalities give a transport plan supported on the relation. -/

open BigOperators Finset
open scoped Classical

namespace MOC

variable {α β : Type*} [Fintype α] [Fintype β]

private theorem restrict_sum {γ : Type*} [Fintype γ] (S : Finset γ) (F : γ → ℝ) :
    ∑ i ∈ S, F i = ∑ i, if i ∈ S then F i else 0 := by
  classical
  have h : univ.filter (fun i => i ∈ S) = S := by ext i; simp
  rw [← Finset.sum_filter, h]

private theorem weighted_sum_le_of_hall (R : α → β → Prop) (p : α → ℝ) (q : β → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ b, 0 ≤ q b)
    (hall : ∀ S : Finset α, ∑ a ∈ S, p a ≤
      ∑ b ∈ univ.filter (fun b => ∃ a ∈ S, R a b), q b)
    (f : α → ℝ) (g : β → ℝ) (hf : ∀ a, 0 ≤ f a) (hg : ∀ b, 0 ≤ g b)
    (hfg : ∀ a b, R a b → f a ≤ g b) : ∑ a, p a * f a ≤ ∑ b, q b * g b := by
  classical
  have aux : ∀ n (f : α → ℝ) (g : β → ℝ), (∀ a, 0 ≤ f a) → (∀ b, 0 ≤ g b) →
      (∀ a b, R a b → f a ≤ g b) →
      (univ.filter (fun a => 0 < f a)).card = n →
      ∑ a, p a * f a ≤ ∑ b, q b * g b := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f g hf hg hfg hcard
      let S := univ.filter (fun a => 0 < f a)
      by_cases hS : S.Nonempty
      · obtain ⟨a₀, ha₀, hmin⟩ := Finset.exists_min_image S f hS
        let δ := f a₀
        have hδ : 0 < δ := (Finset.mem_filter.mp ha₀).2
        let T := univ.filter (fun b => ∃ a ∈ S, R a b)
        let f' (a) := max 0 (f a - δ)
        let g' (b) := max 0 (g b - δ)
        let S' := univ.filter (fun a => 0 < f' a)
        have hsub : S' ⊆ S := by
          intro a ha
          have ha' : 0 < max 0 (f a - δ) := (Finset.mem_filter.mp ha).2
          have hpos : 0 < f a - δ := by simpa only [lt_max_iff, lt_irrefl, false_or] using ha'
          exact Finset.mem_filter.mpr ⟨mem_univ _, by linarith⟩
        have hnot : a₀ ∉ S' := by simp [S', f', δ]
        have hlt : S'.card < n := by
          rw [← hcard]
          exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨hsub, fun h => hnot (h.symm ▸ ha₀)⟩)
        have hsum := ih S'.card hlt f' g'
          (fun _ => le_max_left _ _) (fun _ => le_max_left _ _)
          (fun a b hab => max_le_max le_rfl (sub_le_sub_right (hfg a b hab) _)) rfl
        have hleft (a : α) : f a = (if a ∈ S then δ else 0) + f' a := by
          by_cases ha : a ∈ S
          · rw [if_pos ha, show f' a = f a - δ from max_eq_right (sub_nonneg.mpr (hmin a ha))]
            linarith
          · have hfa : f a = 0 := le_antisymm
              (le_of_not_gt fun ha' => ha (Finset.mem_filter.mpr ⟨mem_univ a, ha'⟩)) (hf a)
            simp [ha, f', hfa, max_eq_left (neg_nonpos.mpr hδ.le)]
        have hright (b : β) : (if b ∈ T then δ else 0) + g' b ≤ g b := by
          by_cases hb : b ∈ T
          · obtain ⟨a, ha, hab⟩ := (Finset.mem_filter.mp hb).2
            have hdg : δ ≤ g b := (hmin a ha).trans (hfg a b hab)
            rw [if_pos hb, show g' b = g b - δ from max_eq_right (sub_nonneg.mpr hdg)]
            linarith
          · simpa only [hb, if_false, zero_add, g', max_le_iff] using
              And.intro (hg b) (sub_le_self (g b) hδ.le)
        calc
          _ = δ * (∑ a ∈ S, p a) + ∑ a, p a * f' a := by
            rw [mul_sum, restrict_sum S (fun a => δ * p a), ← sum_add_distrib]
            apply sum_congr rfl
            intro a _
            rw [hleft a, mul_add]
            by_cases ha : a ∈ S <;> simp [ha, mul_comm]
          _ ≤ δ * (∑ b ∈ T, q b) + ∑ b, q b * g' b :=
            add_le_add (mul_le_mul_of_nonneg_left (hall S) hδ.le) hsum
          _ ≤ _ := by
            rw [mul_sum, restrict_sum T (fun b => δ * q b), ← sum_add_distrib]
            apply sum_le_sum
            intro b _
            have h := mul_le_mul_of_nonneg_left (hright b) (hq b)
            simpa only [mul_add, mul_ite, mul_zero, mul_comm δ] using h
      · have hzero (a : α) : f a = 0 := le_antisymm
          (le_of_not_gt fun h => hS ⟨a, Finset.mem_filter.mpr ⟨mem_univ _, h⟩⟩) (hf a)
        simp only [hzero, mul_zero, sum_const_zero]
        exact sum_nonneg fun b _ => mul_nonneg (hq b) (hg b)
  exact aux _ f g hf hg hfg rfl

/-- If both nonnegative masses sum to one, every weighted Hall bound suffices
for a nonnegative transport plan supported on the prescribed relation. -/
theorem exists_transport_of_weighted_hall (R : α → β → Prop) (p : α → ℝ) (q : β → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ b, 0 ≤ q b)
    (hp₁ : ∑ a, p a = 1) (hq₁ : ∑ b, q b = 1)
    (hall : ∀ S : Finset α, ∑ a ∈ S, p a ≤
      ∑ b ∈ univ.filter (fun b => ∃ a ∈ S, R a b), q b) :
    ∃ μ : α → β → ℝ, (∀ a b, 0 ≤ μ a b) ∧ (∀ a b, μ a b ≠ 0 → R a b) ∧
      (∀ a, ∑ b, μ a b = p a) ∧ (∀ b, ∑ a, μ a b = q b) := by
  classical
  let V := (α ⊕ β) → ℝ
  let e (i : α ⊕ β) : V := Pi.single i 1
  let edge := {x : α × β // R x.1 x.2}
  let vertex (x : edge) : V := e (.inl x.val.1) + e (.inr x.val.2)
  let z : V := Sum.elim p q
  have hz : z ∈ convexHull ℝ (Set.range vertex) := by
    by_contra hn
    obtain ⟨L, c, hc, hsep⟩ := geometric_hahn_banach_point_closed
      (convex_convexHull ℝ (Set.range vertex))
      ((Set.finite_range vertex).isClosed_convexHull) hn
    let f (a : α) := -L (e (.inl a))
    let g (b : β) := L (e (.inr b)) - c
    have hfg (a : α) (b : β) (hab : R a b) : f a ≤ g b := by
      have h := hsep _ (subset_convexHull ℝ _ (Set.mem_range_self (⟨(a, b), hab⟩ : edge)))
      change c < L (e (.inl a) + e (.inr b)) at h
      rw [map_add] at h
      dsimp only [f, g]
      linarith only [h]
    let M := (∑ a, |f a|) + ∑ b, |g b|
    have hf (a : α) : 0 ≤ f a + M := by
      have h : |f a| ≤ ∑ a, |f a| := single_le_sum (fun i _ => abs_nonneg (f i)) (mem_univ a)
      have h' : 0 ≤ ∑ b, |g b| := sum_nonneg fun b _ => abs_nonneg (g b)
      dsimp only [M]
      linarith only [h, h', neg_abs_le (f a)]
    have hg (b : β) : 0 ≤ g b + M := by
      have h : |g b| ≤ ∑ b, |g b| := single_le_sum (fun i _ => abs_nonneg (g i)) (mem_univ b)
      have h' : 0 ≤ ∑ a, |f a| := sum_nonneg fun a _ => abs_nonneg (f a)
      dsimp only [M]
      linarith only [h, h', neg_abs_le (g b)]
    have hsum := weighted_sum_le_of_hall R p q hp hq hall _ _ hf hg
      (fun a b hab => add_le_add_right (hfg a b hab) M)
    simp only [mul_add, sum_add_distrib, ← sum_mul, hp₁, hq₁, one_mul] at hsum
    have hz' : (∑ i : α ⊕ β, z i • e i) = z := by
      funext i
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · change z i * (Pi.single i 1 : V) i = z i
        rw [Pi.single_eq_same, mul_one]
      · intro j _ hj
        change z j * (Pi.single j 1 : V) i = 0
        rw [Pi.single_eq_of_ne (Ne.symm hj), mul_zero]
      · simp
    have hLz : L z = (∑ a, p a * L (e (.inl a))) + ∑ b, q b * L (e (.inr b)) := by
      calc
        _ = L (∑ i : α ⊕ β, z i • e i) := (congrArg L hz').symm
        _ = _ := by
          rw [map_sum]
          simp only [map_smul, smul_eq_mul, Fintype.sum_sum_type, z, Sum.elim_inl, Sum.elim_inr]
    simp only [f, g, mul_neg, sum_neg_distrib, mul_sub, sum_sub_distrib, ← sum_mul,
      hq₁, one_mul] at hsum
    linarith only [hc, hsum, hLz]
  obtain ⟨κ, inst, w, v, hw, _, hv, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hz
  letI : Fintype κ := inst
  have hxExists (k : κ) : ∃ x : edge, vertex x = v k := hv k
  choose x hx using hxExists
  let μ (a : α) (b : β) := ∑ k : κ, if (x k).val.1 = a ∧ (x k).val.2 = b then w k else 0
  refine ⟨μ, fun a b => sum_nonneg (fun k _ => by split_ifs; exact hw k; exact le_rfl), ?_, ?_, ?_⟩
  · intro a b h
    apply Classical.byContradiction
    intro hn
    apply h
    apply sum_eq_zero
    intro k _
    have hne : ¬ ((x k).val.1 = a ∧ (x k).val.2 = b) := by
      rintro ⟨ha, hb⟩
      exact hn (by simpa only [ha, hb] using (x k).property)
    simp [hne]
  · intro a
    have he := congrFun hsum (.inl a)
    change ((∑ k, w k • v k) : V) (.inl a) = p a at he
    rw [Finset.sum_apply] at he
    have hterm (k : κ) : (w k • v k) (.inl a) = if a = (x k).val.1 then w k else 0 := by
      rw [← hx k]
      change w k * ((Pi.single (.inl (x k).val.1) 1 : V) (.inl a) +
        (Pi.single (.inr (x k).val.2) 1 : V) (.inl a)) = _
      by_cases h : a = (x k).val.1 <;> simp [Pi.single_apply, h]
    simp_rw [hterm] at he
    rw [show (∑ b, μ a b) =
        ∑ k : κ, if a = (x k).val.1 then w k else 0 by
      dsimp only [μ]
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro k _
      by_cases h : a = (x k).val.1
      · simp [h, eq_comm]
      · simp [h, Ne.symm h]]
    exact he
  · intro b
    have he := congrFun hsum (.inr b)
    change ((∑ k, w k • v k) : V) (.inr b) = q b at he
    rw [Finset.sum_apply] at he
    have hterm (k : κ) : (w k • v k) (.inr b) = if b = (x k).val.2 then w k else 0 := by
      rw [← hx k]
      change w k * ((Pi.single (.inl (x k).val.1) 1 : V) (.inr b) +
        (Pi.single (.inr (x k).val.2) 1 : V) (.inr b)) = _
      by_cases h : b = (x k).val.2 <;> simp [Pi.single_apply, h]
    simp_rw [hterm] at he
    rw [show (∑ a, μ a b) =
        ∑ k : κ, if b = (x k).val.2 then w k else 0 by
      dsimp only [μ]
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro k _
      by_cases h : b = (x k).val.2
      · simp [h, eq_comm]
      · simp [h, Ne.symm h]]
    exact he

end MOC
