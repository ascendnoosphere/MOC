import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! Entropy maximization with prescribed moments on a finite set. -/

open BigOperators

namespace MOC

noncomputable section

variable {κ : Type*} [Fintype κ]

/-- Entropy plus the average logarithm of a positive reference weight. -/
def finiteEntropyScore (w q : κ → ℝ) : ℝ :=
  ∑ i, (q i * Real.log (w i) + Real.negMulLog (q i))

/-- A finite logarithmic partition function is the maximum entropy score
over probability vectors. The reference weights need no normalization. -/
theorem finiteEntropyScore_gibbs [Nonempty κ] (w : κ → ℝ) (hw : ∀ i, 0 < w i) :
    (∀ q ∈ stdSimplex ℝ κ, finiteEntropyScore w q ≤ Real.log (∑ i, w i)) ∧
      ∃ q ∈ stdSimplex ℝ κ, finiteEntropyScore w q = Real.log (∑ i, w i) := by
  let Z : ℝ := ∑ i, w i
  have hZ : 0 < Z := Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
  let g (i : κ) := w i / Z
  have hg (i : κ) : 0 < g i := div_pos (hw i) hZ
  have hgs : ∑ i, g i = 1 := by
    simp only [g, ← Finset.sum_div]
    exact div_self hZ.ne'
  have hlg (i : κ) : Real.log (g i) = Real.log (w i) - Real.log Z :=
    Real.log_div (hw i).ne' hZ.ne'
  constructor
  · intro q hq
    have hterm (i : κ) :
        q i * Real.log (w i) + Real.negMulLog (q i) ≤
          q i * Real.log Z + g i - q i := by
      rcases eq_or_lt_of_le (hq.1 i) with hzero | hpos
      · simpa only [← hzero, zero_mul, Real.negMulLog_zero, add_zero, zero_add, sub_zero]
          using (hg i).le
      have hl := Real.log_le_sub_one_of_pos (div_pos (hg i) hpos)
      rw [Real.log_div (hg i).ne' hpos.ne', hlg i] at hl
      have hmul := mul_le_mul_of_nonneg_left hl (hq.1 i)
      have he : q i * (g i / q i - 1) = g i - q i := by
        field_simp [hpos.ne'] <;> ring
      rw [he] at hmul
      rw [Real.negMulLog_eq_neg]
      nlinarith only [hmul]
    calc
      finiteEntropyScore w q ≤ ∑ i, (q i * Real.log Z + g i - q i) :=
        Finset.sum_le_sum fun i _ => hterm i
      _ = Real.log Z := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hq.2, hgs]
        ring
  · refine ⟨g, ⟨fun i => (hg i).le, hgs⟩, ?_⟩
    have he (i : κ) :
        g i * Real.log (w i) + Real.negMulLog (g i) = g i * Real.log Z := by
      rw [Real.negMulLog_eq_neg, hlg]
      ring
    simp only [finiteEntropyScore, he, ← Finset.sum_mul, hgs, one_mul]

private theorem continuous_finiteEntropyScore (w : κ → ℝ) :
    Continuous (finiteEntropyScore w) := by
  exact continuous_finset_sum _ fun i _ =>
    ((continuous_apply i).mul continuous_const).add
      (Real.continuous_negMulLog.comp (continuous_apply i))

private theorem concaveOn_finiteEntropyScore (w : κ → ℝ) :
    ConcaveOn ℝ (stdSimplex ℝ κ) (finiteEntropyScore w) := by
  refine ⟨convex_stdSimplex ℝ κ, ?_⟩
  intro q hq r hr a b ha hb hab
  change a * finiteEntropyScore w q + b * finiteEntropyScore w r ≤
    finiteEntropyScore w (a • q + b • r)
  simp only [finiteEntropyScore, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hi := Real.concaveOn_negMulLog.2
    (show q i ∈ Set.Ici (0 : ℝ) from hq.1 i)
    (show r i ∈ Set.Ici (0 : ℝ) from hr.1 i) ha hb hab
  change a * Real.negMulLog (q i) + b * Real.negMulLog (r i) ≤
    Real.negMulLog (a * q i + b * r i) at hi
  change a * (q i * Real.log (w i) + Real.negMulLog (q i)) +
    b * (r i * Real.log (w i) + Real.negMulLog (r i)) ≤
    (a * q i + b * r i) * Real.log (w i) + Real.negMulLog (a * q i + b * r i)
  nlinarith only [hi]

/-- If a finite moment constraint is feasible, the upper bounds from all
linear potentials are attained or improved by some feasible entropy score. -/
theorem exists_finiteEntropyScore_of_potential_bounds [Nonempty κ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : κ → E) (w : κ → ℝ) (hw : ∀ i, 0 < w i) (m : E) (z : ℝ)
    (hfeasible : ∃ q ∈ stdSimplex ℝ κ, (∑ i, q i • g i) = m)
    (hbound : ∀ f : E →L[ℝ] ℝ, z ≤ f m + Real.log (∑ i, w i * Real.exp (-f (g i)))) :
    ∃ q ∈ stdSimplex ℝ κ, (∑ i, q i • g i) = m ∧ z ≤ finiteEntropyScore w q := by
  let M : (κ → ℝ) →L[ℝ] E :=
    ∑ i, (ContinuousLinearMap.proj (R := ℝ) i).smulRight (g i)
  have hM (q : κ → ℝ) : M q = ∑ i, q i • g i := by
    simp only [M, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply]
  let F := finiteEntropyScore w
  have hF := continuous_finiteEntropyScore w
  obtain ⟨q₀, hq₀, hm₀⟩ := hfeasible
  obtain ⟨qlo, _, hlo⟩ := (isCompact_stdSimplex κ).exists_isMinOn ⟨q₀, hq₀⟩ hF.continuousOn
  obtain ⟨qhi, _, hhi⟩ := (isCompact_stdSimplex κ).exists_isMaxOn ⟨q₀, hq₀⟩ hF.continuousOn
  let S : Set ((κ → ℝ) × ℝ) :=
    (stdSimplex ℝ κ ×ˢ Set.Icc (F qlo) (F qhi)) ∩ {p | p.2 ≤ F p.1}
  have hSc : IsCompact S := ((isCompact_stdSimplex κ).prod isCompact_Icc).inter_right
    (isClosed_le continuous_snd (hF.comp continuous_fst))
  have hSv : Convex ℝ S := by
    let D := (stdSimplex ℝ κ ×ˢ Set.Icc (F qlo) (F qhi))
    have he : S = D ∩ {p : (κ → ℝ) × ℝ | p.1 ∈ stdSimplex ℝ κ ∧ p.2 ≤ F p.1} := by
      ext p
      exact ⟨fun hp => ⟨hp.1, hp.1.1, hp.2⟩, fun hp => ⟨hp.1, hp.2.2⟩⟩
    rw [he]
    exact ((convex_stdSimplex ℝ κ).prod (convex_Icc _ _)).inter
      (concaveOn_finiteEntropyScore w).convex_hypograph
  let N := M.prodMap (ContinuousLinearMap.id ℝ ℝ)
  have hN (p : (κ → ℝ) × ℝ) : N p = (M p.1, p.2) := rfl
  by_contra! hfail
  have hnot : (m, z) ∉ N '' S := by
    rintro ⟨p, hp, he⟩
    rw [hN] at he
    have hm := congrArg Prod.fst he
    have hz := congrArg Prod.snd he
    rw [hM] at hm
    exact (not_le_of_gt (hfail p.1 hp.1.1 hm)) (hz ▸ hp.2)
  obtain ⟨L, c, hsmall, hlarge⟩ := geometric_hahn_banach_closed_point
    (hSv.linear_image N.toLinearMap) (hSc.image N.continuous).isClosed hnot
  have htop (q : κ → ℝ) (hq : q ∈ stdSimplex ℝ κ) : L (M q, F q) < c := by
    have hmem : (q, F q) ∈ S := ⟨⟨hq, hlo hq, hhi hq⟩, le_rfl⟩
    exact hsmall _ ⟨(q, F q), hmem, hN _⟩
  let l := L.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let d := L (0, 1)
  have hL (x : E) (t : ℝ) : L (x, t) = l x + t * d := by
    have he : (x, t) = (x, 0) + t • ((0, 1) : E × ℝ) := by simp
    exact (congrArg L he).trans (by simp [l, d, smul_eq_mul])
  have hqsmall := htop q₀ hq₀
  rw [hM, hm₀, hL] at hqsmall
  rw [hL] at hlarge
  have hz₀ : F q₀ < z := hfail q₀ hq₀ hm₀
  have hd : 0 < d := by
    by_contra! hneg
    have hrev := mul_le_mul_of_nonpos_right hz₀.le hneg
    linarith only [hqsmall, hlarge, hrev]
  let f : E →L[ℝ] ℝ := (-d⁻¹) • l
  have hf (x : E) : f x = - l x / d := by
    simp only [f, ContinuousLinearMap.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  let v (i : κ) := w i * Real.exp (-f (g i))
  obtain ⟨q, hq, hqg⟩ := (finiteEntropyScore_gibbs v
    (fun i => mul_pos (hw i) (Real.exp_pos _))).2
  have hsplit : finiteEntropyScore v q = F q - f (M q) := by
    rw [hM, map_sum]
    simp only [F, finiteEntropyScore, v, map_smul, smul_eq_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.log_mul (hw i).ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have htilt := hbound f
  change z ≤ f m + Real.log (∑ i, v i) at htilt
  rw [← hqg, hsplit] at htilt
  simp only [hf] at htilt
  have hmul := mul_le_mul_of_nonneg_right htilt hd.le
  have he (x : ℝ) : (-x / d) * d = -x := div_mul_cancel₀ _ hd.ne'
  rw [add_mul, sub_mul, he, he] at hmul
  have hqsmall := htop q hq
  rw [hL] at hqsmall
  linarith only [hqsmall, hlarge, hmul]

/-- Bounds from all linear potentials imply feasibility and give a
probability vector whose entropy score attains or exceeds the bound. -/
theorem exists_finiteEntropyScore_of_all_potential_bounds [Nonempty κ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : κ → E) (w : κ → ℝ) (hw : ∀ i, 0 < w i) (m : E) (z : ℝ)
    (hbound : ∀ f : E →L[ℝ] ℝ, z ≤ f m + Real.log (∑ i, w i * Real.exp (-f (g i)))) :
    ∃ q ∈ stdSimplex ℝ κ, (∑ i, q i • g i) = m ∧ z ≤ finiteEntropyScore w q := by
  classical
  apply exists_finiteEntropyScore_of_potential_bounds g w hw m z _ hbound
  let M : (κ → ℝ) →L[ℝ] E :=
    ∑ i, (ContinuousLinearMap.proj (R := ℝ) i).smulRight (g i)
  have hM (q : κ → ℝ) : M q = ∑ i, q i • g i := by
    simp only [M, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply]
  change ∃ q ∈ stdSimplex ℝ κ, (∑ i, q i • g i) = m
  by_contra hfail
  have hnot : m ∉ M '' stdSimplex ℝ κ := by
    rintro ⟨q, hq, he⟩
    exact hfail ⟨q, hq, (hM q).symm.trans he⟩
  obtain ⟨l, c, hsmall, hlarge⟩ := geometric_hahn_banach_closed_point
    ((convex_stdSimplex ℝ κ).linear_image M.toLinearMap)
    ((isCompact_stdSimplex κ).image M.continuous).isClosed hnot
  have hg (i : κ) : l (g i) < c := by
    let q : κ → ℝ := fun j => if j = i then 1 else 0
    have hq : q ∈ stdSimplex ℝ κ := by
      refine ⟨fun j => ?_, ?_⟩
      · simp only [q]
        split <;> norm_num
      · simp [q]
    have hqg : M q = g i := by
      rw [hM]
      simp [q, ite_smul]
    exact hsmall _ ⟨q, hq, hqg⟩
  let W : ℝ := ∑ i, w i
  have hW : 0 < W := Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
  let d := l m - c
  have hd : 0 < d := sub_pos.mpr hlarge
  let s := max (Real.log W - z) 0 + 1
  have hs : 0 < s :=
    add_pos_of_nonneg_of_pos (le_max_right _ _) zero_lt_one
  let t := s / d
  have ht : 0 ≤ t := (div_pos hs hd).le
  let f : E →L[ℝ] ℝ := (-t) • l
  have hf (x : E) : f x = -t * l x := by
    simp only [f, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hsum : (∑ i, w i * Real.exp (-f (g i))) ≤ W * Real.exp (t * c) := by
    change (∑ i, w i * Real.exp (-f (g i))) ≤ (∑ i, w i) * Real.exp (t * c)
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (hw i).le
    apply Real.exp_le_exp.mpr
    rw [hf, neg_mul, neg_neg]
    exact mul_le_mul_of_nonneg_left (hg i).le ht
  have hz := hbound f
  have hl := Real.log_le_log
    (Finset.sum_pos (fun i _ => mul_pos (hw i) (Real.exp_pos _)) Finset.univ_nonempty) hsum
  rw [Real.log_mul hW.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
  have hz' := hz.trans (add_le_add_left hl (f m))
  rw [hf] at hz'
  have htd : t * d = s := div_mul_cancel₀ _ hd.ne'
  have he : -t * l m + (Real.log W + t * c) = Real.log W - s := by
    rw [← htd]
    dsimp only [d]
    ring
  rw [he] at hz'
  have hmax : Real.log W - z ≤ max (Real.log W - z) 0 := le_max_left _ _
  change z ≤ Real.log W - (max (Real.log W - z) 0 + 1) at hz'
  linarith only [hz', hmax]

end

end MOC
