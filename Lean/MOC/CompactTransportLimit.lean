import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Lattice
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Limits of decreasing transport costs on a compact product space. -/

open Set MeasureTheory
open scoped CompactlySupported ENNReal

namespace MOC

noncomputable section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [CompactSpace Y]

/-- A positive normalized linear functional on the product with prescribed marginals. -/
def IsCompactTransportFunctional
    (Lx : C(X, ℝ) →ₗ[ℝ] ℝ) (Ly : C(Y, ℝ) →ₗ[ℝ] ℝ)
    (L : C(X × Y, ℝ) →ₗ[ℝ] ℝ) : Prop :=
  (∀ f, 0 ≤ f → 0 ≤ L f) ∧ L 1 = 1 ∧
    (∀ u, L (u.comp ⟨Prod.fst, continuous_fst⟩) = Lx u) ∧
    ∀ v, L (v.comp ⟨Prod.snd, continuous_snd⟩) = Ly v

private def compactTransportFunctionSet
    (Lx : C(X, ℝ) →ₗ[ℝ] ℝ) (Ly : C(Y, ℝ) →ₗ[ℝ] ℝ) :
    Set (C(X × Y, ℝ) → ℝ) :=
  {L | (∀ f g, L (f + g) = L f + L g) ∧
    (∀ (r : ℝ) f, L (r • f) = r * L f) ∧
    (∀ f, 0 ≤ f → 0 ≤ L f) ∧ L 1 = 1 ∧
    (∀ u, L (u.comp ⟨Prod.fst, continuous_fst⟩) = Lx u) ∧
    ∀ v, L (v.comp ⟨Prod.snd, continuous_snd⟩) = Ly v}

private theorem isClosed_compactTransportFunctionSet
    (Lx : C(X, ℝ) →ₗ[ℝ] ℝ) (Ly : C(Y, ℝ) →ₗ[ℝ] ℝ) :
    IsClosed (compactTransportFunctionSet Lx Ly) := by
  unfold compactTransportFunctionSet
  simp only [Set.setOf_and, Set.setOf_forall]
  refine (isClosed_iInter fun f => isClosed_iInter fun g =>
    isClosed_eq (continuous_apply (f + g))
      ((continuous_apply f).add (continuous_apply g))).inter ?_
  refine (isClosed_iInter fun r => isClosed_iInter fun f =>
    isClosed_eq (continuous_apply (r • f))
      (continuous_const.mul (continuous_apply f))).inter ?_
  refine (isClosed_iInter fun f => isClosed_iInter fun _ : 0 ≤ f =>
    isClosed_le continuous_const (continuous_apply f)).inter ?_
  refine (isClosed_eq (continuous_apply _) continuous_const).inter ?_
  exact (isClosed_iInter fun u => isClosed_eq (continuous_apply _) continuous_const).inter
    (isClosed_iInter fun v => isClosed_eq (continuous_apply _) continuous_const)

private def compactTransportLinearMap (Lx : C(X, ℝ) →ₗ[ℝ] ℝ) (Ly : C(Y, ℝ) →ₗ[ℝ] ℝ)
    (L : compactTransportFunctionSet Lx Ly) : C(X × Y, ℝ) →ₗ[ℝ] ℝ where
  toFun := L.val
  map_add' := L.property.1
  map_smul' := L.property.2.1

private theorem isCompact_compactTransportFunctionSet
    (Lx : C(X, ℝ) →ₗ[ℝ] ℝ) (Ly : C(Y, ℝ) →ₗ[ℝ] ℝ) :
    IsCompact (compactTransportFunctionSet Lx Ly) := by
  let I (f : C(X × Y, ℝ)) := Icc (-‖f‖) ‖f‖
  apply (isCompact_univ_pi (s := I) (fun _ => isCompact_Icc)).of_isClosed_subset
    (isClosed_compactTransportFunctionSet Lx Ly)
  intro L hL f _
  let m := compactTransportLinearMap Lx Ly ⟨L, hL⟩
  have hm : m 1 = 1 := hL.2.2.2.1
  have hpos (g : C(X × Y, ℝ)) (hg : 0 ≤ g) : 0 ≤ m g := hL.2.2.1 g hg
  have hhi : 0 ≤ ‖f‖ • (1 : C(X × Y, ℝ)) - f := by
    intro p
    change 0 ≤ ‖f‖ * 1 - f p
    have hp := (le_abs_self (f p)).trans (ContinuousMap.norm_coe_le_norm f p)
    simpa only [mul_one, sub_nonneg] using hp
  have hlo : 0 ≤ ‖f‖ • (1 : C(X × Y, ℝ)) + f := by
    intro p
    change 0 ≤ ‖f‖ * 1 + f p
    have hp := (neg_le_abs (f p)).trans (ContinuousMap.norm_coe_le_norm f p)
    rw [mul_one]
    linarith only [hp]
  have ha := hpos _ hhi
  have hb := hpos _ hlo
  simp only [map_sub, map_add, map_smul, hm, smul_eq_mul, mul_one] at ha hb
  change -‖f‖ ≤ m f ∧ m f ≤ ‖f‖
  exact ⟨by linarith only [hb], sub_nonneg.mp ha⟩

/-- A decreasing sequence of continuous costs has a common transport
functional for any lower bound attained separately at each step. -/
theorem exists_common_compact_transport_functional
    (Lx : C(X, ℝ) →ₗ[ℝ] ℝ) (Ly : C(Y, ℝ) →ₗ[ℝ] ℝ)
    (c : ℕ → C(X × Y, ℝ)) (hc : Antitone c) (a : ℝ)
    (h : ∀ n, ∃ L, IsCompactTransportFunctional Lx Ly L ∧ a ≤ L (c n)) :
    ∃ L, IsCompactTransportFunctional Lx Ly L ∧ ∀ n, a ≤ L (c n) := by
  let S := compactTransportFunctionSet Lx Ly
  let T (n : ℕ) : Set (C(X × Y, ℝ) → ℝ) := S ∩ {L | a ≤ L (c n)}
  have hclosed (n : ℕ) : IsClosed (T n) :=
    (isClosed_compactTransportFunctionSet Lx Ly).inter
      (isClosed_le continuous_const (continuous_apply (c n)))
  have hnonempty (n : ℕ) : (T n).Nonempty := by
    obtain ⟨L, ⟨hp, h1, hx, hy⟩, ha⟩ := h n
    exact ⟨L, ⟨L.map_add, L.map_smul, hp, h1, hx, hy⟩, ha⟩
  have hstep (n : ℕ) : T (n + 1) ⊆ T n := by
    intro L hL
    refine ⟨hL.1, ?_⟩
    change a ≤ L (c n)
    let m := compactTransportLinearMap Lx Ly ⟨L, hL.1⟩
    have hpos : 0 ≤ m (c n - c (n + 1)) := hL.1.2.2.1 _
      (sub_nonneg.mpr (hc (Nat.le_succ n)))
    rw [map_sub] at hpos
    exact hL.2.trans (sub_nonneg.mp hpos)
  have hcompact : IsCompact (T 0) :=
    (isCompact_compactTransportFunctionSet Lx Ly).inter_right
      (isClosed_le continuous_const (continuous_apply (c 0)))
  obtain ⟨L, hL⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    T hstep hnonempty hcompact hclosed
  have hmem (n : ℕ) : L ∈ T n := mem_iInter.mp hL n
  have hS := (hmem 0).1
  exact ⟨compactTransportLinearMap Lx Ly ⟨L, hS⟩, hS.2.2, fun n => (hmem n).2⟩

/-- The positive continuous log truncation with threshold `exp (-n)`. -/
def compactLogTruncation {Z : Type*} [TopologicalSpace Z]
    (k : C(Z, ℂ)) (n : ℕ) : C(Z, ℝ) :=
  ⟨fun x => Real.log (max (Real.exp (-(n : ℝ))) ‖k x‖),
    (continuous_const.max k.continuous.norm).log fun x =>
      (lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ _)).ne'⟩

theorem compactLogTruncation_antitone {Z : Type*} [TopologicalSpace Z] (k : C(Z, ℂ)) :
    Antitone (compactLogTruncation k) := by
  intro m n hm x
  apply Real.log_le_log (lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ _))
  exact max_le_max (Real.exp_le_exp.mpr (neg_le_neg (Nat.cast_le.mpr hm))) le_rfl

section Measure

variable {Z : Type*} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z]
  [MeasurableSpace Z] [BorelSpace Z]

private def compactlySupportedFunctional (L : C(Z, ℝ) →ₗ[ℝ] ℝ) : C_c(Z, ℝ) →ₗ[ℝ] ℝ where
  toFun f := L f.toContinuousMap
  map_add' f g := by
    change L ((f + g).toContinuousMap) = L f.toContinuousMap + L g.toContinuousMap
    rw [show (f + g).toContinuousMap = f.toContinuousMap + g.toContinuousMap by ext z; rfl, map_add]
  map_smul' a f := by
    change L ((a • f).toContinuousMap) = a • L f.toContinuousMap
    rw [show (a • f).toContinuousMap = a • f.toContinuousMap by ext z; rfl, map_smul]

/-- The measure that represents a positive linear functional on a compact space. -/
def compactTransportMeasure (L : C(Z, ℝ) →ₗ[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ L f) : Measure Z :=
  RealRMK.rieszMeasure (Λ := compactlySupportedFunctional L) (fun f hf => hp f.toContinuousMap hf)

theorem integral_compactTransportMeasure (L : C(Z, ℝ) →ₗ[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ L f)
    (f : C(Z, ℝ)) : (∫ x, f x ∂compactTransportMeasure L hp) = L f := by
  let g : C_c(Z, ℝ) := CompactlySupportedContinuousMap.ContinuousMap.liftCompactlySupported f
  change (∫ x, g x ∂compactTransportMeasure L hp) = _
  rw [compactTransportMeasure, RealRMK.integral_rieszMeasure]
  rfl

theorem compactTransportMeasure_univ (L : C(Z, ℝ) →ₗ[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ L f)
    (h1 : L 1 = 1) : compactTransportMeasure L hp univ = 1 := by
  have h := integral_compactTransportMeasure L hp (1 : C(Z, ℝ))
  simp only [ContinuousMap.one_apply, h1, integral_const, smul_eq_mul, mul_one, measureReal_def] at h
  exact (ENNReal.toReal_eq_one_iff _).mp h

end Measure

section Marginals

variable [TopologicalSpace.PseudoMetrizableSpace X] [TopologicalSpace.PseudoMetrizableSpace Y]
  [T2Space X] [T2Space Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

/-- A transport functional with prescribed marginal integrals gives a probability coupling. -/
theorem compactTransportMeasure_marginals
    (Lx : C(X, ℝ) →ₗ[ℝ] ℝ) (Ly : C(Y, ℝ) →ₗ[ℝ] ℝ) (L : C(X × Y, ℝ) →ₗ[ℝ] ℝ)
    (hL : IsCompactTransportFunctional Lx Ly L) (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hx : ∀ f, Lx f = ∫ x, f x ∂μ) (hy : ∀ g, Ly g = ∫ y, g y ∂ν) :
    let γ := compactTransportMeasure L hL.1
    γ univ = 1 ∧ γ.map Prod.fst = μ ∧ γ.map Prod.snd = ν := by
  let γ := compactTransportMeasure L hL.1
  have hγ : γ univ = 1 := compactTransportMeasure_univ L hL.1 hL.2.1
  letI : IsProbabilityMeasure γ := ⟨hγ⟩
  refine ⟨hγ, ?_, ?_⟩
  · apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    let u : C(X, ℝ) := ⟨f, f.continuous⟩
    rw [integral_map measurable_fst.aemeasurable f.continuous.aestronglyMeasurable]
    change (∫ p, (u.comp ⟨Prod.fst, continuous_fst⟩) p ∂γ) = ∫ x, u x ∂μ
    rw [integral_compactTransportMeasure L hL.1, hL.2.2.1, hx]
  · apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro g
    let v : C(Y, ℝ) := ⟨g, g.continuous⟩
    rw [integral_map measurable_snd.aemeasurable g.continuous.aestronglyMeasurable]
    change (∫ p, (v.comp ⟨Prod.snd, continuous_snd⟩) p ∂γ) = ∫ y, v y ∂ν
    rw [integral_compactTransportMeasure L hL.1, hL.2.2.2, hy]

end Marginals

section LogIntegral

variable {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
  [MeasurableSpace Z] [OpensMeasurableSpace Z]

/-- A finite upper bound for the log modulus and all its truncations. -/
def compactLogUpperBound (k : C(Z, ℂ)) : ℝ := Real.log (max 1 ‖k‖)

theorem compactLogTruncation_le_upperBound (k : C(Z, ℂ)) (n : ℕ) (x : Z) :
    compactLogTruncation k n x ≤ compactLogUpperBound k := by
  have h₁ : Real.exp (-(n : ℝ)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))
  have h₂ : ‖k x‖ ≤ ‖k‖ := ContinuousMap.norm_coe_le_norm k x
  exact Real.log_le_log ((Real.exp_pos _).trans_le (le_max_left _ _)) (max_le_max h₁ h₂)

/-- The nonnegative deficit below a finite upper bound for the log
modulus. Its value is infinity at a kernel zero. -/
def compactLogDeficit (k : C(Z, ℂ)) (x : Z) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (compactLogUpperBound k - compactLogTruncation k n x)

theorem compactLogDeficit_of_ne_zero (k : C(Z, ℂ)) (x : Z) (hx : k x ≠ 0) :
    compactLogDeficit k x = ENNReal.ofReal (compactLogUpperBound k - Real.log ‖k x‖) := by
  have hpos : 0 < ‖k x‖ := norm_pos_iff.mpr hx
  apply le_antisymm
  · apply iSup_le
    intro n
    apply ENNReal.ofReal_le_ofReal
    apply sub_le_sub_left
    exact Real.log_le_log hpos (le_max_right _ _)
  · obtain ⟨n, hn⟩ := exists_nat_gt (-Real.log ‖k x‖)
    have hn' : Real.exp (-(n : ℝ)) ≤ ‖k x‖ :=
      (Real.le_log_iff_exp_le hpos).mp (by linarith only [hn])
    have he : compactLogTruncation k n x = Real.log ‖k x‖ := by
      change Real.log (max (Real.exp (-(n : ℝ))) ‖k x‖) = _
      rw [max_eq_right hn']
    rw [← he]
    exact le_iSup (fun m : ℕ => ENNReal.ofReal
      (compactLogUpperBound k - compactLogTruncation k m x)) n

theorem compactLogDeficit_of_zero (k : C(Z, ℂ)) (x : Z) (hx : k x = 0) :
    compactLogDeficit k x = ⊤ := by
  have hM : 0 ≤ compactLogUpperBound k := Real.log_nonneg (le_max_left _ _)
  apply top_unique
  rw [← ENNReal.iSup_natCast]
  apply iSup_le
  intro n
  refine le_iSup_of_le n ?_
  change (n : ℝ≥0∞) ≤ ENNReal.ofReal (compactLogUpperBound k -
    Real.log (max (Real.exp (-(n : ℝ))) ‖k x‖))
  rw [hx, norm_zero, max_eq_left (Real.exp_pos _).le, Real.log_exp, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (by linarith only [hM])

/-- The extended integral of the log modulus under a probability
measure. Subtract the nonnegative deficit from the chosen upper bound. -/
def compactLogModulusIntegral (k : C(Z, ℂ)) (γ : Measure Z) : EReal :=
  (compactLogUpperBound k : EReal) - ((∫⁻ x, compactLogDeficit k x ∂γ) : EReal)

/-- A common lower bound on the truncation integrals bounds the extended log integral. -/
theorem le_compactLogModulusIntegral_of_truncations (k : C(Z, ℂ)) (γ : Measure Z)
    [IsProbabilityMeasure γ] (a : ℝ) (h : ∀ n, a ≤ ∫ x, compactLogTruncation k n x ∂γ) :
    (a : EReal) ≤ compactLogModulusIntegral k γ := by
  let M := compactLogUpperBound k
  let c (n : ℕ) := compactLogTruncation k n
  have hci (n : ℕ) : Integrable (c n) γ := (c n).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hbound (n : ℕ) : (∫ x, c n x ∂γ) ≤ M := by
    have hl := integral_mono (hci n) (integrable_const M)
      (compactLogTruncation_le_upperBound k n)
    simpa only [integral_const, measureReal_univ_eq_one, one_smul] using hl
  have haM : a ≤ M := (h 0).trans (hbound 0)
  let d (n : ℕ) (x : Z) := ENNReal.ofReal (M - c n x)
  have hd (n : ℕ) : Measurable (d n) :=
    (measurable_const.sub (c n).continuous.measurable).ennreal_ofReal
  have hdmono : Monotone d := by
    intro n m hn x
    exact ENNReal.ofReal_le_ofReal (sub_le_sub_left (compactLogTruncation_antitone k hn x) M)
  have hi : (∫⁻ x, compactLogDeficit k x ∂γ) ≤ ENNReal.ofReal (M - a) := by
    unfold compactLogDeficit
    change (∫⁻ x, ⨆ n, d n x ∂γ) ≤ _
    rw [lintegral_iSup hd hdmono]
    apply iSup_le
    intro n
    have hpos : 0 ≤ᵐ[γ] fun x => M - c n x :=
      ae_of_all _ fun x => sub_nonneg.mpr (compactLogTruncation_le_upperBound k n x)
    change (∫⁻ x, ENNReal.ofReal (M - c n x) ∂γ) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal
      (show Integrable (fun x => M - c n x) γ from (integrable_const M).sub (hci n)) hpos,
      integral_sub (integrable_const M) (hci n), integral_const, measureReal_univ_eq_one, one_smul]
    exact ENNReal.ofReal_le_ofReal (sub_le_sub_left (h n) M)
  have he : ((∫⁻ x, compactLogDeficit k x ∂γ) : EReal) ≤ ((M - a : ℝ) : EReal) := by
    have hc := EReal.coe_ennreal_le_coe_ennreal_iff.mpr hi
    rw [EReal.coe_ennreal_ofReal, max_eq_left (sub_nonneg.mpr haM)] at hc
    exact hc
  have hsub : (M : EReal) + -((M - a : ℝ) : EReal) ≤
      (M : EReal) + -((∫⁻ x, compactLogDeficit k x ∂γ) : EReal) :=
    add_le_add le_rfl (EReal.neg_le_neg_iff.mpr he)
  rw [← EReal.coe_neg, ← EReal.coe_add, show M + -(M - a) = a by ring] at hsub
  exact hsub

end LogIntegral

end

end MOC
