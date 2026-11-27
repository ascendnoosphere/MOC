import MOC.SecularChamberSpectrum
import MOC.WeightedSecularChamberMaximum
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.MetricSpace.Sequences

/-! The open positive-residue domain, its finite boundary, and a barrier
that controls all unbounded sequences in the domain. -/

open BigOperators Finset Filter Set Polynomial
open scoped Topology

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The distinct diagonal nodes that produce strictly positive residues
for a fixed spectral list. -/
def secularChamber (h : ι → ℝ) : Set (ι → ℝ) :=
  { d | Function.Injective d ∧ ∀ i, 0 < secularResidue h d i }

private theorem continuousAt_secularResidue (h d : ι → ℝ)
    (hd : Function.Injective d) (i : ι) :
    ContinuousAt (fun p => secularResidue h p i) d := by
  have hn : Continuous (fun p : ι → ℝ => -(∏ j, (p i-h j))) := by
    exact (continuous_finset_prod _ fun j _ => (continuous_apply i).sub continuous_const).neg
  have hD : Continuous (fun p : ι → ℝ => ∏ j ∈ univ.erase i, (p i-p j)) :=
    continuous_finset_prod _ fun j _ => (continuous_apply i).sub (continuous_apply j)
  have hne : (∏ j ∈ univ.erase i, (d i - d j)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr (hd.ne (Ne.symm (ne_of_mem_erase hj)))
  exact hn.continuousAt.div hD.continuousAt hne

theorem isOpen_secularChamber (h : ι → ℝ) : IsOpen (secularChamber h) := by
  apply isOpen_iff_mem_nhds.mpr
  intro d hd
  have hi : ∀ᶠ p : ι → ℝ in 𝓝 d, ∀ i j, i ≠ j → p i ≠ p j := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases h : i = j
    · exact Eventually.of_forall fun _ hn => (hn h).elim
    · have hO : IsOpen {p : ι → ℝ | p i ≠ p j} :=
        isOpen_ne_fun (continuous_apply i) (continuous_apply j)
      have hx : ∀ᶠ p : ι → ℝ in 𝓝 d, p i ≠ p j := hO.mem_nhds (hd.1.ne h)
      exact hx.mono fun _ hp _ => hp
  have hr : ∀ᶠ p : ι → ℝ in 𝓝 d, ∀ i, 0 < secularResidue h p i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (continuousAt_secularResidue h d hd.1 i).tendsto.eventually (Ioi_mem_nhds (hd.2 i))
  filter_upwards [hi, hr] with p hp hR
  exact ⟨fun _ _ he => by_contra fun hn => (hp _ _ hn) he, hR⟩

theorem continuousOn_secularResidues (h : ι → ℝ) :
    ContinuousOn (secularResidue h) (secularChamber h) := by
  intro d hd
  apply continuousWithinAt_pi.mpr
  intro i
  exact (continuousAt_secularResidue h d hd.1 i).continuousWithinAt

theorem secularCharacteristic_eq_spectrum_of_chamber (h d : ι → ℝ)
    (hd : d ∈ secularChamber h) :
    secularCharacteristic d (secularResidue h d) = ∏ i, (X - C (h i)) := by
  unfold secularCharacteristic
  rw [← secular_polynomial_identity h d hd.1]
  abel

theorem secular_residues_unique_of_distinct_nodes (d r h : ι → ℝ)
    (hd : Function.Injective d)
    (hp : secularCharacteristic d r = ∏ i, (X - C (h i))) :
    r = secularResidue h d := by
  funext i
  have he := congrArg (Polynomial.eval (d i)) hp
  simp only [eval_secularCharacteristic_at_node d r i, eval_prod, eval_sub, eval_X, eval_C] at he
  have hn : (∏ j ∈ univ.erase i, (d i - d j)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr (hd.ne (Ne.symm (ne_of_mem_erase hj)))
  apply (eq_div_iff hn).mpr
  linarith only [he]

private theorem continuous_secularCharacteristic_evaluation (z : ℝ) :
    Continuous (fun p : (ι → ℝ) × (ι → ℝ) => (secularCharacteristic p.1 p.2).eval z) := by
  unfold secularCharacteristic
  simp only [eval_sub, eval_prod, eval_X, eval_C, eval_finset_sum, eval_mul]
  exact (continuous_finset_prod _ fun i _ => continuous_const.sub ((continuous_apply i).comp continuous_fst)).sub
    (continuous_finset_sum _ fun i _ => ((continuous_apply i).comp continuous_snd).mul
      (continuous_finset_prod _ fun j _ => continuous_const.sub ((continuous_apply j).comp continuous_fst)))

/-- A convergent sequence of nodes in the chamber has a subsequence
whose residues converge and satisfy the fixed characteristic equation. -/
theorem secular_chamber_sequence_boundary (h : ι → ℝ)
    (d : ℕ → ι → ℝ) (hd : ∀ n, d n ∈ secularChamber h)
    (p : ι → ℝ) (hp : Tendsto d atTop (𝓝 p)) :
    ∃ (r : ι → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun n => secularResidue h (d (φ n))) atTop (𝓝 r) ∧
      (∀ i, 0 ≤ r i) ∧ (secularCharacteristic p r = ∏ i, (X - C (h i))) := by
  let R (n : ℕ) := secularResidue h (d n)
  have hsum : Tendsto (fun n => ∑ i, d n i) atTop (𝓝 (∑ i, p i)) :=
    tendsto_finset_sum _ fun i _ => ((continuous_apply i).continuousAt.tendsto.comp hp)
  obtain ⟨L, hL⟩ := hsum.bddBelow_range
  let Bnd := max 0 ((∑ i, h i)-L)
  have hC : 0 ≤ Bnd := le_max_left _ _
  have hr (n : ℕ) (i : ι) : 0 ≤ R n i := ((hd n).2 i).le
  have hbound (n : ℕ) : ‖R n‖ ≤ Bnd := by
    apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hr n i)]
    have hupper : R n i ≤ ∑ j, R n j :=
      Finset.single_le_sum (f := R n) (fun j _ => hr n j) (mem_univ i)
    have hsumR := sum_secularResidue h (d n) (hd n).1
    have hLb : L ≤ ∑ j, d n j := hL (Set.mem_range_self n)
    change R n i ≤ Bnd
    exact hupper.trans ((le_of_eq hsumR).trans ((sub_le_sub_left hLb _).trans (le_max_right _ _)))
  have hB : Bornology.IsBounded (Set.range R) :=
    isBounded_iff_forall_norm_le.mpr ⟨Bnd, fun _ ⟨n, hn⟩ => hn ▸ hbound n⟩
  obtain ⟨r, _, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hB (fun n => Set.mem_range_self n)
  refine ⟨r, φ, hφ, hlim, ?_, ?_⟩
  · intro i
    have hi : Tendsto (fun n => R (φ n) i) atTop (𝓝 (r i)) :=
      (continuous_apply i).continuousAt.tendsto.comp hlim
    exact ge_of_tendsto hi (Eventually.of_forall fun n => hr (φ n) i)
  · apply Polynomial.funext
    intro z
    have hDL : Tendsto (d ∘ φ) atTop (𝓝 p) := hp.comp hφ.tendsto_atTop
    have hpair := hDL.prodMk_nhds hlim
    have hF := ((continuous_secularCharacteristic_evaluation (ι := ι) z).continuousAt.tendsto.comp hpair)
    have hC : Tendsto (fun _ : ℕ => (∏ i, (X - C (h i))).eval z) atTop
        (𝓝 ((∏ i, (X - C (h i))).eval z)) := tendsto_const_nhds
    apply tendsto_nhds_unique hF
    apply hC.congr'
    exact Eventually.of_forall fun n => by
      change _ = (secularCharacteristic (d (φ n)) (R (φ n))).eval z
      rw [secularCharacteristic_eq_spectrum_of_chamber h (d (φ n)) (hd (φ n))]

/-- A boundary point with an admissible limiting residue vector has
either a node collision or a zero residue. -/
theorem missing_secular_chamber_has_collision_or_zero (h d r : ι → ℝ)
    (hd : d ∉ secularChamber h) (hr : ∀ i, 0 ≤ r i)
    (hp : secularCharacteristic d r = ∏ i, (X - C (h i))) :
    ¬ Function.Injective d ∨ ∃ i, r i = 0 := by
  classical
  by_cases hi : Function.Injective d
  · right
    have he := secular_residues_unique_of_distinct_nodes d r h hi hp
    by_contra! hpos
    apply hd
    exact ⟨hi, fun i => he ▸ lt_of_le_of_ne (hr i) (Ne.symm (hpos i))⟩
  · exact Or.inl hi

/-- A strictly convex coordinate barrier that goes to negative infinity
whenever any diagonal node does so. -/
def secularBarrier (U : ℝ) (d : ι → ℝ) : ℝ :=
  ∑ i, (d i-U + Real.exp (d i-U) - 1)

omit [DecidableEq ι] in
private theorem continuous_secularBarrier (U : ℝ) :
    Continuous (secularBarrier (ι := ι) U) := by
  unfold secularBarrier
  exact continuous_finset_sum _ fun i _ => by fun_prop

private theorem secularBarrier_le_coordinate (U : ℝ) (d : ι → ℝ)
    (hd : ∀ i, d i ≤ U) (i : ι) :
    secularBarrier U d ≤ d i-U := by
  let f (j : ι) := d j-U + Real.exp (d j-U) - 1
  have he (j : ι) : Real.exp (d j-U) ≤ 1 := Real.exp_le_one_iff.mpr (sub_nonpos.mpr (hd j))
  have hf (j : ι) : f j ≤ 0 := by dsimp only [f]; linarith only [hd j, he j]
  change (∑ j, f j) ≤ _
  rw [← sum_erase_add univ f (mem_univ i)]
  have hn : (∑ j ∈ univ.erase i, f j) ≤ 0 := sum_nonpos fun j _ => hf j
  dsimp only [f] at hn ⊢
  linarith only [hn, he i]

omit [DecidableEq ι] in
private theorem secularBarrier_nonpos (U : ℝ) (d : ι → ℝ) (hd : ∀ i, d i ≤ U) :
    secularBarrier U d ≤ 0 := by
  unfold secularBarrier
  apply sum_nonpos
  intro i _
  have he := Real.exp_le_one_iff.mpr (sub_nonpos.mpr (hd i))
  linarith only [hd i, he]

private theorem hasDerivAt_secularBarrier_coordinate (U : ℝ) (d : ι → ℝ) (i : ι) (z : ℝ) :
    HasDerivAt (fun t => secularBarrier U (Function.update d i t))
      (1 + Real.exp (z-U)) z := by
  let c := ∑ j ∈ univ.erase i, (d j-U + Real.exp (d j-U) - 1)
  have he : (fun t => secularBarrier U (Function.update d i t)) =
      (fun t => c + (t-U + Real.exp (t-U) - 1)) := by
    funext t
    unfold secularBarrier
    rw [← sum_erase_add univ (fun j => Function.update d i t j-U +
      Real.exp (Function.update d i t j-U)-1) (mem_univ i), Function.update_self]
    congr 1
    exact sum_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]
  rw [he]
  have hd := (hasDerivAt_id' z).sub_const U
  have hx := (Real.hasDerivAt_exp (z-U)).comp z hd
  simpa only [Function.comp_def, mul_one] using (((hd.add hx).sub_const 1).const_add c)

private theorem hasSecondDerivAt_secularBarrier_coordinate (U : ℝ) (d : ι → ℝ)
    (i : ι) :
    HasDerivAt (deriv (fun t => secularBarrier U (Function.update d i t)))
      (Real.exp (d i-U)) (d i) := by
  rw [show deriv (fun t => secularBarrier U (Function.update d i t)) =
    (fun t => 1 + Real.exp (t-U)) from
      funext fun t => (hasDerivAt_secularBarrier_coordinate U d i t).deriv]
  have h := (Real.hasDerivAt_exp (d i-U)).comp (d i) ((hasDerivAt_id' (d i)).sub_const U)
  simpa only [Function.comp_def, mul_one] using h.const_add 1

/-- A bounded weighted harmonic function of the secular node and
residue data is bounded by its values at collisions or zero residues. -/
theorem secularChamber_harmonic_bound [Nonempty ι] (h : ι → ℝ)
    (F : (ι → ℝ) × (ι → ℝ) → ℝ) (hF : Continuous F) (M B U : ℝ)
    (hU : ∀ i, h i < U)
    (hB : ∀ d ∈ secularChamber h, F (d, secularResidue h d) ≤ B)
    (hBoundary : ∀ d r : ι → ℝ, (∀ i, 0 ≤ r i) →
      secularCharacteristic d r = (∏ i, (X - C (h i))) →
      (¬ Function.Injective d ∨ ∃ i, r i = 0) → F (d,r) ≤ M)
    (hnear : ∀ d ∈ secularChamber h, ∀ i, ∀ᶠ t in 𝓝 (d i),
      DifferentiableAt ℝ (fun s => F (Function.update d i s,
        secularResidue h (Function.update d i s))) t)
    (hsecond : ∀ d ∈ secularChamber h, ∀ i, DifferentiableAt ℝ
      (deriv (fun s => F (Function.update d i s, secularResidue h (Function.update d i s)))) (d i))
    (hzero : ∀ d ∈ secularChamber h, (∑ i, secularResidue h d i *
      deriv (deriv (fun s => F (Function.update d i s, secularResidue h (Function.update d i s))))
        (d i)) = 0) :
    ∀ d ∈ secularChamber h, F (d, secularResidue h d) ≤ M := by
  classical
  let Ω := secularChamber h
  let f (d : ι → ℝ) := F (d,secularResidue h d)
  let phi := secularBarrier (ι := ι) U
  have hΩ : IsOpen Ω := isOpen_secularChamber h
  have hc : ContinuousOn f Ω :=
    hF.continuousOn.comp (continuousOn_id.prodMk (continuousOn_secularResidues h))
      (fun _ _ => Set.mem_univ _)
  have hnod (d : ι → ℝ) (hd : d ∈ Ω) (i : ι) : d i ≤ U :=
    (secular_nodes_lt_spectral_upper_bound d (secularResidue h d) h (fun j => (hd.2 j).le)
      (secularCharacteristic_eq_spectrum_of_chamber h d hd) U hU i).le
  apply weighted_coordinate_harmonic_bound_of_barrier f phi Ω hΩ M (secularResidue h)
    (fun d hd i => (hd.2 i).le) hc (continuous_secularBarrier U).continuousOn
  · intro d hd i
    filter_upwards [hnear d hd i] with t ht using
      ⟨ht, (hasDerivAt_secularBarrier_coordinate U d i t).differentiableAt⟩
  · exact hsecond
  · exact fun d _ i => (hasSecondDerivAt_secularBarrier_coordinate U d i).differentiableAt
  · exact hzero
  · intro d hd
    change 0 < ∑ i, secularResidue h d i *
      deriv (deriv (fun t => secularBarrier U (Function.update d i t))) (d i)
    simp_rw [(hasSecondDerivAt_secularBarrier_coordinate U d _).deriv]
    exact sum_pos (fun i _ => mul_pos (hd.2 i) (Real.exp_pos _)) univ_nonempty
  · intro ε hε a ha
    let g (d : ι → ℝ) := f d + ε * phi d
    apply compact_superlevel_of_boundary_exclusion g Ω (hc.add (continuousOn_const.mul
      (continuous_secularBarrier U).continuousOn)) a
    · apply isBounded_iff_forall_norm_le.mpr
      let L := (a-B)/ε + U
      refine ⟨|L| + |U|, fun d hd => (pi_norm_le_iff_of_nonneg (add_nonneg
        (abs_nonneg L) (abs_nonneg U))).mpr ?_⟩
      intro i
      have hi : d i ≤ U := hnod d hd.1 i
      have hphi : phi d ≤ d i-U := secularBarrier_le_coordinate U d (hnod d hd.1) i
      have hf : f d ≤ B := hB d hd.1
      have hge : a ≤ f d + ε * phi d := hd.2
      have hL : L ≤ d i := by
        dsimp only [L]
        have ht : (a-B)/ε ≤ d i-U := by
          apply (div_le_iff₀ hε).mpr
          nlinarith only [hf, hge, mul_le_mul_of_nonneg_left hphi hε.le]
        linarith only [ht]
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith only [hL, neg_abs_le L, abs_nonneg U]
      · linarith only [hi, le_abs_self U, abs_nonneg L]
    · intro p hp hpΩ
      refine Classical.byContradiction fun hbad => ?_
      have hfreq : ∃ᶠ d in 𝓝[Ω] p, a ≤ g d := by
        change ¬ ∀ᶠ d in 𝓝[Ω] p, ¬ a ≤ g d
        simpa only [not_le] using hbad
      have hpS : p ∈ closure {d ∈ Ω | a ≤ g d} :=
        mem_closure_iff_frequently.mpr
          ((frequently_nhdsWithin_iff.mp hfreq).mono fun _ h => ⟨h.2,h.1⟩)
      obtain ⟨d, hS, hdl⟩ := mem_closure_iff_seq_limit.mp hpS
      obtain ⟨r, ψ, hψ, hr, hr₀, hpoly⟩ := secular_chamber_sequence_boundary h d
        (fun n => (hS n).1) p hdl
      have hf : F (p,r) ≤ M := hBoundary p r hr₀ hpoly
        (missing_secular_chamber_has_collision_or_zero h p r hpΩ hr₀ hpoly)
      have hdψ : Tendsto (d ∘ ψ) atTop (𝓝 p) := hdl.comp hψ.tendsto_atTop
      have hpair := hdψ.prodMk_nhds hr
      have hfl := hF.continuousAt.tendsto.comp hpair
      have hpl := (continuous_secularBarrier (ι := ι) U).continuousAt.tendsto.comp hdψ
      have hgl : Tendsto (g ∘ d ∘ ψ) atTop (𝓝 (F (p,r) + ε*phi p)) :=
        hfl.add (hpl.const_mul ε)
      have hA : a ≤ F (p,r) + ε*phi p := ge_of_tendsto hgl
        (Eventually.of_forall fun n => (hS (ψ n)).2)
      have hpu (i : ι) : p i ≤ U := le_of_tendsto
        (((continuous_apply i).continuousAt.tendsto).comp hdψ)
        (Eventually.of_forall fun n => hnod (d (ψ n)) (hS (ψ n)).1 i)
      have hP : phi p ≤ 0 := secularBarrier_nonpos U p hpu
      linarith only [hf, hA, ha, mul_nonpos_of_nonneg_of_nonpos hε.le hP]

end

end MOC
