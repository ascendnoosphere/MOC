import MOC.FiniteEntropyDuality
import MOC.TracialLogConjugation
import MOC.TracialSpectralScaling

/-! Entropic transport for an ordered kernel on two finite spectral partitions. -/

open BigOperators

namespace MOC

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable (τ : A →L[ℂ] ℂ) (P : SpectralProjectionPartition ι A)
  (Q : SpectralProjectionPartition κ A) (K : ι → κ → ℂ)

/-- The overlap of two projections times the squared modulus of the kernel entry. -/
def tracialKernelWeight (i : ι) (j : κ) : ℝ :=
  tracialProjectionOverlap τ P Q i j * Complex.normSq (K i j)

/-- A cell in the support has nonzero overlap and nonzero kernel entry. -/
abbrev TracialKernelSupport :=
  {e : ι × κ // tracialKernelWeight τ P Q K e.1 e.2 ≠ 0}

/-- A probability vector on the support with row and column masses given by the trace. -/
def IsTracialKernelCoupling (q : TracialKernelSupport τ P Q K → ℝ) : Prop :=
  q ∈ stdSimplex ℝ (TracialKernelSupport τ P Q K) ∧
    (∀ i, (∑ e : TracialKernelSupport τ P Q K, if e.val.1 = i then q e else 0) =
      (τ (P.proj i)).re) ∧
    (∀ j, (∑ e : TracialKernelSupport τ P Q K, if e.val.2 = j then q e else 0) =
      (τ (Q.proj j)).re)

/-- The mean logarithm of the modulus of the supported kernel entries. -/
def tracialKernelMeanLogModulus (q : TracialKernelSupport τ P Q K → ℝ) : ℝ :=
  ∑ e, q e * Real.log ‖K e.val.1 e.val.2‖

/-- The relative entropy of a supported law with respect to the trace overlaps. -/
def tracialKernelRelativeEntropy (q : TracialKernelSupport τ P Q K → ℝ) : ℝ :=
  ∑ e, q e * Real.log (q e / tracialProjectionOverlap τ P Q e.val.1 e.val.2)

/-- The mean log modulus minus half the relative entropy with respect to the overlaps. -/
def tracialKernelEntropyObjective (q : TracialKernelSupport τ P Q K → ℝ) : ℝ :=
  tracialKernelMeanLogModulus τ P Q K q - tracialKernelRelativeEntropy τ P Q K q / 2

private theorem tracialKernelWeight_pos (hτ : IsNormalizedTracialState τ)
    (e : TracialKernelSupport τ P Q K) : 0 < tracialKernelWeight τ P Q K e.val.1 e.val.2 :=
  lt_of_le_of_ne (mul_nonneg ((tracialProjectionOverlap_coupling τ hτ P Q).1 _ _)
    (Complex.normSq_nonneg _)) e.property.symm

private theorem sum_tracialKernelSupport (b : ι → κ → ℝ) :
    (∑ e : TracialKernelSupport τ P Q K,
      tracialKernelWeight τ P Q K e.val.1 e.val.2 * b e.val.1 e.val.2) =
      ∑ i, ∑ j, tracialKernelWeight τ P Q K i j * b i j := by
  classical
  let w (e : ι × κ) := tracialKernelWeight τ P Q K e.1 e.2
  change (∑ e : {e : ι × κ // w e ≠ 0}, w e.val * b e.val.1 e.val.2) =
    ∑ i, ∑ j, w (i, j) * b i j
  rw [← Fintype.sum_prod_type (fun e : ι × κ => w e * b e.1 e.2),
    ← Finset.subtype_univ (fun e : ι × κ => w e ≠ 0),
    Finset.sum_subtype_eq_sum_filter (f := fun e : ι × κ => w e * b e.1 e.2),
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : w e = 0 <;> simp [he]

private theorem tracialKernelSupport_nonempty (hτ : IsNormalizedTracialState τ) (a : ℝ)
    (ha : (a : EReal) ≤ fugledeKadisonLog τ (tracialSpectralKernel P Q K)) :
    Nonempty (TracialKernelSupport τ P Q K) := by
  by_contra hempty
  have hzero (i : ι) (j : κ) : tracialKernelWeight τ P Q K i j = 0 := by
    by_contra h
    exact hempty ⟨⟨(i, j), h⟩⟩
  have hgram : (τ (star (tracialSpectralKernel P Q K) * tracialSpectralKernel P Q K)).re = 0 := by
    rw [tracialSpectralKernel_gram_trace τ hτ]
    change (∑ i, ∑ j, tracialKernelWeight τ P Q K i j) = 0
    simp only [hzero, Finset.sum_const_zero]
  rw [fugledeKadisonLog_eq_bot_of_gram_trace_eq_zero τ hτ _ hgram] at ha
  exact (EReal.bot_lt_coe a).not_ge ha

private def potentialScaling (u : ι → ℝ) : A :=
  ∑ i, (Real.exp (-u i / 2) : ℂ) • P.proj i

private theorem potentialScaling_log_mul (hτ : IsNormalizedTracialState τ) (u : ι → ℝ) (T : A) :
    let D := potentialScaling P u
    let c := -(∑ i, (τ (P.proj i)).re * u i) / 2
    fugledeKadisonLog τ (T * D) = fugledeKadisonLog τ T + (c : EReal) ∧
      fugledeKadisonLog τ (D * T) = fugledeKadisonLog τ T + (c : EReal) := by
  let d (i : ι) := Real.exp (-u i / 2)
  have hd (i : ι) : 0 < d i := Real.exp_pos _
  let D := potentialScaling P u
  have hD : IsSelfAdjoint D := P.scale_selfAdjoint d
  have hDp : ∀ x ∈ spectrum ℝ D, 0 < x := P.scale_spectrum_pos d hd
  have h := fugledeKadisonLog_mul_of_strict_positive τ hτ D T hD hDp
  have htrace : (τ (CFC.log D)).re = -(∑ i, (τ (P.proj i)).re * u i) / 2 := by
    have hterm (i : ι) :
        Real.log (d i) * (τ (P.proj i)).re = -((τ (P.proj i)).re * u i) / 2 := by
      rw [show Real.log (d i) = -u i / 2 from Real.log_exp _]
      ring
    change (τ (CFC.log (∑ i, (d i : ℂ) • P.proj i))).re = _
    rw [P.trace_log_scale d hd τ]
    simp only [hterm, ← Finset.sum_div, Finset.sum_neg_distrib]
  rwa [htrace] at h

/-- Row and column potentials bound twice each real lower bound for the determinant logarithm. -/
theorem tracialSpectralKernel_potential_bound (hτ : IsNormalizedTracialState τ) (a : ℝ)
    (ha : (a : EReal) ≤ fugledeKadisonLog τ (tracialSpectralKernel P Q K))
    (u : ι → ℝ) (v : κ → ℝ) :
    2 * a ≤ (∑ i, (τ (P.proj i)).re * u i) + (∑ j, (τ (Q.proj j)).re * v j) +
      Real.log (∑ e : TracialKernelSupport τ P Q K,
        tracialKernelWeight τ P Q K e.val.1 e.val.2 * Real.exp (-(u e.val.1 + v e.val.2))) := by
  classical
  let T := tracialSpectralKernel P Q K
  let L := potentialScaling P u
  let R := potentialScaling Q v
  let scaled (i : ι) (j : κ) := (Real.exp (-u i / 2) : ℂ) * K i j * (Real.exp (-v j / 2) : ℂ)
  let S := tracialSpectralKernel P Q scaled
  let Z := ∑ e : TracialKernelSupport τ P Q K,
    tracialKernelWeight τ P Q K e.val.1 e.val.2 * Real.exp (-(u e.val.1 + v e.val.2))
  haveI : Nonempty (TracialKernelSupport τ P Q K) := tracialKernelSupport_nonempty τ P Q K hτ a ha
  have hZ : 0 < Z := Finset.sum_pos (fun e _ =>
    mul_pos (tracialKernelWeight_pos τ P Q K hτ e) (Real.exp_pos _)) Finset.univ_nonempty
  have hscale : L * T * R = S := tracialSpectralKernel_scale P Q K _ _
  have hright := (potentialScaling_log_mul τ Q hτ v (L * T)).1
  have hleft := (potentialScaling_log_mul τ P hτ u T).2
  let ru := ∑ i, (τ (P.proj i)).re * u i
  let sv := ∑ j, (τ (Q.proj j)).re * v j
  have hlower : ((a + -ru / 2 + -sv / 2 : ℝ) : EReal) ≤ fugledeKadisonLog τ S := by
    rw [← hscale, hright, hleft, EReal.coe_add, EReal.coe_add]
    exact add_le_add_right (add_le_add_right ha _) _
  have hsquare (x : ℝ) : Real.exp (-x / 2) * Real.exp (-x / 2) = Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hterm (i : ι) (j : κ) :
      Complex.normSq (scaled i j) = Complex.normSq (K i j) * Real.exp (-(u i + v j)) := by
    simp only [scaled, map_mul, Complex.normSq_ofReal, hsquare, neg_add, Real.exp_add]
    ring
  have hgram : (τ (star S * S)).re = Z := by
    rw [tracialSpectralKernel_gram_trace τ hτ P Q scaled]
    dsimp only [Z]
    rw [sum_tracialKernelSupport τ P Q K (fun i j => Real.exp (-(u i + v j)))]
    simp only [hterm, tracialKernelWeight, mul_assoc]
  have hupper := fugledeKadisonLog_le_log_trace_bound τ hτ S Z hZ hgram.le
  have hreal := EReal.coe_le_coe_iff.mp (hlower.trans hupper)
  change 2 * a ≤ ru + sv + Real.log Z
  linarith only [hreal]

private theorem tracialKernelEntropyObjective_eq (q : TracialKernelSupport τ P Q K → ℝ) :
    finiteEntropyScore (fun e : TracialKernelSupport τ P Q K =>
      tracialKernelWeight τ P Q K e.val.1 e.val.2) q / 2 = tracialKernelEntropyObjective τ P Q K q := by
  let p (e : TracialKernelSupport τ P Q K) := tracialProjectionOverlap τ P Q e.val.1 e.val.2
  let k (e : TracialKernelSupport τ P Q K) := ‖K e.val.1 e.val.2‖
  have hterm (e : TracialKernelSupport τ P Q K) :
      q e * Real.log (tracialKernelWeight τ P Q K e.val.1 e.val.2) + Real.negMulLog (q e) =
        2 * (q e * Real.log (k e)) - q e * Real.log (q e / p e) := by
    have hw : p e * k e ^ 2 ≠ 0 := by
      simpa only [p, k, ← Complex.normSq_eq_norm_sq, tracialKernelWeight] using e.property
    have hp := left_ne_zero_of_mul hw
    have hk := right_ne_zero_of_mul hw
    by_cases hq : q e = 0
    · simp [hq]
    change q e * Real.log (p e * Complex.normSq (K e.val.1 e.val.2)) + _ = _
    rw [Complex.normSq_eq_norm_sq, Real.log_mul hp hk, Real.log_pow,
      Real.log_div hq hp, Real.negMulLog_eq_neg]
    dsimp only [k]
    push_cast
    ring
  simp only [finiteEntropyScore, tracialKernelEntropyObjective, tracialKernelMeanLogModulus,
    tracialKernelRelativeEntropy, hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, k, p]
  ring

/-- Each finite lower bound for the determinant logarithm is attained or exceeded by
the entropy objective of a coupling with the prescribed spectral masses. -/
theorem exists_tracial_entropic_transport (hτ : IsNormalizedTracialState τ) (a : ℝ)
    (ha : (a : EReal) ≤ fugledeKadisonLog τ (tracialSpectralKernel P Q K)) :
    ∃ q, IsTracialKernelCoupling τ P Q K q ∧ a ≤ tracialKernelEntropyObjective τ P Q K q := by
  classical
  let C := TracialKernelSupport τ P Q K
  haveI : Nonempty C := tracialKernelSupport_nonempty τ P Q K hτ a ha
  let E := ι ⊕ κ → ℝ
  let L (i : ι) : E := Pi.single (Sum.inl i) 1
  let R (j : κ) : E := Pi.single (Sum.inr j) 1
  let g (e : C) := L e.val.1 + R e.val.2
  let w (e : C) := tracialKernelWeight τ P Q K e.val.1 e.val.2
  let m : E := (∑ i, (τ (P.proj i)).re • L i) + ∑ j, (τ (Q.proj j)).re • R j
  have hgL (e : C) (i : ι) : g e (Sum.inl i) = if e.val.1 = i then 1 else 0 := by
    simp [g, L, R, Pi.single_apply, eq_comm]
  have hgR (e : C) (j : κ) : g e (Sum.inr j) = if e.val.2 = j then 1 else 0 := by
    simp [g, L, R, Pi.single_apply, eq_comm]
  have hmL (i : ι) : m (Sum.inl i) = (τ (P.proj i)).re := by
    simp [m, L, R, Pi.single_apply, smul_eq_mul, mul_ite]
  have hmR (j : κ) : m (Sum.inr j) = (τ (Q.proj j)).re := by
    simp [m, L, R, Pi.single_apply, smul_eq_mul, mul_ite]
  have hbound (f : E →L[ℝ] ℝ) :
      2 * a ≤ f m + Real.log (∑ e, w e * Real.exp (-f (g e))) := by
    let u (i : ι) := f (L i)
    let v (j : κ) := f (R j)
    have hf : f m = (∑ i, (τ (P.proj i)).re * u i) + ∑ j, (τ (Q.proj j)).re * v j := by
      simp only [m, map_add, map_sum, map_smul, smul_eq_mul, u, v]
    have hg (e : C) : f (g e) = u e.val.1 + v e.val.2 := map_add f _ _
    simp only [hf, hg, w]
    exact tracialSpectralKernel_potential_bound τ P Q K hτ a ha u v
  obtain ⟨q, hq, hm, hs⟩ := exists_finiteEntropyScore_of_all_potential_bounds
    g w (tracialKernelWeight_pos τ P Q K hτ) m (2 * a) hbound
  refine ⟨q, ⟨hq, fun i => ?_, fun j => ?_⟩, ?_⟩
  · have hi := congrFun hm (Sum.inl i)
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hgL, mul_ite, mul_one,
      mul_zero, hmL] using hi
  · have hj := congrFun hm (Sum.inr j)
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hgR, mul_ite, mul_one,
      mul_zero, hmR] using hj
  · rw [← tracialKernelEntropyObjective_eq τ P Q K q]
    change a ≤ finiteEntropyScore w q / 2
    linarith only [hs]

/-- The Fuglede–Kadison determinant logarithm of an ordered spectral kernel is at most
the supremum of the entropy objectives. The empty set of couplings has supremum minus infinity. -/
theorem fugledeKadisonLog_spectralKernel_le_entropic_transport (hτ : IsNormalizedTracialState τ) :
    fugledeKadisonLog τ (tracialSpectralKernel P Q K) ≤
      sSup {h : EReal | ∃ q, IsTracialKernelCoupling τ P Q K q ∧
        h = (tracialKernelEntropyObjective τ P Q K q : EReal)} := by
  let T := tracialSpectralKernel P Q K
  by_cases hbot : fugledeKadisonLog τ T = ⊥
  · rw [show fugledeKadisonLog τ (tracialSpectralKernel P Q K) = ⊥ from hbot]
    exact bot_le
  have htop : fugledeKadisonLog τ T ≠ ⊤ := by
    apply ne_of_lt
    unfold fugledeKadisonLog
    exact lt_of_le_of_lt (iInf_le _ (⟨1, zero_lt_one⟩ : Set.Ioi (0 : ℝ))) (EReal.coe_lt_top _)
  let a := (fugledeKadisonLog τ T).toReal
  have he : (a : EReal) = fugledeKadisonLog τ T := EReal.coe_toReal htop hbot
  obtain ⟨q, hq, hs⟩ := exists_tracial_entropic_transport τ P Q K hτ a he.le
  calc
    fugledeKadisonLog τ T = (a : EReal) := he.symm
    _ ≤ (tracialKernelEntropyObjective τ P Q K q : EReal) := EReal.coe_le_coe_iff.mpr hs
    _ ≤ _ := le_sSup ⟨q, hq, rfl⟩

/-- Every probability vector on the support has nonnegative relative entropy with
respect to the full overlap law. -/
theorem tracialKernelRelativeEntropy_nonneg (hτ : IsNormalizedTracialState τ)
    (q : TracialKernelSupport τ P Q K → ℝ) (hq : q ∈ stdSimplex ℝ (TracialKernelSupport τ P Q K)) :
    0 ≤ tracialKernelRelativeEntropy τ P Q K q := by
  classical
  let C := TracialKernelSupport τ P Q K
  let p (e : C) := tracialProjectionOverlap τ P Q e.val.1 e.val.2
  haveI : Nonempty C := by
    by_contra he
    letI : IsEmpty C := not_nonempty_iff.mp he
    have hm : (∑ e : C, q e) = 1 := hq.2
    exact (zero_ne_one : (0 : ℝ) ≠ 1)
      (by simpa only [Finset.univ_eq_empty, Finset.sum_empty] using hm)
  obtain ⟨hpos, _, _, hmass⟩ := tracialProjectionOverlap_coupling τ hτ P Q
  have hp (e : C) : 0 < p e := by
    have hw : p e * Complex.normSq (K e.val.1 e.val.2) ≠ 0 := e.property
    exact lt_of_le_of_ne (hpos _ _) (left_ne_zero_of_mul hw).symm
  have hsum : (∑ e : C, p e) ≤ 1 := by
    let b (x : ι × κ) := tracialProjectionOverlap τ P Q x.1 x.2
    rw [← hmass, ← Fintype.sum_prod_type b]
    change (∑ e : TracialKernelSupport τ P Q K, b e.val) ≤ ∑ x, b x
    rw [← Finset.subtype_univ (fun e : ι × κ => tracialKernelWeight τ P Q K e.1 e.2 ≠ 0),
      Finset.sum_subtype_eq_sum_filter (f := b)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun e _ _ => hpos e.1 e.2)
  have hscore := (finiteEntropyScore_gibbs p hp).1 q hq
  have heq : finiteEntropyScore p q = -tracialKernelRelativeEntropy τ P Q K q := by
    unfold finiteEntropyScore tracialKernelRelativeEntropy
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro e _
    change q e * Real.log (p e) + Real.negMulLog (q e) = -(q e * Real.log (q e / p e))
    by_cases he : q e = 0
    · simp [he]
    rw [Real.log_div he (hp e).ne', Real.negMulLog_eq_neg]
    ring
  rw [heq] at hscore
  exact neg_nonpos.mp (hscore.trans (Real.log_nonpos (Finset.sum_nonneg fun e _ => (hp e).le) hsum))

/-- The determinant logarithm is at most the supremum of the mean log modulus
over supported couplings with the prescribed spectral masses. -/
theorem fugledeKadisonLog_spectralKernel_le_log_transport (hτ : IsNormalizedTracialState τ) :
    fugledeKadisonLog τ (tracialSpectralKernel P Q K) ≤
      sSup {h : EReal | ∃ q, IsTracialKernelCoupling τ P Q K q ∧
        h = (tracialKernelMeanLogModulus τ P Q K q : EReal)} := by
  refine (fugledeKadisonLog_spectralKernel_le_entropic_transport τ P Q K hτ).trans (sSup_le ?_)
  rintro _ ⟨q, hq, rfl⟩
  have hs : tracialKernelEntropyObjective τ P Q K q ≤ tracialKernelMeanLogModulus τ P Q K q :=
    sub_le_self _ (div_nonneg (tracialKernelRelativeEntropy_nonneg τ P Q K hτ q hq.1) zero_le_two)
  exact (EReal.coe_le_coe_iff.mpr hs).trans (le_sSup ⟨q, hq, rfl⟩)

/-- The finite spectral transport bound for a sum uses the kernel
whose value at two spectral labels is the sum of their eigenvalues. -/
theorem fugledeKadisonLog_spectralSum_le_log_transport (hτ : IsNormalizedTracialState τ)
    (a : ι → ℂ) (b : κ → ℂ) :
    let L := fun i j => a i + b j
    fugledeKadisonLog τ ((∑ i, a i • P.proj i) + ∑ j, b j • Q.proj j) ≤
      sSup {h : EReal | ∃ q, IsTracialKernelCoupling τ P Q L q ∧
        h = (tracialKernelMeanLogModulus τ P Q L q : EReal)} := by
  simpa only [tracialSpectralKernel_add] using
    fugledeKadisonLog_spectralKernel_le_log_transport τ P Q (fun i j => a i + b j) hτ

end

end MOC
