import MOC.NormalOrbit
import MOC.SpectralMobius
import Mathlib.Topology.Order.Lattice

/-! A positive support gap can be maximized simultaneously over normalized
spectra, relative eigenbases, and support directions. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem isCompact_spectralEnergy_ball :
    IsCompact {p : (ι → ℂ) × (ι → ℂ) | spectralEnergy p.1 p.2 ≤ 1} := by
  let E : Set (ι → ℂ) := Set.univ.pi fun _ => Metric.closedBall 0 1
  have hE : IsCompact E := isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hc : Continuous (fun p : (ι → ℂ) × (ι → ℂ) => spectralEnergy p.1 p.2) := by
    unfold spectralEnergy
    exact (continuous_finset_sum _ fun i _ => Complex.continuous_normSq.comp (by fun_prop)).add
      (continuous_finset_sum _ fun j _ => Complex.continuous_normSq.comp (by fun_prop))
  refine (hE.prod hE).of_isClosed_subset (isClosed_le hc continuous_const) ?_
  rintro ⟨a,b⟩ hab
  have hnonneg (f : ι → ℂ) : 0 ≤ ∑ i, Complex.normSq (f i) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hterm (f : ι → ℂ) (i : ι) : Complex.normSq (f i) ≤ ∑ j, Complex.normSq (f j) :=
    Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (f j)) (Finset.mem_univ i)
  have hball (x : ℂ) (hx : Complex.normSq x ≤ 1) : x ∈ Metric.closedBall 0 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
    simpa only [← Complex.normSq_eq_norm_sq, one_pow] using hx
  have hle : (∑ i, Complex.normSq (a i)) + ∑ j, Complex.normSq (b j) ≤ 1 := hab
  constructor
  · exact Set.mem_pi.mpr fun i _ => hball _ ((hterm a i).trans (by linarith only [hle, hnonneg b]))
  · exact Set.mem_pi.mpr fun j _ => hball _ ((hterm b j).trans (by linarith only [hle, hnonneg a]))

private theorem isCompact_unit_direction : IsCompact {η : ℂ | Complex.normSq η = 1} := by
  have he : {η : ℂ | Complex.normSq η = 1} = Metric.sphere 0 1 := by
    ext η
    change Complex.normSq η = 1 ↔ dist η 0 = 1
    rw [dist_zero_right, Complex.normSq_eq_norm_sq, ← one_pow 2]
    exact (sq_eq_sq_iff_abs_eq_abs).trans (by simp)
  rw [he]
  exact isCompact_sphere _ _

private theorem exists_normalized_gap_witness
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hbad : ¬ Holds a b U) :
    ∃ (c d : ι → ℂ) (η : ℂ), spectralEnergy c d ≤ 1 ∧ Complex.normSq η = 1 ∧
      ∀ σ : Equiv.Perm ι, 0 < (η * (determinantValue c d U - matchingProduct c d σ)).re := by
  rw [holds_iff_directional] at hbad
  push_neg at hbad
  obtain ⟨η, hsep⟩ := hbad
  have hη : η ≠ 0 := by
    intro hz
    simpa [hz] using hsep (Equiv.refl ι)
  let E := spectralEnergy a b
  let r := (1 + E)⁻¹
  let s := Real.sqrt (Complex.normSq η)
  let k : ℂ := η / (s : ℂ)
  have hE : 0 ≤ E :=
    add_nonneg (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (a i))
      (Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (b j))
  have hE' : 0 < 1 + E := by positivity
  have hr : 0 < r := inv_pos.mpr hE'
  have hs : 0 < s := Real.sqrt_pos_of_pos (Complex.normSq_pos.mpr hη)
  have hsval : s ^ 2 = Complex.normSq η := Real.sq_sqrt (Complex.normSq_nonneg _)
  have hscaled : r ^ 2 * E ≤ 1 := by
    dsimp only [r]
    rw [inv_pow, ← div_eq_inv_mul]
    exact (div_le_iff₀ (pow_pos hE' 2)).mpr (by nlinarith only [hE, sq_nonneg E])
  have hk : Complex.normSq k = 1 := by
    change Complex.normSq (η / (s : ℂ)) = 1
    rw [map_div₀, Complex.normSq_ofReal, ← sq, hsval, div_self (Complex.normSq_pos.mpr hη).ne']
  refine ⟨fun i => (r : ℂ) * a i, fun i => (r : ℂ) * b i, k, ?_, hk, ?_⟩
  · rwa [spectralEnergy_scale]
  · intro σ
    rw [determinantValue_scale, matchingProduct_scale, ← mul_sub]
    have he : k * ((r : ℂ) ^ Fintype.card ι * (determinantValue a b U - matchingProduct a b σ)) =
        ((r ^ Fintype.card ι / s : ℝ) : ℂ) * (η * (determinantValue a b U - matchingProduct a b σ)) := by
      dsimp only [k]
      push_cast
      ring
    rw [he, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos (div_pos (pow_pos hr _) hs) (by rw [mul_sub, Complex.sub_re]; exact sub_pos.mpr (hsep σ))

private theorem spectralEnergy_pos_of_positive_gap (a b : ι → ℂ) (U : Matrix ι ι ℂ) (η : ℂ)
    (h : ∀ σ : Equiv.Perm ι, 0 < (η * (determinantValue a b U - matchingProduct a b σ)).re) :
    0 < spectralEnergy a b := by
  have hn (f : ι → ℂ) : 0 ≤ ∑ i, Complex.normSq (f i) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (f i)
  by_contra! he
  have ha : (∑ i, Complex.normSq (a i)) = 0 := by
    unfold spectralEnergy at he
    linarith only [he, hn a, hn b]
  have hb : (∑ j, Complex.normSq (b j)) = 0 := by
    unfold spectralEnergy at he
    linarith only [he, hn a, hn b]
  have hac : a = 0 := funext fun i => Complex.normSq_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (a j))).mp ha i (Finset.mem_univ i))
  have hbc : b = 0 := funext fun i => Complex.normSq_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (b j))).mp hb i (Finset.mem_univ i))
  have hx := h (Equiv.refl ι)
  rw [hac, hbc] at hx
  simpa [determinantValue, matchingProduct, ← Matrix.det_diagonal] using hx

/-- Starting from any strict violation, choose a violating pair whose ordinary
and squared-norm-weighted traces agree and whose sum is nonnormal. -/
theorem exists_balanced_support_gap_maximizer [Nonempty ι]
    (a₀ b₀ : ι → ℂ) (U₀ : Matrix ι ι ℂ) (hU₀ : IsUnitary U₀) (hbad : ¬ Holds a₀ b₀ U₀) :
    ∃ (a b : ι → ℂ) (U : Matrix ι ι ℂ) (η : ℂ) (g : ℝ),
      IsUnitary U ∧ spectralEnergy a b = 1 ∧ Complex.normSq η = 1 ∧ 0 < g ∧
      (∑ i, a i) = (∑ i, b i) ∧
      (∑ i, (Complex.normSq (a i) : ℂ) * a i) = (∑ i, (Complex.normSq (b i) : ℂ) * b i) ∧
      ¬ IsStarNormal (diagonal a + U * diagonal b * Uᴴ) ∧
      (∀ σ : Equiv.Perm ι,
        g ≤ (η * (determinantValue a b U - matchingProduct a b σ)).re) ∧
      (∀ (c d : ι → ℂ) (V : Matrix ι ι ℂ) (k : ℂ),
        spectralEnergy c d ≤ 1 → IsUnitary V → Complex.normSq k = 1 →
        ∃ σ : Equiv.Perm ι, (k * (determinantValue c d V - matchingProduct c d σ)).re ≤ g) := by
  classical
  obtain ⟨c, d, k, hcd, hk, hsep⟩ := exists_normalized_gap_witness a₀ b₀ U₀ hbad
  let X := ((ι → ℂ) × (ι → ℂ)) × (Matrix ι ι ℂ × ℂ)
  let K : Set X := {p | spectralEnergy p.1 p.2 ≤ 1} ×ˢ
    ({V | IsUnitary V} ×ˢ {k | Complex.normSq k = 1})
  have hK : IsCompact K := isCompact_spectralEnergy_ball.prod
    (isCompact_setOf_isUnitary.prod isCompact_unit_direction)
  let q : X := ((c,d),(U₀,k))
  have hq : q ∈ K := ⟨hcd, hU₀, hk⟩
  let G (σ : Equiv.Perm ι) (p : X) :=
    (p.2.2 * (determinantValue p.1.1 p.1.2 p.2.1 - matchingProduct p.1.1 p.1.2 σ)).re
  let J : Finset (Equiv.Perm ι) := Finset.univ
  have hJ : J.Nonempty := ⟨Equiv.refl ι, Finset.mem_univ _⟩
  let f (p : X) := J.inf' hJ (fun σ => G σ p)
  have hG (σ : Equiv.Perm ι) : Continuous (G σ) := by
    have hd : Continuous (fun p : X => determinantValue p.1.1 p.1.2 p.2.1) := by
      unfold determinantValue
      fun_prop
    have hp : Continuous (fun p : X => matchingProduct p.1.1 p.1.2 σ) := by
      unfold matchingProduct
      exact continuous_finset_prod _ fun j _ => by fun_prop
    exact Complex.continuous_re.comp ((show Continuous (fun p : X => p.2.2) by fun_prop).mul (hd.sub hp))
  have hf : Continuous f := Continuous.finset_inf'_apply hJ fun σ _ => hG σ
  obtain ⟨p, ⟨hp, hU, hη⟩, hmax⟩ := hK.exists_isMaxOn ⟨q,hq⟩ hf.continuousOn
  let a := p.1.1
  let b := p.1.2
  let V₀ := p.2.1
  let η := p.2.2
  let g := f p
  have hg : 0 < g := by
    have hqpos : 0 < f q := (Finset.lt_inf'_iff hJ).mpr (fun σ _ => hsep σ)
    exact hqpos.trans_le (hmax hq)
  have hgap (σ : Equiv.Perm ι) :
      g ≤ (η * (determinantValue a b V₀ - matchingProduct a b σ)).re :=
    Finset.inf'_le _ (Finset.mem_univ σ)
  have hglobal (c d : ι → ℂ) (V : Matrix ι ι ℂ) (k : ℂ)
      (he : spectralEnergy c d ≤ 1) (hV : IsUnitary V) (hk : Complex.normSq k = 1) :
      ∃ σ : Equiv.Perm ι, (k * (determinantValue c d V - matchingProduct c d σ)).re ≤ g := by
    have hmem : ((c,d),(V,k)) ∈ K := ⟨he,hV,hk⟩
    obtain ⟨σ, _, hσ⟩ := (Finset.inf'_le_iff hJ).mp (hmax hmem)
    exact ⟨σ,hσ⟩
  obtain ⟨U, hU', hsupport, htie⟩ := exists_support_frobenius_maximizer a b η
  have heval (σ : Equiv.Perm ι) :
      (η * (determinantValue a b V₀ - matchingProduct a b σ)).re ≤
        (η * (determinantValue a b U - matchingProduct a b σ)).re := by
    simp only [mul_sub, Complex.sub_re]
    exact sub_le_sub_right (hsupport V₀ hU) _
  have hgap' (σ : Equiv.Perm ι) :
      g ≤ (η * (determinantValue a b U - matchingProduct a b σ)).re := (hgap σ).trans (heval σ)
  have hmax' (c d : ι → ℂ) (k : ℂ) (he : spectralEnergy c d ≤ 1) (hk : Complex.normSq k = 1) :=
    hglobal c d U k he hU' hk
  have hp' : spectralEnergy a b ≤ 1 := hp
  have hη' : Complex.normSq η = 1 := hη
  have hpos : 0 < spectralEnergy a b :=
    spectralEnergy_pos_of_positive_gap a b U η (fun σ => hg.trans_le (hgap' σ))
  have hpow := spectralEnergy_mobius_bound a b U hU' η hη' hg hgap' hmax' 0
    (by simp) (by simp) (by simpa using hpos)
  simp only [neg_zero, mobiusSpectrum_zero, mobiusDenominator, zero_mul, sub_zero, add_zero,
    Finset.prod_const_one, one_mul, Complex.normSq_one, mul_one] at hpow
  have henergy : spectralEnergy a b = 1 := by
    apply le_antisymm hp'
    by_contra! hn
    have hd := pow_lt_pow_left₀ hn hpos.le Fintype.card_ne_zero
    exact (not_lt_of_ge hpow) (by simpa only [one_pow] using hd)
  have htrace := equal_trace_of_positive_support_gap_maximizer a b U hU' η g
    hp' hg hgap' (fun c d hcd => hmax' c d η hcd hη')
  have hcubic := equal_cubic_moments_of_positive_gap_maximizer a b U hU' η
    hη' henergy hg hgap' hmax'
  refine ⟨a,b,U,η,g,hU',henergy,hη',hg,htrace,hcubic,?_,hgap',hglobal⟩
  intro hn
  have hh := holds_of_normal_support_frobenius_maximum a b hU' η hn hsupport htie
  obtain ⟨σ,hσ⟩ := (holds_iff_directional a b U).mp hh η
  have hgt := hg.trans_le (hgap' σ)
  simp only [mul_sub, Complex.sub_re, sub_pos] at hgt
  exact (not_lt_of_ge hσ) hgt

end

end MOC
