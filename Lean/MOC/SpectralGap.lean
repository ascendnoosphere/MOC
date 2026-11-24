import MOC.NormalOrbit
import MOC.ContactIteration
import MOC.SpectralMobius
import Mathlib.Topology.Order.Lattice

/-! A positive support gap can be maximized simultaneously over normalized
spectra, relative eigenbases, and support directions. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
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
    rw [dist_zero_right, Complex.normSq_eq_norm_sq]
    simpa only [one_pow] using (sq_eq_sq₀ (norm_nonneg η) (zero_le_one : (0 : ℝ) ≤ 1))
  rw [he]
  exact isCompact_sphere _ _

private theorem exists_normalized_gap_witness
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (η : ℂ)
    (hsep : ∀ σ : Equiv.Perm ι,
      (η * matchingProduct a b σ).re < (η * determinantValue a b U).re) :
    ∃ (c d : ι → ℂ) (k : ℂ), spectralEnergy c d ≤ 1 ∧ Complex.normSq k = 1 ∧
      (∀ σ : Equiv.Perm ι, 0 < (k * (determinantValue c d U - matchingProduct c d σ)).re) ∧
      (∃ m : ℝ, 0 < m ∧ ∀ σ : Equiv.Perm ι,
        (k * matchingProduct c d σ).re = m * (η * matchingProduct a b σ).re) := by
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
  have hE' : 0 < 1 + E := add_pos_of_pos_of_nonneg zero_lt_one hE
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
  let m := r ^ Fintype.card ι / s
  have hmul (z : ℂ) : k * ((r : ℂ) ^ Fintype.card ι * z) = (m : ℂ) * (η * z) := by
    dsimp only [k, m]
    push_cast
    ring
  have hm : 0 < m := div_pos (pow_pos hr _) hs
  refine ⟨fun i => (r : ℂ) * a i, fun i => (r : ℂ) * b i, k, ?_, hk, ?_, m, hm, ?_⟩
  · rwa [spectralEnergy_scale]
  · intro σ
    rw [determinantValue_scale, matchingProduct_scale, ← mul_sub, hmul, Complex.re_ofReal_mul]
    exact mul_pos hm (by rw [mul_sub, Complex.sub_re]; exact sub_pos.mpr (hsep σ))
  · intro σ
    rw [matchingProduct_scale, hmul, Complex.re_ofReal_mul]

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
  have hz : diagonal (0 : ι → ℂ) = 0 := Matrix.diagonal_zero
  have hd : determinantValue (0 : ι → ℂ) 0 U = ∏ _ : ι, (0 : ℂ) := by
    unfold determinantValue
    rw [hz, Matrix.mul_zero, Matrix.zero_mul, add_zero]
    simpa only [hz, Pi.zero_apply] using (Matrix.det_diagonal (d := (0 : ι → ℂ)))
  rw [hd] at hx
  have hfalse : (0 : ℝ) < 0 := by
    simpa only [matchingProduct, Pi.zero_apply, add_zero, sub_self, mul_zero, Complex.zero_re] using hx
  exact (lt_irrefl _) hfalse

/-- The prescribed labels all maximize the projected matching product. -/
def KeepsContacts (S : Finset (Equiv.Perm ι)) (a b : ι → ℂ) (η : ℂ) : Prop :=
  ∀ p ∈ S, ∀ q : Equiv.Perm ι,
    (η * matchingProduct a b q).re ≤ (η * matchingProduct a b p).re

omit [DecidableEq ι] in
theorem KeepsContacts.of_profile_scale {S : Finset (Equiv.Perm ι)}
    {a b c d : ι → ℂ} {η k : ℂ} {m : ℝ} (h : KeepsContacts S a b η) (hm : 0 ≤ m)
    (he : ∀ q : Equiv.Perm ι,
      (k * matchingProduct c d q).re = m * (η * matchingProduct a b q).re) :
    KeepsContacts S c d k := by
  intro p hp q
  rw [he, he]
  exact mul_le_mul_of_nonneg_left (h p hp q) hm

/-- A normalized support gap can be maximized with all prescribed contacts
retained. Fractional-linear changes with compensated phase preserve those
contacts, so the same trace and cubic balances still hold. The mixer may
also be chosen to be an unrestricted orbit support maximizer. -/
theorem exists_balanced_support_gap_maximizer_with_contacts [Nonempty ι]
    (S : Finset (Equiv.Perm ι)) (a₀ b₀ : ι → ℂ) (U₀ : Matrix ι ι ℂ) (k₀ : ℂ)
    (hU₀ : IsUnitary U₀) (hE₀ : spectralEnergy a₀ b₀ ≤ 1) (hk₀ : Complex.normSq k₀ = 1)
    (hsep : ∀ σ : Equiv.Perm ι, 0 < (k₀ * (determinantValue a₀ b₀ U₀ -
      matchingProduct a₀ b₀ σ)).re) (hS₀ : KeepsContacts S a₀ b₀ k₀) :
    ∃ (a b : ι → ℂ) (U : Matrix ι ι ℂ) (η : ℂ) (g : ℝ),
      IsUnitary U ∧ spectralEnergy a b = 1 ∧ Complex.normSq η = 1 ∧ 0 < g ∧
      KeepsContacts S a b η ∧
      (∑ i, a i) = (∑ i, b i) ∧
      (∑ i, (Complex.normSq (a i) : ℂ) * a i) = (∑ i, (Complex.normSq (b i) : ℂ) * b i) ∧
      ¬ IsStarNormal (diagonal a + U * diagonal b * Uᴴ) ∧
      (∀ σ : Equiv.Perm ι,
        g ≤ (η * (determinantValue a b U - matchingProduct a b σ)).re) ∧
      (∀ (c d : ι → ℂ) (V : Matrix ι ι ℂ) (k : ℂ),
        spectralEnergy c d ≤ 1 → IsUnitary V → Complex.normSq k = 1 →
        KeepsContacts S c d k →
        ∃ σ : Equiv.Perm ι, (k * (determinantValue c d V - matchingProduct c d σ)).re ≤ g) ∧
      (∀ V : Matrix ι ι ℂ, IsUnitary V →
        (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re) := by
  classical
  let X := ((ι → ℂ) × (ι → ℂ)) × (Matrix ι ι ℂ × ℂ)
  let K₀ : Set X := {p | spectralEnergy p.1 p.2 ≤ 1} ×ˢ
    ({V | IsUnitary V} ×ˢ {k | Complex.normSq k = 1})
  let T : Set X := {p | KeepsContacts S p.1.1 p.1.2 p.2.2}
  let K := K₀ ∩ T
  have hK₀ : IsCompact K₀ := isCompact_spectralEnergy_ball.prod
    (isCompact_setOf_isUnitary.prod isCompact_unit_direction)
  let P (j : Equiv.Perm ι) (p : X) :=
    (p.2.2 * matchingProduct p.1.1 p.1.2 j).re
  have hP (j : Equiv.Perm ι) : Continuous (P j) := by
    have hp : Continuous (fun p : X => matchingProduct p.1.1 p.1.2 j) := by
      unfold matchingProduct
      exact continuous_finset_prod _ fun i _ => by fun_prop
    exact Complex.continuous_re.comp ((show Continuous (fun p : X => p.2.2) by fun_prop).mul hp)
  have hT : IsClosed T := by
    have he : T = ⋂ j ∈ S, ⋂ l : Equiv.Perm ι, {p : X | P l p ≤ P j p} := by
      ext p
      simp only [T, KeepsContacts, Set.mem_setOf_eq, Set.mem_iInter, P]
    rw [he]
    exact isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_iInter fun l => isClosed_le (hP l) (hP j)
  have hK : IsCompact K := hK₀.inter_right hT
  let q : X := ((a₀,b₀),(U₀,k₀))
  have hq : q ∈ K := ⟨⟨hE₀, hU₀, hk₀⟩, hS₀⟩
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
  obtain ⟨p, ⟨⟨hp, hU, hη⟩, hpS⟩, hmax⟩ := hK.exists_isMaxOn ⟨q,hq⟩ hf.continuousOn
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
      (he : spectralEnergy c d ≤ 1) (hV : IsUnitary V) (hk : Complex.normSq k = 1) (hcs : KeepsContacts S c d k) :
      ∃ σ : Equiv.Perm ι, (k * (determinantValue c d V - matchingProduct c d σ)).re ≤ g := by
    have hmem : ((c,d),(V,k)) ∈ K := ⟨⟨he,hV,hk⟩,hcs⟩
    have hle : J.inf' hJ (fun σ => G σ ((c,d),(V,k))) ≤ g := hmax hmem
    obtain ⟨σ, _, hσ⟩ := (Finset.inf'_le_iff hJ).mp hle
    exact ⟨σ,hσ⟩
  obtain ⟨U, hU', hsupport, htie⟩ := exists_support_frobenius_maximizer a b η
  have heval (σ : Equiv.Perm ι) :
      (η * (determinantValue a b V₀ - matchingProduct a b σ)).re ≤
        (η * (determinantValue a b U - matchingProduct a b σ)).re := by
    simp only [mul_sub, Complex.sub_re]
    exact sub_le_sub_right (hsupport V₀ hU) _
  have hgap' (σ : Equiv.Perm ι) :
      g ≤ (η * (determinantValue a b U - matchingProduct a b σ)).re := (hgap σ).trans (heval σ)
  have hpos : 0 < spectralEnergy a b :=
    spectralEnergy_pos_of_positive_gap a b U η (fun σ => hg.trans_le (hgap' σ))
  have hbound :=
    spectralEnergy_shifted_mobius_bound_of_profile_scale_maximum a b U hU' η hη hg hgap'
      (fun c d k he hk ⟨m, hm, hscale⟩ =>
        hglobal c d U k he hU' hk (KeepsContacts.of_profile_scale hpS hm.le hscale))
  have henergy_bound (s : ℂ) (he : 0 < spectralEnergy (fun i => a i + s) (fun j => b j - s)) :
      1 ≤ spectralEnergy (fun i => a i + s) (fun j => b j - s) ^ Fintype.card ι := by
    simpa [mobiusDenominator] using hbound 0 s (by simp) (by simp) (by simpa using he)
  have heq (x : ℝ) (hx : 0 ≤ x) (hb : x ≤ 1) (hle : 1 ≤ x ^ Fintype.card ι) : x = 1 := by
    refine le_antisymm hb ?_
    by_contra! hn
    exact (not_lt_of_ge hle) (by simpa only [one_pow] using
      (pow_lt_pow_left₀ hn hx (Fintype.card_ne_zero (α := ι))))
  have henergy : spectralEnergy a b = 1 :=
    heq _ hpos.le hp (by simpa using henergy_bound 0 (by simpa using hpos))
  let S₀ : ℂ := (∑ i, a i) - ∑ j, b j
  let N : ℝ := 2 * (Fintype.card ι : ℝ)
  let s : ℂ := -S₀ / (N : ℂ)
  have hcenter : spectralEnergy (fun i => a i + s) (fun j => b j - s) =
      spectralEnergy a b - Complex.normSq S₀ / N := spectralEnergy_centering a b
  have hshift : 0 < spectralEnergy (fun i => a i + s) (fun j => b j - s) := by
    apply spectralEnergy_pos_of_positive_gap _ _ U η
    simpa only [determinantValue_shift a b hU' s, matchingProduct_shift a b s] using
      (fun σ => hg.trans_le (hgap' σ))
  have hN : 0 < N := mul_pos two_pos (Nat.cast_pos.mpr Fintype.card_pos)
  have hcenter_le : spectralEnergy (fun i => a i + s) (fun j => b j - s) ≤ 1 := by
    rw [hcenter, henergy]
    exact sub_le_self _ (div_nonneg (Complex.normSq_nonneg _) hN.le)
  have hcenter_eq := heq _ hshift.le hcenter_le (henergy_bound s hshift)
  have htrace : (∑ i, a i) = ∑ i, b i := by
    apply sub_eq_zero.mp
    change S₀ = 0
    rw [hcenter, henergy, sub_eq_self] at hcenter_eq
    exact Complex.normSq_eq_zero.mp ((div_eq_zero_iff.mp hcenter_eq).resolve_right hN.ne')
  have hcubic := equal_cubic_moments_of_mobius_energy_bound a b henergy htrace
    (fun t ha hb he => by
      simpa only [add_zero, sub_zero] using
        hbound t 0 ha hb (by simpa only [add_zero, sub_zero] using he))
  refine ⟨a,b,U,η,g,hU',henergy,hη,hg,hpS,htrace,hcubic,?_,hgap',hglobal,hsupport⟩
  intro hn
  have hh := holds_of_normal_support_frobenius_maximum a b hU' η hn hsupport htie
  obtain ⟨σ,hσ⟩ := (holds_iff_directional a b U).mp hh η
  have hgt := hg.trans_le (hgap' σ)
  simp only [mul_sub, Complex.sub_re, sub_pos] at hgt
  exact (not_lt_of_ge hσ) hgt

/-- Normalize a strict witness by a positive projected common factor without
losing a contact or changing its pivot. -/
theorem StrictMatchingSupport.exists_normalized_retaining_contacts
    {U : Matrix ι ι ℂ} (w : StrictMatchingSupport U) :
    ∃ (c d : ι → ℂ) (k : ℂ), spectralEnergy c d ≤ 1 ∧ Complex.normSq k = 1 ∧
      (∀ σ : Equiv.Perm ι, 0 < (k * (determinantValue c d U - matchingProduct c d σ)).re) ∧
      KeepsContacts w.contacts c d k := by
  obtain ⟨c,d,k,hE,hk,hgap,m,hm,hs⟩ := exists_normalized_gap_witness w.a w.b U w.η
    (fun σ => (w.maximal σ).trans_lt w.strict)
  have h : KeepsContacts w.contacts w.a w.b w.η := by
    intro p hp q
    rw [(Finset.mem_filter.mp hp).2]
    exact w.maximal q
  exact ⟨c,d,k,hE,hk,hgap,KeepsContacts.of_profile_scale h hm.le hs⟩

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
  rw [holds_iff_directional] at hbad
  push_neg at hbad
  obtain ⟨η₀,hsep₀⟩ := hbad
  obtain ⟨c,d,k,hcd,hk,hsep,_⟩ := exists_normalized_gap_witness a₀ b₀ U₀ η₀ hsep₀
  obtain ⟨a,b,U,η,g,hU,he,hη,hg,_,htrace,hcubic,hn,hgap,hmax,_⟩ :=
    exists_balanced_support_gap_maximizer_with_contacts ∅ c d U₀ k hU₀ hcd hk hsep
      (by simp [KeepsContacts])
  exact ⟨a,b,U,η,g,hU,he,hη,hg,htrace,hcubic,hn,hgap,
    fun c d V k he hV hk => hmax c d V k he hV hk (by simp [KeepsContacts])⟩

/-- For any positive finite order, only the unit-energy, doubly balanced
spectra with nonnormal sum are needed for the conjecture. -/
theorem conjecture_iff_balanced_nonnormal [Nonempty ι] :
    Conjecture ι ↔ ∀ (a b : ι → ℂ) (U : Matrix ι ι ℂ), IsUnitary U →
      spectralEnergy a b = 1 → (∑ i, a i) = (∑ i, b i) →
      (∑ i, (Complex.normSq (a i) : ℂ) * a i) = (∑ i, (Complex.normSq (b i) : ℂ) * b i) →
      ¬ IsStarNormal (diagonal a + U * diagonal b * Uᴴ) → Holds a b U := by
  constructor
  · intro h a b U hU _ _ _ _
    exact h a b U hU
  · intro h a b U hU
    by_contra hn
    obtain ⟨c,d,V,η,g,hV,henergy,_,hg,htrace,hcubic,hnormal,hgap,_⟩ :=
      exists_balanced_support_gap_maximizer a b U hU hn
    obtain ⟨σ,hσ⟩ := (holds_iff_directional c d V).mp
      (h c d V hV henergy htrace hcubic hnormal) η
    have hgt := hg.trans_le (hgap σ)
    simp only [mul_sub, Complex.sub_re, sub_pos] at hgt
    exact (not_lt_of_ge hσ) hgt

end

end MOC
