import MOC.AnchoredChart
import MOC.MatchingQuartet
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice

/-! Rational slices of the contact fiber and the obstruction to a
nonconstant common translation of the matching coordinates. -/

open BigOperators Set Polynomial

namespace MOC

/-- A nonconstant reduced rational function takes every value except a
finite set on the complement of a finite exceptional set. -/
theorem rational_range_cofinite (p q : ℂ[X]) (hcop : IsCoprime p q)
    (S : Set ℂ) (hS : S.Finite)
    (hvar : ∃ x y : ℂ, p.eval x / q.eval x ≠ p.eval y / q.eval y) :
    ∃ E : Set ℂ, E.Finite ∧ ∀ w ∉ E, ∃ z ∉ S, q.eval z ≠ 0 ∧
      p.eval z / q.eval z = w := by
  obtain ⟨x, y, hxy⟩ := hvar
  have hp : p ≠ 0 := by
    intro hp
    simp [hp] at hxy
  have hq : q ≠ 0 := by
    intro hq
    simp [hq] at hxy
  have hpos : 0 < p.natDegree ∨ 0 < q.natDegree := by
    by_contra! hn
    have heval (s : ℂ[X]) (hs : s.natDegree ≤ 0) (z : ℂ) :
        s.eval z = s.coeff 0 :=
      (congrArg (Polynomial.eval z) (eq_C_of_natDegree_le_zero hs)).trans eval_C
    apply hxy
    simp only [heval p hn.1, heval q hn.2]
  let k := max p.natDegree q.natDegree
  have hk : 0 < k := by
    rcases hpos with h | h
    · exact h.trans_le (le_max_left _ _)
    · exact h.trans_le (le_max_right _ _)
  have hcoeff : p.coeff k ≠ 0 ∨ q.coeff k ≠ 0 := by
    by_cases hle : p.natDegree ≤ q.natDegree
    · right
      rw [show k = q.natDegree from max_eq_right hle, coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hq
    · left
      rw [show k = p.natDegree from max_eq_left (le_of_not_ge hle), coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hp
  let u := p.coeff k / q.coeff k
  let T := (fun z => p.eval z / q.eval z) '' S
  refine ⟨insert u T, (hS.image _).insert _, ?_⟩
  intro w hw
  have hP : (p - C w * q).coeff k ≠ 0 := by
    rw [coeff_sub, coeff_C_mul]
    intro h
    have he := sub_eq_zero.mp h
    by_cases hqk : q.coeff k = 0
    · exact hcoeff.resolve_right (fun hn => hn hqk) (by simpa only [hqk, mul_zero] using he)
    · exact hw (mem_insert_iff.mpr (Or.inl ((eq_div_iff hqk).mpr he.symm)))
  have hdeg : (p - C w * q).degree ≠ 0 := by
    intro h
    have hnat : (p - C w * q).natDegree = 0 := natDegree_eq_of_degree_eq_some h
    exact hP (coeff_eq_zero_of_natDegree_lt (by rwa [hnat]))
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (p - C w * q) hdeg
  have he : p.eval z = w * q.eval z := by
    simpa only [IsRoot, eval_sub, eval_mul, eval_C, sub_eq_zero] using hz
  have hqz : q.eval z ≠ 0 := by
    intro hzero
    have hpz : p.eval z = 0 := by simpa only [hzero, mul_zero] using he
    obtain ⟨a, b, hab⟩ := hcop
    have h := congrArg (Polynomial.eval z) hab
    simp only [eval_add, eval_mul, eval_one, hpz, hzero, mul_zero, add_zero,
      zero_ne_one] at h
  have hz : p.eval z / q.eval z = w := (div_eq_iff hqz).mpr he
  exact ⟨z, fun hzS => hw (mem_insert_of_mem _ ⟨z, hzS, hz⟩), hqz, hz⟩

private theorem eval_div_reduce (p q : ℂ[X]) (hq : q ≠ 0) (z : ℂ)
    (hz : q.eval z ≠ 0) :
    let d := GCDMonoid.gcd p q
    (p / d).eval z / (q / d).eval z = p.eval z / q.eval z := by
  intro d
  have hd : d ≠ 0 := gcd_ne_zero_of_right hq
  have hp' : d * (p / d) = p :=
    EuclideanDomain.mul_div_cancel' hd (GCDMonoid.gcd_dvd_left p q)
  have hq' : d * (q / d) = q :=
    EuclideanDomain.mul_div_cancel' hd (GCDMonoid.gcd_dvd_right p q)
  have hpe := congrArg (Polynomial.eval z) hp'
  have hqe := congrArg (Polynomial.eval z) hq'
  simp only [eval_mul] at hpe hqe
  have hdz : d.eval z ≠ 0 := left_ne_zero_of_mul (by rwa [hqe])
  rw [← hpe, ← hqe, mul_div_mul_left _ _ hdz]

/-- A nonconstant rational function on a cofinite set takes a cofinite
set of values. Common factors in its numerator and denominator are allowed. -/
theorem rational_range_cofinite_of_eval_ne_zero (p q : ℂ[X])
    (S : Set ℂ) (hS : S.Finite) (hq : ∀ z ∉ S, q.eval z ≠ 0)
    (hvar : ∃ x ∉ S, ∃ y ∉ S, p.eval x / q.eval x ≠ p.eval y / q.eval y) :
    ∃ E : Set ℂ, E.Finite ∧ ∀ w ∉ E, ∃ z ∉ S, p.eval z / q.eval z = w := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hvar
  have hq' : q ≠ 0 := by
    intro h
    exact hq x hx (by rw [h, eval_zero])
  let d := GCDMonoid.gcd p q
  obtain ⟨E, hE, hsurj⟩ := rational_range_cofinite (p / d) (q / d)
    (isCoprime_div_gcd_div_gcd hq') S hS
    ⟨x, y, by rw [eval_div_reduce p q hq' x (hq x hx),
      eval_div_reduce p q hq' y (hq y hy)]; exact hxy⟩
  refine ⟨E, hE, fun w hw => ?_⟩
  obtain ⟨z, hz, _, he⟩ := hsurj w hw
  exact ⟨z, hz, (eval_div_reduce p q hq' z (hq z hz)).symm.trans he⟩

/-- A finite family of initially positive rational gaps reaches a new
zero without a compactification, provided one quotient varies. -/
theorem exists_new_contact_on_rational_slice {ι : Type*} (J : Finset ι)
    {S : Set ℂ} (hS : S.Finite) (p q : ι → ℂ[X])
    (hq : ∀ i ∈ J, ∀ z ∉ S, (q i).eval z ≠ 0)
    {x₀ : ℂ} (hx₀ : x₀ ∉ S)
    (hstart : ∀ i ∈ J, (0 : ℝ) < ((p i).eval x₀ / (q i).eval x₀).re)
    (hvar : ∃ i ∈ J, ∃ x ∉ S, ∃ y ∉ S,
      (p i).eval x / (q i).eval x ≠ (p i).eval y / (q i).eval y) :
    ∃ z ∉ S, (∀ i ∈ J, (0 : ℝ) ≤ ((p i).eval z / (q i).eval z).re) ∧
      ∃ i ∈ J, ((p i).eval z / (q i).eval z).re = 0 := by
  obtain ⟨i, hi, hnonconstant⟩ := hvar
  obtain ⟨E, hE, hsurj⟩ :=
    rational_range_cofinite_of_eval_ne_zero (p i) (q i) S hS (hq i hi) hnonconstant
  obtain ⟨l, hl⟩ := (hE.image Complex.re).bddBelow
  let w : ℂ := ((min l 0 - 1 : ℝ) : ℂ)
  have hwre : w.re < 0 := by
    change min l 0 - 1 < 0
    linarith only [min_le_right l 0]
  have hw : w ∉ E := by
    intro h
    have hle : l ≤ w.re := hl ⟨w, h, rfl⟩
    change l ≤ min l 0 - 1 at hle
    linarith only [hle, min_le_left l 0]
  obtain ⟨z, hz, he⟩ := hsurj w hw
  let H (j : ι) (x : ℂ) := ((p j).eval x / (q j).eval x).re
  let hJn : J.Nonempty := ⟨i, hi⟩
  let m (x : ℂ) := J.inf' hJn (fun j => H j x)
  have hm : ContinuousOn m Sᶜ :=
    ContinuousOn.finset_inf'_apply (f := H) hJn (fun j hj =>
      Complex.continuous_re.comp_continuousOn
        ((p j).continuousOn.div (q j).continuousOn (hq j hj)))
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hconn : IsPreconnected Sᶜ :=
    (hS.countable.isPathConnected_compl_of_one_lt_rank hrank).isConnected.isPreconnected
  have hnegative : H i z < 0 := by
    change ((p i).eval z / (q i).eval z).re < 0
    rwa [he]
  have hmz : m z < 0 := (Finset.inf'_lt_iff hJn).2 ⟨i, hi, hnegative⟩
  have hm₀ : 0 < m x₀ := (Finset.lt_inf'_iff hJn).2 hstart
  have himage : (0 : ℝ) ∈ m '' Sᶜ :=
    (hconn.image _ hm).Icc_subset ⟨z, hz, rfl⟩ ⟨x₀, hx₀, rfl⟩ ⟨hmz.le, hm₀.le⟩
  obtain ⟨v, hv, hmv⟩ := himage
  have hnonneg : ∀ j ∈ J, 0 ≤ H j v :=
    (Finset.le_inf'_iff hJn (fun j => H j v)).1 (show 0 ≤ m v from hmv.ge)
  obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_inf' hJn (fun j => H j v)
  exact ⟨v, hv, hnonneg, j, hj, heq.symm.trans hmv⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A changed matching vector with the active differences fixed must change
an inactive difference. The nonzero alternating sum rules out translation. -/
theorem exists_varying_inactive_matching_difference (a b a' b' : ι → ℂ)
    (J : Finset (Equiv.Perm ι)) (r σ₀ : Equiv.Perm ι) (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (ha : Function.Injective a) (hb : Function.Injective b) (hnz : ∀ r s, a r + b s ≠ 0)
    (hfixed : ∀ σ ∉ J,
      matchingProduct a b r - matchingProduct a b σ =
        matchingProduct a' b' r - matchingProduct a' b' σ)
    (hvar : ∃ σ, matchingProduct a b σ ≠ matchingProduct a' b' σ) :
    ∃ σ ∈ J, matchingProduct a b r - matchingProduct a b σ ≠
      matchingProduct a' b' r - matchingProduct a' b' σ := by
  classical
  by_contra! hzero
  let c := matchingProduct a' b' r - matchingProduct a b r
  have htranslate (σ : Equiv.Perm ι) :
      matchingProduct a' b' σ = matchingProduct a b σ + c := by
    have h := if hσ : σ ∈ J then hzero σ hσ else hfixed σ hσ
    dsimp only [c]
    linear_combination h
  have hdiag := matchingProduct_disjoint_swaps_identity a b σ₀ i j k l hij hik hil hjk hjl hkl
  have hdiag' := matchingProduct_disjoint_swaps_identity a' b' σ₀ i j k l hij hik hil hjk hjl hkl
  simp only [htranslate] at hdiag'
  have hΓ := matchingProduct_disjoint_swaps_alternating_sum_ne_zero
    a b σ₀ i j k l hij hik hil hjk hjl hkl ha hb hnz
  have hc := eq_zero_of_matching_quartet_translation hdiag hΓ hdiag'
  obtain ⟨σ, hσ⟩ := hvar
  exact hσ (by simpa only [hc, add_zero] using (htranslate σ).symm)

/-- A rational matching slice that fixes the complex active differences
and determinant deficit adds a support contact at the same positive gap. -/
theorem exists_new_matching_contact_on_rational_slice {S : Set ℂ} (hS : S.Finite)
    (a b : ℂ → ι → ℂ) (U : Matrix ι ι ℂ) (η : ℂ) (hη : η ≠ 0)
    (r σ₀ : Equiv.Perm ι) (J : Finset (Equiv.Perm ι)) (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    {x₀ : ℂ} (hx₀ : x₀ ∉ S)
    (ha : Function.Injective (a x₀)) (hb : Function.Injective (b x₀))
    (hnz : ∀ i j, a x₀ i + b x₀ j ≠ 0)
    (hfixed : ∀ x ∉ S, ∀ σ ∉ J,
      matchingProduct (a x) (b x) r - matchingProduct (a x) (b x) σ =
        matchingProduct (a x₀) (b x₀) r - matchingProduct (a x₀) (b x₀) σ)
    (hold : ∀ σ ∉ J, matchingGap (a x₀) (b x₀) η r σ = 0)
    (hstart : ∀ σ ∈ J, 0 < matchingGap (a x₀) (b x₀) η r σ)
    (hchange : ∃ y ∉ S, ∃ σ,
      matchingProduct (a x₀) (b x₀) σ ≠ matchingProduct (a y) (b y) σ)
    (p q : Equiv.Perm ι → ℂ[X])
    (hq : ∀ σ ∈ J, ∀ x ∉ S, (q σ).eval x ≠ 0)
    (hrat : ∀ σ ∈ J, ∀ x ∉ S, (p σ).eval x / (q σ).eval x =
      η * (matchingProduct (a x) (b x) r - matchingProduct (a x) (b x) σ))
    {g : ℝ} (hg : 0 < g)
    (hgap : ∀ x ∉ S,
      (η * (determinantValue (a x) (b x) U - matchingProduct (a x) (b x) r)).re = g) :
    ∃ z ∉ S, (∀ σ, 0 ≤ matchingGap (a z) (b z) η r σ) ∧
      (∀ σ ∉ J, matchingGap (a z) (b z) η r σ = 0) ∧
      (∃ σ ∈ J, matchingGap (a z) (b z) η r σ = 0) ∧
      (η * determinantValue (a z) (b z) U).re - (η * matchingProduct (a z) (b z) r).re = g ∧
      ∀ σ, (η * matchingProduct (a z) (b z) σ).re < (η * determinantValue (a z) (b z) U).re := by
  have hreal (σ : Equiv.Perm ι) (hσ : σ ∈ J) (x : ℂ) (hx : x ∉ S) :
      ((p σ).eval x / (q σ).eval x).re = matchingGap (a x) (b x) η r σ := by
    rw [hrat σ hσ x hx]
    simp only [matchingGap, mul_sub, Complex.sub_re]
  have hvar : ∃ σ ∈ J, ∃ x ∉ S, ∃ y ∉ S,
      (p σ).eval x / (q σ).eval x ≠ (p σ).eval y / (q σ).eval y := by
    obtain ⟨y, hy, hmatch⟩ := hchange
    obtain ⟨σ, hσ, hne⟩ := exists_varying_inactive_matching_difference
      (a x₀) (b x₀) (a y) (b y) J r σ₀ i j k l hij hik hil hjk hjl hkl
      ha hb hnz (fun σ hσ => (hfixed y hy σ hσ).symm) hmatch
    refine ⟨σ, hσ, x₀, hx₀, y, hy, ?_⟩
    rw [hrat σ hσ x₀ hx₀, hrat σ hσ y hy]
    exact fun he => hne (mul_left_cancel₀ hη he)
  obtain ⟨z, hz, hnonneg, σ, hσ, hzero⟩ :=
    exists_new_contact_on_rational_slice J hS p q hq hx₀
      (fun σ hσ => by rw [hreal σ hσ x₀ hx₀]; exact hstart σ hσ) hvar
  have hkeep (τ : Equiv.Perm ι) (hτ : τ ∉ J) : matchingGap (a z) (b z) η r τ = 0 := by
    calc
      _ = (η * (matchingProduct (a z) (b z) r - matchingProduct (a z) (b z) τ)).re := by
        simp only [matchingGap, mul_sub, Complex.sub_re]
      _ = _ := by
        rw [hfixed z hz τ hτ]
        simpa only [mul_sub, Complex.sub_re] using hold τ hτ
  have hall (τ : Equiv.Perm ι) : 0 ≤ matchingGap (a z) (b z) η r τ := by
    by_cases hτ : τ ∈ J
    · rw [← hreal τ hτ z hz]
      exact hnonneg τ hτ
    · exact (hkeep τ hτ).ge
  have hg' : (η * determinantValue (a z) (b z) U).re -
      (η * matchingProduct (a z) (b z) r).re = g := by
    simpa only [mul_sub, Complex.sub_re] using hgap z hz
  have hrlt : (η * matchingProduct (a z) (b z) r).re <
      (η * determinantValue (a z) (b z) U).re := by
    apply sub_pos.mp
    rwa [hg']
  exact ⟨z, hz, hall, hkeep, ⟨σ, hσ, (hreal σ hσ z hz).symm.trans hzero⟩, hg',
    fun τ => (sub_nonneg.mp (hall τ)).trans_lt hrlt⟩

private theorem exists_rational_bilinear_slice (A B D : ℂ) :
    ∃ p q d : ℂ[X], d.eval 0 ≠ 0 ∧ p.eval 0 = 0 ∧ q.eval 0 = 0 ∧
      (p = X * d ∨ q = X * d) ∧ C A * p * d + C B * q * d + C D * p * q = 0 := by
  by_cases hB : B = 0
  · by_cases hA : A = 0
    · exact ⟨X, 0, 1, by simp, by simp, by simp, Or.inl (by simp), by simp [hA, hB]⟩
    · let d : ℂ[X] := C A + C D * X
      refine ⟨- C B * X, X * d, d, by simpa [d] using hA, by simp, by simp, Or.inr rfl, ?_⟩
      simp only [d]
      ring
  · let d : ℂ[X] := C B + C D * X
    refine ⟨X * d, - C A * X, d, by simpa [d] using hB, by simp, by simp, Or.inl rfl, ?_⟩
    simp only [d]
    ring

set_option maxHeartbeats 2000000 in
private theorem exists_two_contact_progression_of_bilinear_family
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ) (hη : η ≠ 0)
    (r s : Equiv.Perm ι) (i j k l : ι) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (ha : Function.Injective a) (hb : Function.Injective b) (hnz : ∀ i j, a i + b j ≠ 0)
    (hinj : Function.Injective (matchingProduct a b))
    (htie : matchingGap a b η r s = 0)
    (hstart : ∀ σ, σ ≠ r → σ ≠ s → 0 < matchingGap a b η r σ)
    (hstrict : (η * matchingProduct a b r).re < (η * determinantValue a b U).re)
    (L M N : Equiv.Perm ι → ℂ)
    (hrealize : ∀ t u c : ℂ, ∃ a' b' : ι → ℂ, ∀ σ,
      matchingProduct a' b' σ = c * (matchingProduct a b σ + L σ * t + M σ * u + N σ * t * u))
    (hmove : ∀ t u c : ℂ, (t ≠ 0 ∨ u ≠ 0) → c ≠ 0 → ∃ σ,
      matchingProduct a b σ ≠ c * (matchingProduct a b σ + L σ * t + M σ * u + N σ * t * u)) :
    ∃ a' b' : ι → ℂ, (∀ i j, a' i + b' j ≠ 0) ∧ Function.Injective (matchingProduct a' b') ∧
      (∀ σ, 0 ≤ matchingGap a' b' η r σ) ∧ matchingGap a' b' η r s = 0 ∧
      (∃ τ, τ ≠ r ∧ τ ≠ s ∧ matchingGap a' b' η r τ = 0) ∧
      (η * determinantValue a' b' U).re - (η * matchingProduct a' b' r).re =
        (η * determinantValue a b U).re - (η * matchingProduct a b r).re := by
  classical
  let z₀ := matchingProduct a b
  let G (z : Equiv.Perm ι → ℂ) := (∑ σ, signedWeight U σ * z σ) - z r
  let P := G z₀
  let H := z₀ r - z₀ s
  have hP : P = determinantValue a b U - z₀ r := by
    dsimp only [P, G, z₀]
    rw [signed_determinant a b U hU]
  let g : ℝ := (η * determinantValue a b U).re - (η * z₀ r).re
  have hg : 0 < g := sub_pos.mpr hstrict
  have hPg : (η * P).re = g := by rw [hP, mul_sub, Complex.sub_re]
  have hP₀ : P ≠ 0 := by
    intro h
    simp only [h, mul_zero, Complex.zero_re] at hPg
    exact hg.ne' hPg.symm
  let A := P * (L r - L s) - H * G L
  let B := P * (M r - M s) - H * G M
  let D := P * (N r - N s) - H * G N
  obtain ⟨p, q, d, hd₀, hp₀, hq₀, hfree, hslice⟩ := exists_rational_bilinear_slice A B D
  let V (σ : Equiv.Perm ι) : ℂ[X] :=
    C (z₀ σ) * d ^ 2 + C (L σ) * p * d + C (M σ) * q * d + C (N σ) * p * q
  let Q : ℂ[X] := C P * d ^ 2 + C (G L) * p * d + C (G M) * q * d + C (G N) * p * q
  have hV₀ (σ : Equiv.Perm ι) : (V σ).eval 0 = z₀ σ * d.eval 0 ^ 2 := by
    simp [V, hp₀, hq₀]
  have hQ₀ : Q.eval 0 = P * d.eval 0 ^ 2 := by simp [Q, hp₀, hq₀]
  let I := {u : Equiv.Perm ι × Equiv.Perm ι // u.1 ≠ u.2}
  let bad : ℂ[X] := d * Q * (∏ σ, V σ) * ∏ u : I, (V u.1.1 - V u.1.2)
  let S : Set ℂ := {t | bad.IsRoot t}
  have hbad (t : ℂ) : bad.eval t ≠ 0 ↔
      ((d.eval t ≠ 0 ∧ Q.eval t ≠ 0) ∧ (∀ σ, (V σ).eval t ≠ 0)) ∧
        ∀ u : I, (V u.1.1).eval t - (V u.1.2).eval t ≠ 0 := by
    simp only [bad, eval_mul, eval_prod, eval_sub, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
      Finset.mem_univ, true_implies]
  have hQ₀nz : Q.eval 0 ≠ 0 := by
    rw [hQ₀]
    exact mul_ne_zero hP₀ (pow_ne_zero _ hd₀)
  have hV₀nz (σ : Equiv.Perm ι) : (V σ).eval 0 ≠ 0 := by
    rw [hV₀]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => hnz (σ j) j)
      (pow_ne_zero _ hd₀)
  have hdiff₀nz (u : I) : (V u.1.1).eval 0 - (V u.1.2).eval 0 ≠ 0 := by
    rw [hV₀, hV₀, ← sub_mul]
    exact mul_ne_zero (sub_ne_zero.mpr (hinj.ne u.2)) (pow_ne_zero _ hd₀)
  have hzero : 0 ∉ S := (hbad 0).2 ⟨⟨⟨hd₀, hQ₀nz⟩, hV₀nz⟩, hdiff₀nz⟩
  have hS : S.Finite := finite_setOf_isRoot (fun h => hzero (by simp [S, IsRoot, h]))
  have hd (t : ℂ) (ht : t ∉ S) : d.eval t ≠ 0 := ((hbad t).1 ht).1.1.1
  have hQ (t : ℂ) (ht : t ∉ S) : Q.eval t ≠ 0 := ((hbad t).1 ht).1.1.2
  let x (t : ℂ) := p.eval t / d.eval t
  let y (t : ℂ) := q.eval t / d.eval t
  let c (t : ℂ) := P * d.eval t ^ 2 / Q.eval t
  let Z (t u : ℂ) (σ : Equiv.Perm ι) := z₀ σ + L σ * t + M σ * u + N σ * t * u
  choose a₀ b₀ hab₀ using fun t : ℂ => hrealize (x t) (y t) (c t)
  let a' (t : ℂ) := if t = 0 then a else a₀ t
  let b' (t : ℂ) := if t = 0 then b else b₀ t
  have ha'₀ : a' 0 = a := if_pos rfl
  have hb'₀ : b' 0 = b := if_pos rfl
  have hcZ (t : ℂ) (ht : t ∉ S) (σ : Equiv.Perm ι) :
      c t * Z (x t) (y t) σ = P * (V σ).eval t / Q.eval t := by
    simp only [c, V, Z, x, y, eval_add, eval_mul, eval_pow, eval_C]
    field_simp [hd t ht, hQ t ht] <;> ring
  have hZ (t : ℂ) (ht : t ∉ S) (σ : Equiv.Perm ι) :
      matchingProduct (a' t) (b' t) σ = P * (V σ).eval t / Q.eval t := by
    by_cases ht₀ : t = 0
    · subst t
      rw [ha'₀, hb'₀, hV₀, hQ₀, mul_left_comm P, mul_div_cancel_right₀ _ (mul_ne_zero hP₀
        (pow_ne_zero _ hd₀))]
    · rw [show a' t = a₀ t from if_neg ht₀, show b' t = b₀ t from if_neg ht₀, hab₀]
      exact hcZ t ht σ
  have heval (t : ℂ) : (∑ σ, signedWeight U σ * (V σ).eval t) - (V r).eval t = Q.eval t := by
    simp only [V, Q, eval_add, eval_mul, eval_pow, eval_C, mul_add, Finset.sum_add_distrib,
      ← mul_assoc, ← Finset.sum_mul, P, G]
    ring
  have hrel (t : ℂ) :
      P * ((V r).eval t - (V s).eval t) = H * Q.eval t := by
    have h := congrArg (Polynomial.eval t) hslice
    simp only [eval_add, eval_mul, eval_C, eval_zero, A, B, D] at h
    simp only [V, Q, eval_add, eval_mul, eval_pow, eval_C]
    dsimp only [H] at h ⊢
    linear_combination h
  have hdef (t : ℂ) (ht : t ∉ S) :
      determinantValue (a' t) (b' t) U - matchingProduct (a' t) (b' t) r = P := by
    rw [← signed_determinant _ _ U hU]
    simp_rw [hZ t ht]
    calc
      _ = P / Q.eval t * ((∑ σ, signedWeight U σ * (V σ).eval t) - (V r).eval t) := by
        rw [mul_sub, Finset.mul_sum]
        congr 1
        · apply Finset.sum_congr rfl
          intro σ _
          ring
        · ring
      _ = P := by rw [heval, div_mul_cancel₀ _ (hQ t ht)]
  let J : Finset (Equiv.Perm ι) := (Finset.univ.erase r).erase s
  have hJ (σ : Equiv.Perm ι) : σ ∈ J ↔ σ ≠ r ∧ σ ≠ s := by
    simp [J, and_comm]
  have hfixed (t : ℂ) (ht : t ∉ S) (σ : Equiv.Perm ι) (hσ : σ ∉ J) :
      matchingProduct (a' t) (b' t) r - matchingProduct (a' t) (b' t) σ = z₀ r - z₀ σ := by
    by_cases hr : σ = r
    · simp [hr]
    have hs : σ = s := not_not.mp (fun hn => hσ ((hJ σ).2 ⟨hr, hn⟩))
    subst σ
    rw [hZ t ht r, hZ t ht s, ← sub_div, ← mul_sub, hrel, mul_div_cancel_right₀ _ (hQ t ht)]
  have hchange : ∃ t ∉ S, ∃ σ, z₀ σ ≠ matchingProduct (a' t) (b' t) σ := by
    obtain ⟨t, ht⟩ := (hS.insert (0 : ℂ)).exists_not_mem
    have ht₀ : t ≠ 0 := fun h => ht (Or.inl h)
    have htS : t ∉ S := fun h => ht (Or.inr h)
    have hxy : x t ≠ 0 ∨ y t ≠ 0 := by
      rcases hfree with hp | hq
      · left
        simpa only [x, hp, eval_mul, eval_X, mul_div_cancel_right₀ _ (hd t htS)] using ht₀
      · right
        simpa only [y, hq, eval_mul, eval_X, mul_div_cancel_right₀ _ (hd t htS)] using ht₀
    obtain ⟨σ, hσ⟩ := hmove (x t) (y t) (c t) hxy
      (div_ne_zero (mul_ne_zero hP₀ (pow_ne_zero _ (hd t htS))) (hQ t htS))
    refine ⟨t, htS, σ, ?_⟩
    rwa [hZ t htS, ← hcZ t htS]
  have hkeep (σ : Equiv.Perm ι) (hσ : σ ∉ J) : matchingGap a b η r σ = 0 := by
    by_cases hr : σ = r
    · simp [hr, matchingGap]
    have hs : σ = s := not_not.mp (fun hn => hσ ((hJ σ).2 ⟨hr, hn⟩))
    simpa only [hs] using htie
  obtain ⟨v, hv, hall, hold, ⟨τ, hτ, hτzero⟩, hg', _⟩ :=
    exists_new_matching_contact_on_rational_slice hS a' b' U η hη r r J i j k l
      hij hik hil hjk hjl hkl hzero (by rwa [ha'₀]) (by rwa [hb'₀]) (by rwa [ha'₀, hb'₀])
      (fun t ht σ hσ => by rw [ha'₀, hb'₀]; exact hfixed t ht σ hσ)
      (fun σ hσ => by rw [ha'₀, hb'₀]; exact hkeep σ hσ)
      (fun σ hσ => by
        rw [ha'₀, hb'₀]
        exact hstart σ ((hJ σ).1 hσ).1 ((hJ σ).1 hσ).2)
      (by rw [ha'₀, hb'₀]; exact hchange)
      (fun σ => C (η * P) * (V r - V σ)) (fun _ => Q) (fun _ _ => hQ)
      (fun σ _ t ht => by simp only [hZ t ht, eval_mul, eval_C, eval_sub]; ring)
      hg (fun t ht => by rw [hdef t ht, hPg])
  have hvdata := (hbad v).1 hv
  have hvnz (σ : Equiv.Perm ι) : matchingProduct (a' v) (b' v) σ ≠ 0 := by
    rw [hZ v hv]
    exact div_ne_zero (mul_ne_zero hP₀ (hvdata.1.2 σ)) (hQ v hv)
  refine ⟨a' v, b' v, ?_, ?_, hall, hold s (by simp [hJ]),
    ⟨τ, ((hJ τ).1 hτ).1, ((hJ τ).1 hτ).2, hτzero⟩, hg'⟩
  · intro i j h
    apply hvnz (Equiv.swap j i)
    unfold matchingProduct
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simpa only [Equiv.swap_apply_left] using h
  · intro σ τ he
    apply Classical.byContradiction
    intro hne
    refine hvdata.2 ⟨(σ, τ), hne⟩ ?_
    rw [hZ v hv σ, hZ v hv τ] at he
    exact sub_eq_zero.mpr (mul_left_cancel₀ hP₀ ((div_left_inj' (hQ v hv)).mp he))

/-- Two tied support matchings at a regular strict violation can be joined by
a third matching. The relative unitary, support direction, and positive gap
are preserved. Two columns in the anchored chart suffice for the deformation. -/
theorem exists_third_matching_contact [Nonempty ι]
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ) (hη : η ≠ 0)
    (r s : Equiv.Perm ι) (i j k l : ι) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (ha : Function.Injective a) (hb : Function.Injective b) (hnz : ∀ i j, a i + b j ≠ 0)
    (hinj : Function.Injective (matchingProduct a b))
    (htie : matchingGap a b η r s = 0)
    (hstart : ∀ σ, σ ≠ r → σ ≠ s → 0 < matchingGap a b η r σ)
    (hstrict : (η * matchingProduct a b r).re < (η * determinantValue a b U).re) :
    ∃ a' b' : ι → ℂ, (∀ i j, a' i + b' j ≠ 0) ∧ Function.Injective (matchingProduct a' b') ∧
      (∀ σ, 0 ≤ matchingGap a' b' η r σ) ∧ matchingGap a' b' η r s = 0 ∧
      (∃ τ, τ ≠ r ∧ τ ≠ s ∧ matchingGap a' b' η r τ = 0) ∧
      (η * determinantValue a' b' U).re - (η * matchingProduct a' b' r).re =
        (η * determinantValue a b U).re - (η * matchingProduct a b r).re := by
  classical
  obtain ⟨c, x, y, hx, hy, hunit, hpiv, hchart, hspec⟩ :=
    exists_anchored_chart_of_nonopposite_spectra a b i i j j hnz (ha.ne hij.symm) (hb.ne hij.symm)
  let Y (t u : ℂ) := Function.update (Function.update y j (y j + t)) k (y k + u)
  have hYj (t u : ℂ) : Y t u j = y j + t := by simp [Y, hjk]
  have hYk (t u : ℂ) : Y t u k = y k + u := by simp [Y]
  have hYother (t u : ℂ) (m : ι) (hmj : m ≠ j) (hmk : m ≠ k) : Y t u m = y m := by
    simp [Y, hmj, hmk]
  have hY₀ : Y 0 0 = y := by
    funext m
    by_cases hmj : m = j
    · simp [hmj, hYj]
    by_cases hmk : m = k
    · simp [hmk, hYk]
    exact hYother _ _ _ hmj hmk
  let Z (t u : ℂ) := anchoredMatchingCoordinate c x (Y t u)
  have hZ₀ (σ : Equiv.Perm ι) : Z 0 0 σ = matchingProduct a b σ := by
    rw [hspec σ]
    simp only [Z, hY₀]
  let T : Finset ι := {j, k}
  let R (σ : Equiv.Perm ι) := c * ∏ m ∈ Tᶜ, (1 - x (σ m) * y m)
  have hfactor (t u : ℂ) (σ : Equiv.Perm ι) :
      Z t u σ = R σ * (1 - x (σ j) * (y j + t)) * (1 - x (σ k) * (y k + u)) := by
    let f (m : ι) := 1 - x (σ m) * Y t u m
    have hout : (∏ m ∈ Tᶜ, f m) = ∏ m ∈ Tᶜ, (1 - x (σ m) * y m) := by
      apply Finset.prod_congr rfl
      intro m hm
      have hmk : m ≠ j ∧ m ≠ k := by simpa [T, not_or] using Finset.mem_compl.mp hm
      simp only [f, hYother t u m hmk.1 hmk.2]
    have hin : (∏ m ∈ T, f m) = f j * f k := by
      dsimp only [T]
      rw [Finset.prod_insert (show j ∉ ({k} : Finset ι) by simpa using hjk),
        Finset.prod_singleton]
    change c * (∏ m, f m) = _
    rw [← Finset.prod_compl_mul_prod T f, hout, hin]
    simp only [R, f, hYj, hYk]
    ring
  let L (σ : Equiv.Perm ι) := Z 1 0 σ - Z 0 0 σ
  let M (σ : Equiv.Perm ι) := Z 0 1 σ - Z 0 0 σ
  let N (σ : Equiv.Perm ι) := Z 1 1 σ - Z 1 0 σ - Z 0 1 σ + Z 0 0 σ
  have hZ (t u : ℂ) (σ : Equiv.Perm ι) :
      Z t u σ = matchingProduct a b σ + L σ * t + M σ * u + N σ * t * u := by
    rw [← hZ₀]
    simp only [L, M, N, hfactor]
    ring
  apply exists_two_contact_progression_of_bilinear_family a b U hU η hη r s i j k l
    hij hik hil hjk hjl hkl ha hb hnz hinj htie hstart hstrict L M N
  · intro t u d
    obtain ⟨a', b', h⟩ := exists_spectra_of_anchoredMatchingCoordinate (d * c) x (Y t u)
    refine ⟨a', b', fun σ => ?_⟩
    rw [← hZ, h σ]
    simp only [Z, anchoredMatchingCoordinate, mul_assoc]
  · intro t u d htu _
    by_contra! hsame
    have heq (σ : Equiv.Perm ι) :
        anchoredMatchingCoordinate c x y σ = anchoredMatchingCoordinate (d * c) x (Y t u) σ := by
      rw [← hspec, hsame, ← hZ]
      simp only [Z, anchoredMatchingCoordinate, mul_assoc]
    have hy' : Y t u i = 0 := (hYother t u i hij hik).trans hy
    have hYeq := (anchored_chart_eq_of_matchingCoordinates_eq c (d * c) x y x (Y t u)
      i i j j hx hy hx hy' hunit hunit hpiv hchart heq).2.2
    rcases htu with ht | hu
    · have he := congrFun hYeq j
      rw [hYj] at he
      exact ht (by linear_combination -he)
    · have he := congrFun hYeq k
      rw [hYk] at he
      exact hu (by linear_combination -he)

end MOC
