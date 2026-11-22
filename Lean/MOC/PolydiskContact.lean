import MOC.AffineContact
import MOC.ConcentricPerturbation
import MOC.Weights

/-! Extremizing spectral energy among optimal points of a polydisk
rules out an interior coordinate when the affine envelope has at most two contacts. -/

open BigOperators Filter Matrix
open scoped Topology

namespace MOC

noncomputable section

private theorem affine_disk_energy_contradiction {J : Type*} [Fintype J]
    (s : J → ℂ) (b : J → ℝ) (x : ℂ) (H : ℝ)
    (hx : ‖x‖ < 1) (hupper : ∀ j, (s j * x).re + b j ≤ H)
    (hmin : ∀ y, ‖y‖ ≤ 1 → ∃ j, H ≤ (s j * y).re + b j)
    (henergy : ∀ y, ‖y‖ ≤ 1 → (∀ j, (s j * y).re + b j ≤ H) →
      Complex.normSq y ≤ Complex.normSq x)
    (r q : J) (hactive : ∀ j, (s j * x).re + b j = H → j = r ∨ j = q) : False := by
  let d := s r - s q
  obtain ⟨v, hv, heq⟩ : ∃ v : ℂ, v ≠ 0 ∧ (s r * v).re = (s q * v).re := by
    by_cases hd : d = 0
    · exact ⟨1, one_ne_zero, by rw [sub_eq_zero.mp hd]⟩
    · refine ⟨Complex.I * star d, mul_ne_zero Complex.I_ne_zero (star_ne_zero.mpr hd), ?_⟩
      have he : (d * (Complex.I * star d)).re = 0 := by
        rw [mul_left_comm d, Complex.star_def, Complex.mul_conj]
        simp [Complex.mul_re]
      exact sub_eq_zero.mp (by simpa only [d, sub_mul, Complex.sub_re] using he)
  let y (w : ℂ) (t : ℝ) := x + (t : ℂ) * w
  have hy (w : ℂ) (t : ℝ) (j : J) :
      (s j * y w t).re + b j = (s j * x).re + b j + t * (s j * w).re := by
    dsimp only [y]
    rw [mul_add, mul_left_comm (s j), Complex.add_re, Complex.re_ofReal_mul]
    ring
  have hnear (w : ℂ) : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ‖y w t‖ < 1 ∧
      ∀ j, (s j * x).re + b j ≠ H → (s j * y w t).re + b j < H := by
    have hn : ContinuousAt (fun t : ℝ => ‖y w t‖) 0 := by unfold y; fun_prop
    have hb : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ‖y w t‖ < 1 :=
      hn.eventually_lt continuousAt_const (by simpa [y] using hx)
    have hc (j : J) : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
        (s j * x).re + b j ≠ H → (s j * y w t).re + b j < H := by
      by_cases hh : (s j * x).re + b j = H
      · exact Eventually.of_forall (fun _ hn => False.elim (hn hh))
      · have hc : ContinuousAt (fun t : ℝ => (s j * y w t).re + b j) 0 := by unfold y; fun_prop
        refine (hc.eventually_lt continuousAt_const ?_).mono (fun _ ht _ => ht)
        simpa [y] using lt_of_le_of_ne (hupper j) hh
    exact (hb.and (Filter.eventually_all.mpr hc)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ⟨hplus, hminus⟩, ht⟩ :=
    (((hnear v).and (hnear (-v))).and self_mem_nhdsWithin).exists
  change 0 < t at ht
  have hslope (j : J) (hj : (s j * x).re + b j = H) :
      (s j * v).re = (s r * v).re := by
    rcases hactive j hj with rfl | rfl
    · rfl
    · exact heq.symm
  obtain ⟨j, hj⟩ := hmin (y v t) hplus.1.le
  obtain ⟨k, hk⟩ := hmin (y (-v) t) hminus.1.le
  have hjx : (s j * x).re + b j = H := by
    by_contra hn
    exact (not_lt_of_ge hj) (hplus.2 j hn)
  have hkx : (s k * x).re + b k = H := by
    by_contra hn
    exact (not_lt_of_ge hk) (hminus.2 k hn)
  rw [hy, hjx, hslope j hjx] at hj
  rw [hy, hkx, mul_neg, Complex.neg_re, hslope k hkx] at hk
  have hz : (s r * v).re = 0 := by
    have h₁ : 0 ≤ t * (s r * v).re := by linarith only [hj]
    have h₂ : t * (s r * v).re ≤ 0 := by linarith only [hk]
    exact (mul_eq_zero.mp (le_antisymm h₂ h₁)).resolve_left ht.ne'
  have hflat (j : J) (hj : (s j * x).re + b j = H) :
      (s j * v).re = 0 := (hslope j hj).trans hz
  have h₁ := henergy (y v t) hplus.1.le (fun j => by
    by_cases hj : (s j * x).re + b j = H
    · rw [hy, hj, hflat j hj, mul_zero, add_zero]
    · exact (hplus.2 j hj).le)
  have h₂ := henergy (y (-v) t) hminus.1.le (fun j => by
    by_cases hj : (s j * x).re + b j = H
    · rw [hy, hj, mul_neg, Complex.neg_re, hflat j hj, neg_zero, mul_zero, add_zero]
    · exact (hminus.2 j hj).le)
  let w := (t : ℂ) * v
  change Complex.normSq (x + w) ≤ Complex.normSq x at h₁
  have h₂' : Complex.normSq (x - w) ≤ Complex.normSq x := by
    simpa only [y, w, mul_neg, sub_eq_add_neg] using h₂
  rw [Complex.normSq_add] at h₁
  rw [Complex.normSq_sub] at h₂'
  have hp : 0 < Complex.normSq w := Complex.normSq_pos.mpr
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne') hv)
  linarith only [h₁, h₂', hp]

private abbrev DiskSpectra (n : ℕ) := Fin n ⊕ Fin n → ℂ

private def diskMatching {n : ℕ} (x : DiskSpectra n) (σ : Equiv.Perm (Fin n)) : ℂ :=
  matchingProduct (fun i => x (.inl i)) (fun j => x (.inr j)) σ

private theorem diskMatching_update {n : ℕ} (x : DiskSpectra n) (k : Fin n ⊕ Fin n)
    (σ : Equiv.Perm (Fin n)) (z : ℂ) :
    diskMatching (Function.update x k z) σ =
      z * (diskMatching (Function.update x k 1) σ -
        diskMatching (Function.update x k 0) σ) + diskMatching (Function.update x k 0) σ := by
  cases k with
  | inl i =>
    let j := σ.symm i
    let p := ∏ l ∈ Finset.univ.erase j, (x (.inl (σ l)) + x (.inr l))
    have hp (w : ℂ) : diskMatching (Function.update x (.inl i) w) σ =
        (w + x (.inr j)) * p := by
      unfold diskMatching matchingProduct
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
      have hj : σ j = i := σ.apply_symm_apply i
      have hfirst : Function.update x (.inl i) w (.inl (σ j)) = w := by
        rw [congrArg (Sum.inl : Fin n → Fin n ⊕ Fin n) hj, Function.update_self]
      dsimp only
      rw [hfirst, Function.update_of_ne (by simp : Sum.inr j ≠ Sum.inl i)]
      apply congrArg ((w + x (.inr j)) * ·)
      apply Finset.prod_congr rfl
      intro l hl
      have h : σ l ≠ i := by
        rw [← hj]
        exact σ.injective.ne (Finset.mem_erase.mp hl).1
      have hleft : (Sum.inl (σ l) : Fin n ⊕ Fin n) ≠ Sum.inl i := Sum.inl_injective.ne h
      rw [Function.update_of_ne hleft,
        Function.update_of_ne (by simp : Sum.inr l ≠ Sum.inl i)]
    rw [hp z, hp 1, hp 0]
    ring
  | inr j =>
    let p := ∏ l ∈ Finset.univ.erase j, (x (.inl (σ l)) + x (.inr l))
    have hp (w : ℂ) : diskMatching (Function.update x (.inr j) w) σ =
        (x (.inl (σ j)) + w) * p := by
      unfold diskMatching matchingProduct
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
      simp only [Function.update_self, Function.update_of_ne (by simp : Sum.inl (σ j) ≠ Sum.inr j)]
      apply congrArg ((x (.inl (σ j)) + w) * ·)
      apply Finset.prod_congr rfl
      intro l hl
      have hright : (Sum.inr l : Fin n ⊕ Fin n) ≠ Sum.inr j :=
        Sum.inr_injective.ne (Finset.mem_erase.mp hl).1
      rw [Function.update_of_ne (by simp : Sum.inl (σ l) ≠ Sum.inr j),
        Function.update_of_ne hright]
    rw [hp z, hp 1, hp 0]
    ring

/-- For a fixed mixer and support direction with a strict violation in the
unit polydisk, the largest support excess on that polydisk is attained at
spectra with at least three maximizing permutation labels. -/
theorem exists_polydisk_maximum_three_contacts {n : ℕ}
    (a₀ b₀ : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) (η : ℂ)
    (ha₀ : ∀ i, ‖a₀ i‖ ≤ 1) (hb₀ : ∀ i, ‖b₀ i‖ ≤ 1)
    (hsep : ∀ σ : Equiv.Perm (Fin n),
      (η * (matchingProduct a₀ b₀ σ - determinantValue a₀ b₀ U)).re < 0) :
    ∃ (a b : Fin n → ℂ) (H : ℝ), (∀ i, ‖a i‖ ≤ 1) ∧ (∀ i, ‖b i‖ ≤ 1) ∧ H < 0 ∧
      (∀ σ : Equiv.Perm (Fin n), (η * (matchingProduct a b σ - determinantValue a b U)).re ≤ H) ∧
      (∀ c d : Fin n → ℂ, (∀ i, ‖c i‖ ≤ 1) → (∀ i, ‖d i‖ ≤ 1) →
        ∃ σ : Equiv.Perm (Fin n), H ≤ (η * (matchingProduct c d σ - determinantValue c d U)).re) ∧
      3 ≤ (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
        (η * (matchingProduct a b σ - determinantValue a b U)).re = H).card := by
  classical
  let K : Set (DiskSpectra n) := Set.univ.pi fun _ => Metric.closedBall 0 1
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hmem (x : DiskSpectra n) : x ∈ K ↔ ∀ k, ‖x k‖ ≤ 1 := by
    simp [K, Set.mem_pi, Metric.mem_closedBall, dist_zero_right]
  let x₀ := Sum.elim a₀ b₀
  have hx₀ : x₀ ∈ K := (hmem x₀).mpr fun k => by
    cases k with
    | inl i => exact ha₀ i
    | inr i => exact hb₀ i
  let D (x : DiskSpectra n) := determinantValue (fun i => x (.inl i)) (fun j => x (.inr j)) U
  let f (x : DiskSpectra n) (σ : Equiv.Perm (Fin n)) := (η * (diskMatching x σ - D x)).re
  let J : Finset (Equiv.Perm (Fin n)) := Finset.univ
  have hJ : J.Nonempty := ⟨1, Finset.mem_univ _⟩
  let F (x : DiskSpectra n) := J.sup' hJ (f x)
  have hd : Continuous D := by unfold D determinantValue; fun_prop
  have hf (σ : Equiv.Perm (Fin n)) : Continuous (fun x => f x σ) := by
    have hp : Continuous (fun x : DiskSpectra n => diskMatching x σ) := by
      unfold diskMatching matchingProduct
      exact continuous_finset_prod _ fun _ _ => by fun_prop
    exact Complex.continuous_re.comp (continuous_const.mul (hp.sub hd))
  have hF : Continuous F := Continuous.finset_sup'_apply hJ fun σ _ => hf σ
  obtain ⟨x₁, hx₁, hmin₁⟩ := hK.exists_isMinOn ⟨x₀,hx₀⟩ hF.continuousOn
  let H := F x₁
  have hH : H < 0 :=
    (hmin₁ hx₀).trans_lt ((Finset.sup'_lt_iff hJ).mpr fun σ _ => hsep σ)
  let S := K ∩ {x | F x ≤ H}
  have hS : IsCompact S := hK.inter_right (isClosed_le hF continuous_const)
  let E (x : DiskSpectra n) : ℝ := ∑ k, Complex.normSq (x k)
  have hE : Continuous E :=
    continuous_finset_sum _ fun _ _ => Complex.continuous_normSq.comp (by fun_prop)
  obtain ⟨x, hx, hEmax⟩ := hS.exists_isMaxOn ⟨x₁, hx₁, show F x₁ ≤ H from le_rfl⟩ hE.continuousOn
  have hle (σ : Equiv.Perm (Fin n)) : f x σ ≤ H :=
    (Finset.le_sup' (f x) (Finset.mem_univ σ)).trans hx.2
  have hglobal (y : DiskSpectra n) (hy : y ∈ K) : ∃ σ, H ≤ f y σ := by
    have hFy : H ≤ J.sup' hJ (f y) := hmin₁ hy
    obtain ⟨σ, _, hσ⟩ := (Finset.le_sup'_iff hJ).mp hFy
    exact ⟨σ, hσ⟩
  let a (i : Fin n) := x (.inl i)
  let b (i : Fin n) := x (.inr i)
  refine ⟨a, b, H, fun i => (hmem x).mp hx.1 (.inl i), fun i => (hmem x).mp hx.1 (.inr i),
    hH, hle, ?_, ?_⟩
  · intro c d hc hd
    exact hglobal (Sum.elim c d) ((hmem _).mpr fun k => by
      cases k with
      | inl i => exact hc i
      | inr i => exact hd i)
  let C := J.filter fun σ => f x σ = H
  change 3 ≤ C.card
  by_cases hcard : 3 ≤ C.card
  · exact hcard
  exfalso
  have hcard' : C.card < 3 := Nat.lt_of_not_ge hcard
  have hC : C.Nonempty := by
    obtain ⟨r, hr⟩ := hglobal x hx.1
    exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, le_antisymm (hle r) hr⟩⟩
  obtain ⟨r, q, hcover⟩ : ∃ r q, ∀ σ ∈ C, σ = r ∨ σ = q := by
    have hpos := Finset.card_pos.mpr hC
    by_cases h : C.card = 1
    · obtain ⟨r, hr⟩ := Finset.card_eq_one.mp h
      exact ⟨r, r, fun σ hσ => Or.inl (by simpa only [hr, Finset.mem_singleton] using hσ)⟩
    · obtain ⟨r, q, _, hrq⟩ := Finset.card_eq_two.mp (show C.card = 2 by omega)
      exact ⟨r, q, fun σ hσ => by simpa only [hrq, Finset.mem_insert, Finset.mem_singleton] using hσ⟩
  have hboundary (k : Fin n ⊕ Fin n) : ‖x k‖ = 1 := by
    by_cases hk : 1 ≤ ‖x k‖
    · exact le_antisymm ((hmem x).mp hx.1 k) hk
    exfalso
    have hk' : ‖x k‖ < 1 := lt_of_not_ge hk
    let u (z : ℂ) := Function.update x k z
    have hux : u (x k) = x := by simp [u]
    have hu (z : ℂ) (hz : ‖z‖ ≤ 1) : u z ∈ K := (hmem _).mpr (fun l => by
      by_cases hl : l = k
      · subst l; simpa [u] using hz
      · simpa only [u, Function.update_of_ne hl] using (hmem x).mp hx.1 l)
    have hD (z : ℂ) : D (u z) = z * (D (u 1) - D (u 0)) + D (u 0) := by
      have hsum (w : ℂ) : D (u w) = ∑ σ, signedWeight U σ * diskMatching (u w) σ :=
        (signed_determinant _ _ U hU).symm
      rw [hsum z, hsum 1, hsum 0, ← Finset.sum_sub_distrib, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro σ _
      rw [show u z = Function.update x k z from rfl, diskMatching_update]
      change _ = z * (signedWeight U σ * diskMatching (u 1) σ -
        signedWeight U σ * diskMatching (u 0) σ) + _
      ring
    let s (σ : Equiv.Perm (Fin n)) := η * ((diskMatching (u 1) σ -
      diskMatching (u 0) σ) - (D (u 1) - D (u 0)))
    let c (σ : Equiv.Perm (Fin n)) := f (u 0) σ
    have haff (z : ℂ) (σ : Equiv.Perm (Fin n)) : (s σ * z).re + c σ = f (u z) σ := by
      have hM : diskMatching (u z) σ = z * (diskMatching (u 1) σ - diskMatching (u 0) σ) +
          diskMatching (u 0) σ := diskMatching_update x k σ z
      dsimp only [s, c, f]
      rw [← Complex.add_re, hD z, hM]
      congr 1
      ring
    have hbase (σ : Equiv.Perm (Fin n)) : (s σ * x k).re + c σ = f x σ := by
      rw [haff, hux]
    refine affine_disk_energy_contradiction s c (x k) H hk' (fun σ => (hbase σ).trans_le (hle σ))
      (fun z hz => ?_) (fun z hz h => ?_) r q (fun σ h => ?_)
    · obtain ⟨σ, hσ⟩ := hglobal (u z) (hu z hz)
      exact ⟨σ, hσ.trans_eq (haff z σ).symm⟩
    · have hzS : u z ∈ S := ⟨hu z hz, (Finset.sup'_le_iff hJ (f (u z))).mpr fun σ _ =>
          by rw [← haff]; exact h σ⟩
      have hEz : E (u z) ≤ E x := hEmax hzS
      have hrest : (∑ l ∈ Finset.univ.erase k, Complex.normSq (u z l)) =
          ∑ l ∈ Finset.univ.erase k, Complex.normSq (x l) := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [show u z l = x l from Function.update_of_ne (Finset.mem_erase.mp hl).1 z x]
      dsimp only [E] at hEz
      rw [← Finset.add_sum_erase Finset.univ (fun l => Complex.normSq (u z l)) (Finset.mem_univ k),
        ← Finset.add_sum_erase Finset.univ (fun l => Complex.normSq (x l)) (Finset.mem_univ k),
        hrest] at hEz
      simpa only [u, Function.update_self, add_le_add_iff_right] using hEz
    · exact hcover σ (Finset.mem_filter.mpr ⟨Finset.mem_univ σ, (hbase σ).symm.trans h⟩)
  have ha (i : Fin n) : Complex.normSq (a i) = 1 := by
    simp [a, Complex.normSq_eq_norm_sq, hboundary (.inl i)]
  have hb (i : Fin n) : Complex.normSq (b i) = 1 := by
    simp [b, Complex.normSq_eq_norm_sq, hboundary (.inr i)]
  have hhold := holds_of_concentric_circles a b 1 1 ha hb U hU
  obtain ⟨σ, hσ⟩ := (holds_iff_directional a b U).mp hhold η
  have hs : 0 ≤ f x σ := by
    change 0 ≤ (η * (matchingProduct a b σ - determinantValue a b U)).re
    rw [mul_sub, Complex.sub_re, sub_nonneg]
    exact hσ
  exact (not_lt_of_ge hs) ((hle σ).trans_lt hH)

end

end MOC
