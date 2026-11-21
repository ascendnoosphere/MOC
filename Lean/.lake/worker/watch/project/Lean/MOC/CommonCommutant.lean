import MOC.DruryResolvent
import MOC.SupportBlocks

/-! A proper pair of support blocks is the obstruction to a scalar common
commutant for two simple diagonal spectra. -/

open Matrix

namespace MOC

noncomputable section

variable {n : ℕ}

private theorem diagonal_of_commute_simple_diagonal {a : Fin n → ℂ}
    (ha : Function.Injective a) {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : Commute (diagonal a) Y) : Y = diagonal Y.diag := by
  ext i j : 1
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.diag_apply]
  · have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) h.eq
    change (diagonal a * Y) i j = (Y * diagonal a) i j at he
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm (Y i j)] at he
    have hzero : (a i - a j) * Y i j = 0 := by rw [sub_mul, he, sub_self]
    rw [Matrix.diagonal_apply_ne _ hij]
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr fun he => hij (ha he))

private theorem constant_left_labels_of_diagonal_intertwining [Nonempty (Fin n)]
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : IsUnitary U)
    (hexpand : ∀ s : Finset (Fin n), s.Nonempty → (∃ i, i ∉ s) →
      s.card < (supportColumns U s).card)
    (a b : Fin n → ℂ) (h : diagonal a * U = U * diagonal b) :
    ∃ μ : ℂ, a = fun _ => μ := by
  classical
  let i₀ : Fin n := Classical.choice ‹Nonempty (Fin n)›
  let μ := a i₀
  let s := Finset.univ.filter (fun i : Fin n => a i = μ)
  let t := Finset.univ.filter (fun j : Fin n => b j = μ)
  have hs (i : Fin n) : i ∈ s ↔ a i = μ := by simp [s]
  have ht (j : Fin n) : j ∈ t ↔ b j = μ := by simp [t]
  have hentry (i j : Fin n) (hu : U i j ≠ 0) : a i = b j := by
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) h
    change (diagonal a * U) i j = (U * diagonal b) i j at he
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm (U i j)] at he
    exact mul_right_cancel₀ hu he
  have hzero (i : Fin n) (hi : i ∈ s) (j : Fin n) (hj : j ∉ t) : U i j = 0 := by
    by_contra hu
    exact hj ((ht j).mpr ((hentry i j hu).symm.trans ((hs i).mp hi)))
  have hother (i : Fin n) (hi : i ∉ s) (j : Fin n) (hj : j ∈ t) : U i j = 0 := by
    by_contra hu
    exact hi ((hs i).mpr ((hentry i j hu).trans ((ht j).mp hj)))
  have hcard := card_eq_of_unitary_closed_support_cut hU s t hzero hother
  have hcols : supportColumns U s ⊆ t := by
    intro j hj
    obtain ⟨i, hi, hu⟩ : ∃ i ∈ s, U i j ≠ 0 := (Finset.mem_filter.mp hj).2
    exact (ht j).mpr ((hentry i j hu).symm.trans ((hs i).mp hi))
  have hle : (supportColumns U s).card ≤ s.card := by
    rw [hcard]
    exact Finset.card_le_card hcols
  refine ⟨μ, ?_⟩
  funext i
  by_contra hi
  exact (not_lt_of_ge hle) (hexpand s ⟨i₀, (hs i₀).mpr rfl⟩
    ⟨i, fun him => hi ((hs i).mp him)⟩)

/-- With simple spectra and strict support expansion in the change of basis,
every matrix commuting with both summands is a scalar. -/
theorem scalar_of_commute_simple_summands_of_strict_support_expansion [Nonempty (Fin n)]
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : IsUnitary U)
    (hexpand : ∀ s : Finset (Fin n), s.Nonempty → (∃ i, i ∉ s) →
      s.card < (supportColumns U s).card)
    {a c : Fin n → ℂ} (ha : Function.Injective a) (hc : Function.Injective c)
    (Y : Matrix (Fin n) (Fin n) ℂ) (hAY : Commute (diagonal a) Y)
    (hCY : Commute (U * diagonal c * Uᴴ) Y) :
    ∃ μ : ℂ, Y = μ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  let C := U * diagonal c * Uᴴ
  let Z := Uᴴ * Y * U
  have hDZ : Commute (diagonal c) Z := by
    change diagonal c * Z = Z * diagonal c
    calc
      _ = Uᴴ * (C * Y) * U := by
        simp only [Z, C, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Uᴴ U, hU.2, Matrix.one_mul]
      _ = Uᴴ * (Y * C) * U := by rw [show C * Y = Y * C from hCY.eq]
      _ = _ := by simp only [Z, C, Matrix.mul_assoc, hU.2, Matrix.mul_one]
  have hYZ : Y * U = U * Z := by
    simp only [Z, ← Matrix.mul_assoc, hU.1, Matrix.one_mul]
  have hY := diagonal_of_commute_simple_diagonal ha hAY
  have hZ := diagonal_of_commute_simple_diagonal hc hDZ
  have hdiag : diagonal Y.diag * U = U * diagonal Z.diag := by
    calc
      _ = Y * U := by rw [← hY]
      _ = U * Z := hYZ
      _ = _ := by rw [← hZ]
  obtain ⟨μ, hμ⟩ := constant_left_labels_of_diagonal_intertwining hU hexpand _ _ hdiag
  exact ⟨μ, hY.trans ((congrArg diagonal hμ).trans (Matrix.smul_one_eq_diagonal μ).symm)⟩

/-- With simple spectra and no proper paired blocks in the change of basis,
every matrix commuting with both summands is a scalar. -/
theorem scalar_of_commute_simple_summands [Nonempty (Fin n)]
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : IsUnitary U) (hcut : ¬ HasProperPairedBlocks U)
    {a c : Fin n → ℂ} (ha : Function.Injective a) (hc : Function.Injective c)
    (Y : Matrix (Fin n) (Fin n) ℂ) (hAY : Commute (diagonal a) Y)
    (hCY : Commute (U * diagonal c * Uᴴ) Y) :
    ∃ μ : ℂ, Y = μ • (1 : Matrix (Fin n) (Fin n) ℂ) :=
  scalar_of_commute_simple_summands_of_strict_support_expansion hU
    (card_lt_supportColumns_of_no_paired_blocks hU hcut) ha hc Y hAY hCY

/-- The scalar commutant condition in Drury's resolvent equation follows from
simple spectra and strict support expansion. -/
theorem scalar_of_commute_simple_resolvent_summands_of_strict_support_expansion
    [Nonempty (Fin n)] {U : Matrix (Fin n) (Fin n) ℂ} (hU : IsUnitary U)
    (hexpand : ∀ s : Finset (Fin n), s.Nonempty → (∃ i, i ∉ s) →
      s.card < (supportColumns U s).card)
    {a c : Fin n → ℂ} (ha : Function.Injective a) (hc : Function.Injective c)
    (hinv : IsUnit (diagonal a).det) (Y : Matrix (Fin n) (Fin n) ℂ)
    (hAY : Commute (diagonal a) Y)
    (hXY : Commute ((U * diagonal c * Uᴴ) * (diagonal a)⁻¹) Y) :
    ∃ μ : ℂ, Y = μ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have h := hXY.mul_left hAY
  rw [Matrix.mul_assoc (U * diagonal c * Uᴴ), (diagonal a).nonsing_inv_mul hinv, Matrix.mul_one] at h
  exact scalar_of_commute_simple_summands_of_strict_support_expansion hU hexpand ha hc Y hAY h

/-- The scalar commutant condition in Drury's resolvent equation follows from
simple spectra and the same support condition used in the least-order reduction. -/
theorem scalar_of_commute_simple_resolvent_summands [Nonempty (Fin n)]
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : IsUnitary U) (hcut : ¬ HasProperPairedBlocks U)
    {a c : Fin n → ℂ} (ha : Function.Injective a) (hc : Function.Injective c)
    (hinv : IsUnit (diagonal a).det) (Y : Matrix (Fin n) (Fin n) ℂ)
    (hAY : Commute (diagonal a) Y)
    (hXY : Commute ((U * diagonal c * Uᴴ) * (diagonal a)⁻¹) Y) :
    ∃ μ : ℂ, Y = μ • (1 : Matrix (Fin n) (Fin n) ℂ) :=
  scalar_of_commute_simple_resolvent_summands_of_strict_support_expansion hU
    (card_lt_supportColumns_of_no_paired_blocks hU hcut) ha hc hinv Y hAY hXY

private theorem not_commute_simple_summands_of_strict_support_expansion
    [Nonempty (Fin n)] (hn : 2 ≤ n)
    {a c : Fin n → ℂ} (ha : Function.Injective a) (hc : Function.Injective c)
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : IsUnitary U)
    (hexpand : ∀ s : Finset (Fin n), s.Nonempty → (∃ i, i ∉ s) →
      s.card < (supportColumns U s).card) :
    ¬ Commute (diagonal a) (U * diagonal c * Uᴴ) := by
  intro h
  obtain ⟨μ, hμ⟩ := scalar_of_commute_simple_summands_of_strict_support_expansion hU
    hexpand ha hc (diagonal a) (Commute.refl _) h.symm
  have hval (i : Fin n) : a i = μ := by
    simpa only [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_eq, mul_one] using congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i i) hμ
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro he
    have he' : (0 : ℕ) = 1 := congrArg Fin.val he
    omega
  exact hij (ha ((hval i).trans (hval j).symm))

private theorem commute_of_linear_drury_equation [Nonempty (Fin n)]
    (A C : Matrix (Fin n) (Fin n) ℂ) {κ ω : ℂ} (hκ : κ ≠ star κ) (hω : ω ≠ 0)
    (hinv : IsUnit A.det)
    (h : (ω * star κ + star ω * κ) • (C * A⁻¹) =
      (ω + star ω) • (1 : Matrix (Fin n) (Fin n) ℂ)) : Commute A C := by
  let k := ω * star κ + star ω * κ
  change k • (C * A⁻¹) = (ω + star ω) • (1 : Matrix (Fin n) (Fin n) ℂ) at h
  have hk : k ≠ 0 := by
    intro hk
    let i : Fin n := Classical.choice ‹Nonempty (Fin n)›
    have he : 0 = ω + star ω := by
      simpa only [hk, zero_smul, zero_mul, Matrix.zero_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply_eq, mul_one] using congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i i) h
    have hstar : star ω = -ω := by linear_combination -he
    apply mul_ne_zero hω (sub_ne_zero.mpr (Ne.symm hκ))
    calc
      ω * (star κ - κ) = k := by dsimp only [k]; rw [hstar]; ring
      _ = 0 := hk
  have hscaled := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => k⁻¹ • M) h
  simp only [smul_smul, inv_mul_cancel₀ hk, one_smul] at hscaled
  have hC : C = (k⁻¹ * (ω + star ω)) • A := calc
    C = (C * A⁻¹) * A := by rw [Matrix.mul_assoc, A.nonsing_inv_mul hinv, Matrix.mul_one]
    _ = _ := by rw [hscaled, Matrix.smul_mul, Matrix.one_mul]
  rw [hC]
  exact (Commute.refl A).smul_right _

/-- A nonsingular quadratic support maximum for two simple Hermitian spectra,
one multiplied by `-κ`, satisfies Drury's resolvent equation when the relative
eigenbasis has strict support expansion. A nonreal `κ` and a nonzero support
direction force a nonzero leading coefficient. -/
theorem exists_drury_quadratic_of_simple_support_maximum [Nonempty (Fin n)]
    (hn : 2 ≤ n)
    {a c : Fin n → ℂ} (ha : Function.Injective a) (hc : Function.Injective c)
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : IsUnitary U)
    (hexpand : ∀ s : Finset (Fin n), s.Nonempty → (∃ i, i ∉ s) →
      s.card < (supportColumns U s).card)
    (κ ξ : ℂ) (hκ : κ * star κ = 1) (hκ' : κ ≠ star κ) (hξ : ξ ≠ 0)
    (hA : (diagonal a).IsHermitian) (hC : (diagonal c).IsHermitian)
    (hinv : IsUnit (diagonal a).det) :
    let A := diagonal a
    let C := U * diagonal c * Uᴴ
    let T := A - κ • C
    let ω := ξ * T.det
    let X := C * A⁻¹
    IsUnit T.det →
    (∀ R : Matrix (Fin n) (Fin n) ℂ, IsUnitary R →
      let d := (A - κ • (R * C * Rᴴ)).det - T.det
      (ξ * d).re ≤ -Complex.normSq d / 2) →
    ∃ ell : ℝ, ell ≠ 0 ∧ (ell : ℂ) • (X * X) +
        (ω * star κ + star ω * κ - (ell : ℂ) * (κ + star κ)) • X +
        ((ell : ℂ) - ω - star ω) • (1 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  dsimp only
  let A := diagonal a
  let C := U * diagonal c * Uᴴ
  let T := A - κ • C
  let ω := ξ * T.det
  intro hT hpenalty
  change IsUnit T.det at hT
  have hT' : A + -(κ • C) = T := (sub_eq_add_neg A (κ • C)).symm
  have hmax (R : Matrix (Fin n) (Fin n) ℂ) (hR : IsUnitary R) :
      (ξ * (A + R * (-(κ • C)) * Rᴴ).det).re ≤ (ξ * (A + -(κ • C)).det).re := by
    have h := hpenalty R hR
    change (ξ * ((A - κ • (R * C * Rᴴ)).det - T.det)).re ≤
      -Complex.normSq ((A - κ • (R * C * Rᴴ)).det - T.det) / 2 at h
    rw [mul_sub, Complex.sub_re] at h
    have hle : (ξ * (A - κ • (R * C * Rᴴ)).det).re ≤ (ξ * T.det).re := by
      linarith only [h, Complex.normSq_nonneg ((A - κ • (R * C * Rᴴ)).det - T.det)]
    simpa only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul,
      ← sub_eq_add_neg] using hle
  have hstat := support_maximum_inverse_commutator A (-(κ • C)) ξ
    (show (A + -(κ • C)).det ≠ 0 by rw [hT']; exact isUnit_iff_ne_zero.mp hT) hmax
  dsimp only at hstat
  rw [hT'] at hstat
  have hcomm : -(κ • C) * T⁻¹ - T⁻¹ * (-(κ • C)) = T⁻¹ * A - A * T⁻¹ := by
    rw [show -(κ • C) = T - A by dsimp only [T]; abel]
    rw [Matrix.sub_mul, Matrix.mul_sub, T.mul_nonsing_inv hT, T.nonsing_inv_mul hT]
    abel
  rw [hcomm] at hstat
  obtain ⟨ell, hquad⟩ := exists_drury_quadratic_of_stationarity A C κ ω hκ hA
    (Matrix.isHermitian_mul_mul_conjTranspose U hC) hinv hT hstat
    (scalar_of_commute_simple_resolvent_summands_of_strict_support_expansion hU hexpand ha hc hinv)
  refine ⟨ell, ?_, hquad⟩
  intro hell
  have hω : ω ≠ 0 := mul_ne_zero hξ (isUnit_iff_ne_zero.mp hT)
  apply not_commute_simple_summands_of_strict_support_expansion hn ha hc hU hexpand
  apply commute_of_linear_drury_equation A C hκ' hω hinv
  dsimp only at hquad
  rw [hell, Complex.ofReal_zero, zero_smul, zero_add, zero_mul, sub_zero] at hquad
  apply sub_eq_zero.mp
  rw [sub_eq_add_neg, ← neg_smul, show -(ω + star ω) = 0 - ω - star ω by ring]
  exact hquad

end

end MOC
