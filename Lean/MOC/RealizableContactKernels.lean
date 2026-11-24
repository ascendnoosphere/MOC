import MOC.MatchingProfileClosed

/-! The all-nonzero chart of the additive matching cone, in column-to-row
permutation convention. The support line must be applied to the complex
products, not to arbitrary assignments of real contact gaps. -/

open BigOperators Matrix

namespace MOC
noncomputable section


variable {ι : Type*}

/-- A normalized rank-at-most-one Schur complement, with pivot row and column
equal to one when the two pivot coordinates vanish. -/
def anchoredMatchingKernel (x y : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => 1 + x i * y j

theorem anchoredMatchingKernel_threeMinors (x y : ι → ℂ) :
    VanishingThreeMinors (anchoredMatchingKernel x y) := by
  intro r c
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply, anchoredMatchingKernel, Matrix.of_apply]
  ring

/-- On a nonzero pivot row and column, the normalizing factors and the outer
product are explicit for an additive kernel. -/
theorem additive_eq_gauged_anchored (a b : ι → ℂ) (o : ι)
    (hr : ∀ j, a o + b j ≠ 0) (hc : ∀ i, a i + b o ≠ 0) :
    let x := fun i => (a i - a o) / (a i + b o)
    let y := fun j => (b o - b j) / (a o + b j)
    x o = 0 ∧ y o = 0 ∧
    ∀ i j, a i + b j =
      ((a i + b o) / (a o + b o)) * (a o + b j) * anchoredMatchingKernel x y i j := by
  dsimp only
  refine ⟨by simp, by simp, fun i j => ?_⟩
  unfold anchoredMatchingKernel
  simp only [Matrix.of_apply]
  field_simp [hr j, hc i, hr o]; ring

variable [Fintype ι]

/-- Multiplication by row and column scalars acts by one common profile
scalar. This is a permutation identity, not a finite case split. -/
theorem gauged_kernelMatchingProduct (K : Matrix ι ι ℂ) (L R : ι → ℂ)
    (σ : Equiv.Perm ι) :
    kernelMatchingProduct (Matrix.of fun i j => L i * R j * K i j) σ =
      ((∏ i, L i) * ∏ j, R j) * kernelMatchingProduct K σ := by
  simp only [kernelMatchingProduct, Matrix.of_apply, Finset.prod_mul_distrib, Equiv.prod_comp σ L]

variable [DecidableEq ι]

/-- Any complex entry lies on a matching. Thus a profile with no zero coordinate
comes only from kernels with no zero entries. -/
theorem kernel_nonzero_of_profile_nonzero (K : Matrix ι ι ℂ)
    (h : ∀ σ, kernelMatchingProduct K σ ≠ 0) : ∀ i j, K i j ≠ 0 := by
  intro i j
  have h' := Finset.prod_ne_zero_iff.mp (h (Equiv.swap j i)) j (Finset.mem_univ j)
  simpa only [Equiv.swap_apply_left] using h'

/-- Exact normalized chart: the nonvanishing in the hypothesis concerns matching
products, not gaps. The scalar and outer product suffice, with no spectral
or support assumptions in the reverse direction. -/
theorem nonzero_additive_profile_iff_anchored (o : ι) (p : Equiv.Perm ι → ℂ)
    (hp : ∀ σ, p σ ≠ 0) :
    (∃ a b : ι → ℂ, matchingProduct a b = p) ↔
    ∃ d : ℂ, d ≠ 0 ∧ ∃ x y : ι → ℂ, x o = 0 ∧ y o = 0 ∧
      ∀ σ, p σ = d * kernelMatchingProduct (anchoredMatchingKernel x y) σ := by
  constructor
  · rintro ⟨a, b, rfl⟩
    let A : Matrix ι ι ℂ := Matrix.of fun i j => a i + b j
    have hnr := kernel_nonzero_of_profile_nonzero A hp
    let x := fun i => (a i - a o) / (a i + b o)
    let y := fun j => (b o - b j) / (a o + b j)
    let L := fun i => (a i + b o) / (a o + b o)
    let R := fun j => a o + b j
    obtain ⟨hx, hy, he⟩ := additive_eq_gauged_anchored a b o (hnr o) (fun i => hnr i o)
    refine ⟨(∏ i, L i) * ∏ j, R j, mul_ne_zero ?_ ?_, x, y, hx, hy, fun σ => ?_⟩
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => div_ne_zero (hnr i o) (hnr o o)
    · exact Finset.prod_ne_zero_iff.mpr fun j _ => hnr o j
    · have hA : A = Matrix.of fun i j => L i * R j * anchoredMatchingKernel x y i j := by
        ext i j
        exact he i j
      change kernelMatchingProduct A σ = _
      rw [hA, gauged_kernelMatchingProduct]
  · rintro ⟨d, _, x, y, _, _, h⟩
    let K : Matrix ι ι ℂ := Matrix.of fun i j => (if i = o then d else 1) * (fun _ : ι => (1 : ℂ)) j * anchoredMatchingKernel x y i j
    have hK : VanishingThreeMinors K := by
      intro r c
      simp only [Matrix.det_fin_three, Matrix.submatrix_apply, K, anchoredMatchingKernel, Matrix.of_apply]
      ring
    have hprof : kernelMatchingProduct K = p := by
      funext σ
      change kernelMatchingProduct (Matrix.of fun i j =>
        (if i = o then d else 1) * (fun _ : ι => (1 : ℂ)) j * anchoredMatchingKernel x y i j) σ = _
      rw [gauged_kernelMatchingProduct, h σ]
      simp [Finset.prod_ite_eq']
    have hm : p ∈ {p : Equiv.Perm ι → ℂ | ∃ K : Matrix ι ι ℂ,
        VanishingThreeMinors K ∧ kernelMatchingProduct K = p} := ⟨K, hK, hprof⟩
    rw [← additive_profiles_eq_rankTwo_matching_profiles] at hm
    exact hm

/-- Exact realization of prescribed supporting labels, in the nonzero
profile chart. It uses strict inequalities off the prescribed set so the
contact set is exact. A complex support direction is absorbed in the scalar. -/
theorem realizable_nonzero_contacts_iff_anchored (o : ι)
    (C : Set (Equiv.Perm ι)) (H : ℝ) :
    (∃ a b : ι → ℂ, (∀ σ, matchingProduct a b σ ≠ 0) ∧
      (∀ σ ∈ C, (matchingProduct a b σ).re = H) ∧
      (∀ σ ∉ C, (matchingProduct a b σ).re < H)) ↔
    ∃ d : ℂ, d ≠ 0 ∧ ∃ x y : ι → ℂ, x o = 0 ∧ y o = 0 ∧
      (∀ i j, anchoredMatchingKernel x y i j ≠ 0) ∧
      (∀ σ ∈ C, (d * kernelMatchingProduct (anchoredMatchingKernel x y) σ).re = H) ∧
      (∀ σ ∉ C, (d * kernelMatchingProduct (anchoredMatchingKernel x y) σ).re < H) := by
  constructor
  · rintro ⟨a, b, hp, hc, hs⟩
    obtain ⟨d, hd, x, y, hx, hy, he⟩ :=
      (nonzero_additive_profile_iff_anchored o _ hp).mp ⟨a, b, rfl⟩
    have hn : ∀ σ, kernelMatchingProduct (anchoredMatchingKernel x y) σ ≠ 0 := by
      intro σ hz
      exact hp σ (by rw [he σ, hz, mul_zero])
    exact ⟨d, hd, x, y, hx, hy, kernel_nonzero_of_profile_nonzero _ hn,
      fun σ hσ => by rw [← he σ]; exact hc σ hσ,
      fun σ hσ => by rw [← he σ]; exact hs σ hσ⟩
  · rintro ⟨d, hd, x, y, hx, hy, hn, hc, hs⟩
    let p := fun σ => d * kernelMatchingProduct (anchoredMatchingKernel x y) σ
    have hp (σ : Equiv.Perm ι) : p σ ≠ 0 :=
      mul_ne_zero hd (Finset.prod_ne_zero_iff.mpr fun j _ => hn (σ j) j)
    obtain ⟨a, b, he⟩ := (nonzero_additive_profile_iff_anchored o p hp).mpr
      ⟨d, hd, x, y, hx, hy, fun _ => rfl⟩
    exact ⟨a, b, fun σ => by rw [he]; exact hp σ,
      fun σ hσ => by rw [he]; exact hc σ hσ,
      fun σ hσ => by rw [he]; exact hs σ hσ⟩

/-- With two distinct active products, there are exactly two candidate normal
rays. After fixing one of them, every other contact is a real cross-ratio
equality and every missing contact must have the same strict orientation. -/
theorem strict_contact_set_iff_oriented_edge {α : Type*} (p : α → ℂ) (C : Set α)
    {r s : α} (hr : r ∈ C) (hs : s ∈ C) (hpair : p s ≠ p r) :
    (∃ d : ℂ, d ≠ 0 ∧ ∃ H : ℝ,
      (∀ j ∈ C, (d * p j).re = H) ∧
      (∀ j ∉ C, (d * p j).re < H)) ↔
    (∀ j ∈ C, ((p j - p r) / (p s - p r)).im = 0) ∧
    ((∀ j ∉ C, 0 < ((p j - p r) / (p s - p r)).im) ∨
     (∀ j ∉ C, ((p j - p r) / (p s - p r)).im < 0)) := by
  let Δ := p s - p r
  have hΔ : Δ ≠ 0 := sub_ne_zero.mpr hpair
  have hratio (j : α) : Δ * ((p j - p r) / Δ) = p j - p r := by
    rw [mul_comm, div_mul_cancel₀ _ hΔ]
  have hproj (d : ℂ) (j : α) (hd : (d * Δ).re = 0) :
      (d * p j).re - (d * p r).re =
        -(d * Δ).im * ((p j - p r) / Δ).im := by
    rw [← Complex.sub_re, ← mul_sub]
    calc
      (d * (p j - p r)).re = (d * (Δ * ((p j - p r) / Δ))).re :=
        congrArg (fun z : ℂ => (d * z).re) (hratio j).symm
      _ = _ := by rw [← mul_assoc, Complex.mul_re, hd]; ring
  constructor
  · rintro ⟨d, hd, H, hC, hS⟩
    have he : (d * Δ).re = 0 := by rw [show Δ = p s - p r from rfl, mul_sub,
      Complex.sub_re, hC s hs, hC r hr, sub_self]
    have him : (d * Δ).im ≠ 0 := by
      intro h
      apply mul_ne_zero hd hΔ
      exact Complex.ext (by simpa using he) (by simpa using h)
    refine ⟨fun j hj => ?_, ?_⟩
    · have hz := hproj d j he
      rw [hC j hj, hC r hr, sub_self] at hz
      exact (mul_eq_zero.mp hz.symm).resolve_left (neg_ne_zero.mpr him)
    · obtain hneg | hpos := lt_or_gt_of_ne him
      · right
        intro j hj
        have hval := hproj d j he
        have hlt := hS j hj
        rw [← hC r hr, ← sub_neg, hval] at hlt
        exact neg_of_mul_neg_right hlt (neg_pos.mpr hneg).le
      · left
        intro j hj
        have hval := hproj d j he
        have hlt := hS j hj
        rw [← hC r hr, ← sub_neg, hval] at hlt
        exact pos_of_mul_neg_right hlt (neg_neg_of_pos hpos).le
  · rintro ⟨hC, hS | hS⟩
    · let d := Complex.I / Δ
      have hdΔ : d * Δ = Complex.I := div_mul_cancel₀ _ hΔ
      have he : (d * Δ).re = 0 := by rw [hdΔ, Complex.I_re]
      refine ⟨d, div_ne_zero Complex.I_ne_zero hΔ, (d * p r).re, ?_, ?_⟩
      · intro j hj
        have hv := hproj d j he
        rw [hdΔ, hC j hj, mul_zero] at hv
        exact sub_eq_zero.mp hv
      · intro j hj
        have hv := hproj d j he
        rw [hdΔ, Complex.I_im, neg_one_mul] at hv
        exact sub_neg.mp (hv ▸ neg_neg_of_pos (hS j hj))
    · let d := -Complex.I / Δ
      have hdΔ : d * Δ = -Complex.I := div_mul_cancel₀ _ hΔ
      have he : (d * Δ).re = 0 := by rw [hdΔ, Complex.neg_re, Complex.I_re, neg_zero]
      refine ⟨d, div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hΔ, (d * p r).re, ?_, ?_⟩
      · intro j hj
        have hv := hproj d j he
        rw [hdΔ, hC j hj, mul_zero] at hv
        exact sub_eq_zero.mp hv
      · intro j hj
        have hv := hproj d j he
        rw [hdΔ, Complex.neg_im, Complex.I_im, neg_neg, one_mul] at hv
        exact sub_neg.mp (hv ▸ hS j hj)

/-- The pivot chart when the pivot row or column may have zeros. The residual
is still rank at most one, but the leading pivot column and row cannot in
general be gauged to constant vectors. -/
def generalPivotMatchingKernel (u v x y : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => u i * v j + x i * y j

/-- Exact normalized rank-one residual description, including profiles with
some zero coordinates. If the entire profile vanishes, no pivot is needed. -/
theorem additive_profile_iff_general_pivot (o : ι) (p : Equiv.Perm ι → ℂ) :
    (∃ a b : ι → ℂ, matchingProduct a b = p) ↔
    p = 0 ∨ ∃ (q : ι) (d : ℂ), d ≠ 0 ∧ ∃ u v x y : ι → ℂ,
      u o = 1 ∧ v q = 1 ∧ x o = 0 ∧ y q = 0 ∧
      ∀ σ, p σ = d * kernelMatchingProduct (generalPivotMatchingKernel u v x y) σ := by
  constructor
  · rintro ⟨a, b, rfl⟩
    by_cases hzero : matchingProduct a b = 0
    · exact Or.inl hzero
    · right
      obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm ι, matchingProduct a b σ ≠ 0 := by
        contrapose! hzero
        exact funext hzero
      let q := σ.symm o
      let m := a o + b q
      have hn : m ≠ 0 := by
        have ht := Finset.prod_ne_zero_iff.mp hσ q (Finset.mem_univ q)
        simpa only [q, Equiv.apply_symm_apply] using ht
      let u i := (a i + b q) / m
      let v j := (a o + b j) / m
      let x i := (a i - a o) / m
      let y j := (b q - b j) / m
      refine ⟨q, m ^ Fintype.card ι, pow_ne_zero _ hn, u, v, x, y, ?_, ?_, ?_, ?_, fun τ => ?_⟩
      · exact div_self hn
      · exact div_self hn
      · simp [x]
      · simp [y]
      · have h (i j : ι) : a i + b j = m * generalPivotMatchingKernel u v x y i j := by
          simp only [generalPivotMatchingKernel, Matrix.of_apply, u, v, x, y]
          field_simp [m, hn]; ring
        simp only [matchingProduct, kernelMatchingProduct, h, Finset.prod_mul_distrib,
          Finset.prod_const, Finset.card_univ]
  · rintro (rfl | ⟨q, d, _, u, v, x, y, _, _, _, _, hprof⟩)
    · refine ⟨0, 0, funext fun σ => ?_⟩
      exact Finset.prod_eq_zero (Finset.mem_univ o) (by simp)
    · let K : Matrix ι ι ℂ := Matrix.of fun i j =>
        (if i = o then d else 1) * (fun _ : ι => (1 : ℂ)) j * generalPivotMatchingKernel u v x y i j
      have hK : VanishingThreeMinors K := by
        intro r c
        simp only [Matrix.det_fin_three, Matrix.submatrix_apply, K, generalPivotMatchingKernel,
          Matrix.of_apply, mul_one]
        ring
      have hp : kernelMatchingProduct K = p := by
        funext σ
        change kernelMatchingProduct (Matrix.of fun i j =>
          (if i = o then d else 1) * (fun _ : ι => (1 : ℂ)) j * generalPivotMatchingKernel u v x y i j) σ = _
        rw [gauged_kernelMatchingProduct, hprof σ]
        simp [Finset.prod_ite_eq']
      have hm : p ∈ {p : Equiv.Perm ι → ℂ | ∃ K : Matrix ι ι ℂ,
          VanishingThreeMinors K ∧ kernelMatchingProduct K = p} := ⟨K, hK, hp⟩
      rw [← additive_profiles_eq_rankTwo_matching_profiles] at hm
      exact hm

/-- Recover one chart entry as the ratio of two profiles differing by a pivot
swap. The completion is arbitrary and no choice of matching weights is used. -/
theorem anchored_entry_eq_profile_ratio (x y : ι → ℂ) (o j : ι) (hjo : j ≠ o)
    (hx : x o = 0) (hy : y o = 0) (σ : Equiv.Perm ι) (hσ : σ o = o)
    (d : ℂ) (hn : d * kernelMatchingProduct (anchoredMatchingKernel x y)
      (σ * Equiv.swap o j) ≠ 0) :
    anchoredMatchingKernel x y (σ j) j =
      (d * kernelMatchingProduct (anchoredMatchingKernel x y) σ) /
      (d * kernelMatchingProduct (anchoredMatchingKernel x y) (σ * Equiv.swap o j)) := by
  let K := anchoredMatchingKernel x y
  have hrow (k : ι) : K o k = 1 := by simp [K, anchoredMatchingKernel, hx]
  have hcol (k : ι) : K k o = 1 := by simp [K, anchoredMatchingKernel, hy]
  let S : Finset ι := Finset.univ.erase o
  have hj : j ∈ S := Finset.mem_erase.mpr ⟨hjo, Finset.mem_univ j⟩
  have hsplit (τ : Equiv.Perm ι) : kernelMatchingProduct K τ =
      K (τ o) o * (K (τ j) j * ∏ k ∈ S.erase j, K (τ k) k) := by
    unfold kernelMatchingProduct
    rw [← Finset.mul_prod_erase Finset.univ (fun k => K (τ k) k) (Finset.mem_univ o),
      ← Finset.mul_prod_erase S (fun k => K (τ k) k) hj]
  have he : (∏ k ∈ S.erase j, K ((σ * Equiv.swap o j) k) k) =
      ∏ k ∈ S.erase j, K (σ k) k := by
    apply Finset.prod_congr rfl
    intro k hk
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    have hko : k ≠ o := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hko hkj]
  change K (σ j) j = (d * kernelMatchingProduct K σ) /
    (d * kernelMatchingProduct K (σ * Equiv.swap o j))
  apply (eq_div_iff hn).mpr
  rw [hsplit σ, hsplit (σ * Equiv.swap o j), hcol, hcol, Equiv.Perm.mul_apply,
    Equiv.swap_apply_right, hσ, hrow, he, one_mul, one_mul, one_mul]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- Vanishing of every crossed residual 2×2 minor. Combined with entry recovery,
these give compatibility equations across unrelated pairs of contacts. -/
theorem anchored_residual_cross (x y : ι → ℂ) (i i' j j' : ι) :
    (anchoredMatchingKernel x y i j - 1) * (anchoredMatchingKernel x y i' j' - 1) =
      (anchoredMatchingKernel x y i j' - 1) * (anchoredMatchingKernel x y i' j - 1) := by
  simp only [anchoredMatchingKernel, Matrix.of_apply]
  ring

/-- A fixed matching completion recovers each nonpivot entry from two values
of the prescribed profile. -/
def recoveredAnchoredKernel (o : ι) (p : Equiv.Perm ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j =>
    if i = o ∨ j = o then 1
    else p (Equiv.swap j i) / p (Equiv.swap j i * Equiv.swap o j)

/-- Algebraic test directly on the proposed complex profile. Every 2×2 minor
of the recovered residual must vanish, and the recovered products must
agree with the proposed products up to the single pivot-matching scalar. -/
theorem nonzero_additive_profile_iff_recovered (o : ι) (p : Equiv.Perm ι → ℂ)
    (hp : ∀ σ, p σ ≠ 0) :
    (∃ a b : ι → ℂ, matchingProduct a b = p) ↔
    let K := recoveredAnchoredKernel o p
    (∀ i i' j j', (K i j - 1) * (K i' j' - 1) = (K i j' - 1) * (K i' j - 1)) ∧
    (∀ σ, p σ * kernelMatchingProduct K 1 = p 1 * kernelMatchingProduct K σ) := by
  let K := recoveredAnchoredKernel o p
  have hr (j : ι) : K o j = 1 := by simp [K, recoveredAnchoredKernel]
  have hc (i : ι) : K i o = 1 := by simp [K, recoveredAnchoredKernel]
  change _ ↔ (∀ i i' j j', (K i j - 1) * (K i' j' - 1) = (K i j' - 1) * (K i' j - 1)) ∧
    (∀ σ, p σ * kernelMatchingProduct K 1 = p 1 * kernelMatchingProduct K σ)
  constructor
  · intro h
    obtain ⟨d, _, x, y, hx, hy, hprof⟩ :=
      (nonzero_additive_profile_iff_anchored o p hp).mp h
    have he : K = anchoredMatchingKernel x y := by
      ext i j
      by_cases hio : i = o
      · subst i
        simp [K, recoveredAnchoredKernel, anchoredMatchingKernel, hx]
      · by_cases hjo : j = o
        · subst j
          simp [K, recoveredAnchoredKernel, anchoredMatchingKernel, hy]
        · let σ : Equiv.Perm ι := Equiv.swap j i
          have hi : σ j = i := Equiv.swap_apply_left j i
          have ho : σ o = o := Equiv.swap_apply_of_ne_of_ne (Ne.symm hjo) (Ne.symm hio)
          have hn : d * kernelMatchingProduct (anchoredMatchingKernel x y)
              (σ * Equiv.swap o j) ≠ 0 := by rw [← hprof]; exact hp _
          have hratio := anchored_entry_eq_profile_ratio x y o j hjo hx hy σ ho d hn
          rw [hi, ← hprof, ← hprof] at hratio
          simpa [K, recoveredAnchoredKernel, hio, hjo, σ] using hratio.symm
    rw [he]
    refine ⟨anchored_residual_cross x y, fun σ => ?_⟩
    rw [hprof σ, hprof 1]
    ring
  · rintro ⟨hminor, hprof⟩
    let E (i j : ι) := K i j - 1
    have hres (i i' j j' : ι) : E i j * E i' j' = E i j' * E i' j := hminor i i' j j'
    obtain ⟨x, y, hxy⟩ : ∃ x y : ι → ℂ, ∀ i j, E i j = x i * y j := by
      by_cases he : ∃ i j, E i j ≠ 0
      · obtain ⟨r, s, hrs⟩ := he
        refine ⟨fun i => E i s, fun j => E r j / E r s, fun i j => ?_⟩
        rw [← mul_div_assoc]
        exact (eq_div_iff hrs).mpr (hres i r j s)
      · refine ⟨0, 0, fun i j => ?_⟩
        simpa only [Pi.zero_apply, zero_mul] using
          (show E i j = 0 from not_ne_iff.mp fun h => he ⟨i, j, h⟩)
    have hk : K = anchoredMatchingKernel x y := by
      ext i j
      have h := hxy i j
      simp only [E, anchoredMatchingKernel, Matrix.of_apply] at h ⊢
      linear_combination h
    have hnorm (i j : ι) : K i j ≠ 0 := by
      by_cases h : i = o ∨ j = o
      · rcases h with rfl | rfl
        · rw [hr]; exact one_ne_zero
        · rw [hc]; exact one_ne_zero
      · simpa only [K, recoveredAnchoredKernel, Matrix.of_apply, if_neg h] using
          div_ne_zero (hp (Equiv.swap j i)) (hp (Equiv.swap j i * Equiv.swap o j))
    have hn : kernelMatchingProduct K 1 ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => hnorm _ _
    let d := p 1 / kernelMatchingProduct K 1
    have hd : d ≠ 0 := div_ne_zero (hp 1) hn
    have hscaled (σ : Equiv.Perm ι) :
        p σ = d * kernelMatchingProduct K σ := by
      dsimp only [d]
      rw [div_mul_eq_mul_div]
      exact (eq_div_iff hn).mpr (hprof σ)
    refine (additive_profile_iff_general_pivot o p).mpr (Or.inr
      ⟨o, d, hd, 1, 1, Function.update x o 0, Function.update y o 0,
        rfl, rfl, Function.update_self .., Function.update_self .., ?_⟩)
    have hK : K = generalPivotMatchingKernel 1 1 (Function.update x o 0) (Function.update y o 0) := by
      ext i j
      by_cases hi : i = o
      · subst i
        simp [hr, generalPivotMatchingKernel]
      · by_cases hj : j = o
        · subst j
          simp [hc, generalPivotMatchingKernel]
        · rw [hk]
          simp [anchoredMatchingKernel, generalPivotMatchingKernel, Function.update_of_ne hi,
            Function.update_of_ne hj]
    intro σ
    exact hK ▸ hscaled σ

end
end MOC
