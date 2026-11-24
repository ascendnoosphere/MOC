import MOC.MatchingTriangle
import MOC.MatchingQuartet

/-! Contact sets obstruct positive subset-event certificates. A noncontact
must admit a subset image distinguishing it from every contact. -/

open Finset

namespace MOC

variable {ι : Type*} [DecidableEq ι]

/-- A positive subset-event decomposition must separate each positive gap
from all zero gaps by a single subset image. -/
theorem exists_contact_separating_subset_of_nonnegative_events
    {κ : Type*} [Fintype κ] (g : Equiv.Perm ι → ℝ)
    (I J : κ → Finset ι) (c : κ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (h : ∀ π, g π = ∑ k, if (J k).map π.toEmbedding = I k then c k else 0)
    (σ : Equiv.Perm ι) (hσ : 0 < g σ) :
    ∃ S : Finset ι, ∀ τ, g τ = 0 → S.map τ.toEmbedding ≠ S.map σ.toEmbedding := by
  classical
  have hk : ∃ k : κ, 0 < c k ∧ (J k).map σ.toEmbedding = I k := by
    by_contra! hn
    have hzero : g σ = 0 := by
      rw [h]
      apply sum_eq_zero
      intro k _
      split_ifs with he
      · exact le_antisymm (le_of_not_gt (fun hp => hn k hp he)) (hc k)
      · rfl
    exact hσ.ne' hzero
  obtain ⟨k, hkc, hkI⟩ := hk
  refine ⟨J k, fun τ hτ he => ?_⟩
  have ht := he.trans hkI
  have hb : c k ≤ g τ := by
    rw [h]
    calc
      c k = (if (J k).map τ.toEmbedding = I k then c k else 0) := by rw [if_pos ht]
      _ ≤ _ := single_le_sum (f := fun i => if (J i).map τ.toEmbedding = I i then c i else 0) (fun i _ => by dsimp only; split_ifs; exacts [hc i, le_rfl]) (mem_univ k)
  exact (not_le_of_gt hkc) (hτ ▸ hb)

/-- If every two-coloring has a same-color swap whose gap is zero,
the positive gap at the starting matching has no subset-event certificate.
In particular an odd cycle of contact swaps suffices. -/
theorem not_nonnegative_events_of_contact_swap_cut
    {κ : Type*} [Fintype κ] (g : Equiv.Perm ι → ℝ) (σ : Equiv.Perm ι)
    (hσ : 0 < g σ)
    (hswap : ∀ S : Finset ι, ∃ i j : ι, (i ∈ S ↔ j ∈ S) ∧
      g (σ * Equiv.swap i j) = 0)
    (I J : κ → Finset ι) (c : κ → ℝ) (hc : ∀ k, 0 ≤ c k) :
    ¬ ∀ π, g π = ∑ k, if (J k).map π.toEmbedding = I k then c k else 0 := by
  intro h
  obtain ⟨S, hS⟩ := exists_contact_separating_subset_of_nonnegative_events g I J c hc h σ hσ
  obtain ⟨i, j, hij, hg⟩ := hswap S
  apply hS _ hg
  have e : S.map (Equiv.swap i j).toEmbedding = S := by
    ext x
    rw [Finset.mem_map_equiv, Equiv.symm_swap]
    by_cases hxi : x = i
    · simpa [hxi] using hij.symm
    by_cases hxj : x = j
    · simpa [hxj] using hij
    rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]
  calc
    _ = (S.map (Equiv.swap i j).toEmbedding).map σ.toEmbedding := by rw [map_map]; rfl
    _ = _ := congrArg (fun T => T.map σ.toEmbedding) e

variable [Fintype ι]

/-- A positive-gap matching cannot have a triangle of contact swaps.
The two three-cycles and the base matching balance the three swaps. -/
theorem no_contact_swap_triangle_of_strict_matching_gap
    (a b : ι → ℂ) (η : ℂ) (H : ℝ) (σ : Equiv.Perm ι) (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hmax : ∀ π, (η * matchingProduct a b π).re ≤ H)
    (hσ : (η * matchingProduct a b σ).re < H)
    (h₁ : (η * matchingProduct a b (σ * Equiv.swap i j)).re = H)
    (h₂ : (η * matchingProduct a b (σ * Equiv.swap i k)).re = H)
    (h₃ : (η * matchingProduct a b (σ * Equiv.swap j k)).re = H) : False := by
  have he := congrArg (fun z : ℂ => (η * z).re)
    (matchingProduct_triangle_identity a b σ i j k hij hik hjk)
  simp only [mul_add, Complex.add_re, h₁, h₂, h₃] at he
  linarith only [he, hσ, hmax (σ * Equiv.swap i j * Equiv.swap j k),
    hmax (σ * Equiv.swap j k * Equiv.swap i j)]


/-- For a noncontact below a nonpositive support level, a multiplicative
rectangle with two contact sides has their opposite signed offsets. The
nonzero hypotheses matter at level zero only. -/
theorem opposite_contact_offsets_of_nonpositive_height
    {x y z w : ℂ} {H : ℝ} (hH : H ≤ 0) (hx : x.re < H)
    (hy : y.re = H) (hz : z.re = H) (hw : w.re ≤ H)
    (hxy : x * w = y * z) (hy₀ : y ≠ 0) (hz₀ : z ≠ 0) :
    (x.re * y.im - H * x.im) * (x.re * z.im - H * x.im) < 0 := by
  have hx₀ : x.re < 0 := hx.trans_le hH
  have hR := congrArg Complex.re hxy
  have hI := congrArg Complex.im hxy
  simp only [Complex.mul_re, Complex.mul_im, hy, hz] at hR hI
  have he : (x.re * y.im - H * x.im) * (x.re * z.im - H * x.im) =
      (x.re ^ 2 + x.im ^ 2) * (H ^ 2 - x.re * w.re) := by
    linear_combination (x.re ^ 2) * hR + x.re * x.im * hI
  have hK : 0 < x.re ^ 2 + x.im ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx₀.ne) (sq_nonneg _)
  rw [he]
  by_cases h : H = 0
  · rw [h] at hy hz hw he ⊢
    have hy' : y.im ≠ 0 := fun h => hy₀ (Complex.ext hy h)
    have hz' : z.im ≠ 0 := fun h => hz₀ (Complex.ext hz h)
    have hn : x.re * y.im * (x.re * z.im) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hx₀.ne hy') (mul_ne_zero hx₀.ne hz')
    simp only [zero_mul, sub_zero] at he
    rw [he] at hn
    exact lt_of_le_of_ne
      (mul_nonpos_of_nonneg_of_nonpos hK.le (by
        have hp := mul_nonneg_of_nonpos_of_nonpos hx₀.le hw
        linarith only [hp]))
      hn
  · have hp := mul_le_mul_of_nonpos_left hw hx₀.le
    have hneg := mul_neg_of_neg_of_pos (lt_of_le_of_ne hH h) (sub_pos.mpr hx)
    apply mul_neg_of_pos_of_neg hK
    nlinarith only [hp, hneg]

/-- Apply the rectangle inequality to disjoint contact swaps based at a
noncontact. In contrast to a rectangle based at a contact, the base here
is strictly below the support line. -/
theorem disjoint_contact_swaps_opposite_offsets_of_nonpositive_height
    (a b : ι → ℂ) (η : ℂ) (H : ℝ) (hH : H ≤ 0)
    (σ : Equiv.Perm ι) (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hmax : ∀ π, (η * matchingProduct a b π).re ≤ H)
    (hσ : (η * matchingProduct a b σ).re < H)
    (h₁ : (η * matchingProduct a b (σ * Equiv.swap i j)).re = H)
    (h₂ : (η * matchingProduct a b (σ * Equiv.swap k l)).re = H)
    (hn₁ : matchingProduct a b (σ * Equiv.swap i j) ≠ 0)
    (hn₂ : matchingProduct a b (σ * Equiv.swap k l) ≠ 0) :
    let x := η * matchingProduct a b σ
    let d (π : Equiv.Perm ι) := x.re * (η * matchingProduct a b π).im - H * x.im
    d (σ * Equiv.swap i j) * d (σ * Equiv.swap k l) < 0 := by
  intro x d
  have hη : η ≠ 0 := by
    intro he
    subst η
    simp only [zero_mul, Complex.zero_re] at hσ
    exact (not_lt_of_ge hH) hσ
  apply opposite_contact_offsets_of_nonpositive_height hH hσ h₁ h₂ (hmax (σ * Equiv.swap i j * Equiv.swap k l))
    _ (mul_ne_zero hη hn₁) (mul_ne_zero hη hn₂)
  linear_combination η ^ 2 *
    matchingProduct_disjoint_swaps_identity a b σ i j k l hij hik hil hjk hjl hkl


private theorem center_of_intersecting_triangle_free_edges
    (E : ι → ι → Prop) (anchor : ι)
    (symm : ∀ {i j}, E i j → E j i)
    (triangle : ∀ {i j k}, E i j → E i k → E j k → False)
    (intersects : ∀ {i j k l}, E i j → E k l → i = k ∨ i = l ∨ j = k ∨ j = l) :
    ∃ v : ι, ∀ i j, E i j → i = v ∨ j = v := by
  classical
  by_cases hex : ∃ x y, E x y
  · obtain ⟨x, y, hxy⟩ := hex
    by_cases hx : ∀ i j, E i j → i = x ∨ j = x
    · exact ⟨x, hx⟩
    push_neg at hx
    obtain ⟨i, j, hij, hi, hj⟩ := hx
    obtain ⟨z, hyz, hxz⟩ : ∃ z, E y z ∧ x ≠ z := by
      rcases intersects hxy hij with h | h | h | h
      · exact (hi h.symm).elim
      · exact (hj h.symm).elim
      · exact ⟨j, h ▸ hij, hj.symm⟩
      · exact ⟨i, h ▸ symm hij, hi.symm⟩
    refine ⟨y, fun k l hkl => ?_⟩
    by_contra! he
    have hx' : x = k ∨ x = l := by
      rcases intersects hxy hkl with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (he.1 h.symm).elim
      · exact (he.2 h.symm).elim
    have hz' : z = k ∨ z = l := by
      rcases intersects hyz hkl with h | h | h | h
      · exact (he.1 h.symm).elim
      · exact (he.2 h.symm).elim
      · exact Or.inl h
      · exact Or.inr h
    have he' : E x z := by
      rcases hx' with hx' | hx' <;> rcases hz' with hz' | hz'
      · exact (hxz (hx'.trans hz'.symm)).elim
      · exact hx'.symm ▸ hz'.symm ▸ hkl
      · exact hx'.symm ▸ hz'.symm ▸ symm hkl
      · exact (hxz (hx'.trans hz'.symm)).elim
    exact triangle hxy he' hyz
  · exact ⟨anchor, fun i j h => (hex ⟨i,j,h⟩).elim⟩

private theorem exists_cut_of_triangle_free_two_stars
    (E : ι → ι → Prop) (u v : ι)
    (symm : ∀ {i j}, E i j → E j i)
    (loopless : ∀ i, ¬ E i i)
    (triangle : ∀ {i j k}, E i j → E i k → E j k → False)
    (cover : ∀ {i j}, E i j → (i = u ∨ i = v) ∨ (j = u ∨ j = v)) :
    ∃ S : Finset ι, ∀ i j, E i j → ¬ (i ∈ S ↔ j ∈ S) := by
  classical
  by_cases huv : E u v
  · let S : Finset ι := univ.filter (E v)
    have hv : v ∉ S := by simpa [S] using loopless v
    have hu : u ∈ S := by simpa [S] using symm huv
    have atV (j) (he : E v j) : ¬ (v ∈ S ↔ j ∈ S) :=
      fun h => hv (h.mpr (by simpa [S] using he))
    have atU (j) (he : E u j) : ¬ (u ∈ S ↔ j ∈ S) := by
      intro h
      have hj : E v j := by simpa [S] using h.mp hu
      exact triangle huv he hj
    refine ⟨S, fun i j h => ?_⟩
    rcases cover h with (rfl | rfl) | (rfl | rfl)
    · exact atU _ h
    · exact atV _ h
    · exact fun he => atU _ (symm h) he.symm
    · exact fun he => atV _ (symm h) he.symm
  · refine ⟨{u,v}, fun i j he h => ?_⟩
    have no_centers (x y) (hx : x = u ∨ x = v) (hy : y = u ∨ y = v)
        (he : E x y) : False := by
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact loopless _ he
      · exact huv he
      · exact huv (symm he)
      · exact loopless _ he
    rcases cover he with hx | hy
    · exact no_centers i j hx (by simpa using h.mp (by simpa using hx)) he
    · exact no_centers i j (by simpa using h.mpr (by simpa using hy)) hy he

/-- At nonpositive height, contact swaps around any noncontact form a
bipartite graph. This excludes the odd-cycle obstruction for swaps,
though it does not yet distinguish the noncontact from longer changes. -/
theorem exists_contact_swap_bicoloring_of_nonpositive_height
    (a b : ι → ℂ) (η : ℂ) (H : ℝ) (hH : H ≤ 0) (σ : Equiv.Perm ι)
    (hmax : ∀ π, (η * matchingProduct a b π).re ≤ H)
    (hσ : (η * matchingProduct a b σ).re < H)
    (hnz : ∀ π, matchingProduct a b π ≠ 0) :
    ∃ S : Finset ι, ∀ i j, i ≠ j →
      (η * matchingProduct a b (σ * Equiv.swap i j)).re = H →
      ¬ (i ∈ S ↔ j ∈ S) := by
  classical
  by_cases hg : ∃ i : ι, True
  · obtain ⟨anchor, _⟩ := hg
    let p (π : Equiv.Perm ι) := η * matchingProduct a b π
    let E (i j : ι) := i ≠ j ∧ (p (σ * Equiv.swap i j)).re = H
    let d (i j : ι) := (p σ).re * (p (σ * Equiv.swap i j)).im - H * (p σ).im
    have dcomm (i j) : d i j = d j i := by dsimp [d]; rw [Equiv.swap_comm i j]
    have esymm {i j} (he : E i j) : E j i := by
      refine ⟨he.1.symm, ?_⟩
      simpa only [Equiv.swap_comm j i] using he.2
    have eloop (i) : ¬ E i i := fun h => h.1 rfl
    have etri {i j k} (hij : E i j) (hik : E i k) (hjk : E j k) : False :=
      no_contact_swap_triangle_of_strict_matching_gap a b η H σ i j k hij.1 hik.1 hjk.1
        hmax hσ hij.2 hik.2 hjk.2
    have eop {i j k l} (hij : E i j) (hkl : E k l)
        (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
        d i j * d k l < 0 :=
      disjoint_contact_swaps_opposite_offsets_of_nonpositive_height a b η H hH σ i j k l
        hij.1 hik hil hjk hjl hkl.1 hmax hσ hij.2 hkl.2 (hnz _) (hnz _)
    have centers (q : ℝ → Prop) (hq : ∀ x y, q x → q y → 0 ≤ x * y) :
        ∃ v : ι, ∀ i j, E i j → q (d i j) → i = v ∨ j = v := by
      let E' (i j : ι) := E i j ∧ q (d i j)
      have hs {i j} (h : E' i j) : E' j i := ⟨esymm h.1, dcomm i j ▸ h.2⟩
      obtain ⟨v,hv⟩ := center_of_intersecting_triangle_free_edges E' anchor
        hs (fun x y z => etri x.1 y.1 z.1) (by
          intro i j k l hij hkl
          by_contra! h
          exact (not_lt_of_ge (hq _ _ hij.2 hkl.2))
            (eop hij.1 hkl.1 h.1 h.2.1 h.2.2.1 h.2.2.2))
      exact ⟨v, fun i j h h' => hv i j ⟨h,h'⟩⟩
    obtain ⟨u,hu⟩ := centers (fun x => 0 ≤ x) (fun _ _ => mul_nonneg)
    obtain ⟨v,hv⟩ := centers (fun x => x ≤ 0) (fun _ _ => mul_nonneg_of_nonpos_of_nonpos)
    have cover {i j} (h : E i j) : (i = u ∨ i = v) ∨ (j = u ∨ j = v) := by
      rcases le_total 0 (d i j) with hp | hn
      · rcases hu i j h hp with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
      · rcases hv i j h hn with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)
    obtain ⟨S,hS⟩ := exists_cut_of_triangle_free_two_stars E u v esymm eloop etri cover
    exact ⟨S, fun i j h₁ h₂ => hS i j ⟨h₁,h₂⟩⟩
  · exact ⟨∅, fun i => (hg ⟨i,trivial⟩).elim⟩

end MOC
