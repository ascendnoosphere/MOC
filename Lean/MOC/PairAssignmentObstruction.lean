import MOC.SubsetAssignmentSupport

/-! A symbolic obstruction for the relaxed assignment on unordered pairs.
The local inversion inequality does not concern whether any such relaxation
gap is achieved by a unitary; it is not an MOC counterexample.

A mathematical order-five realization uses positive increasing a with
`a 0 * a 3 > a 1 * a 2` and `a 0 * a 4 > a 2 * a 3`. For example
`a j = t^(3^j)`, t > 1. Then the strictly lower block is the three edges
of the triangle on 0,1,2 and the strictly upper block is the four edges
of the star at 4. Put `b = ζ*a` with ζ the unit phase π/3 and
`η = -i*conj ζ`. The size-one and size-four projected coefficients vanish
since Re(η ζ^k)=sin((k-1)π/3); the size-two and size-three coefficients
are both √3/2. For p(I)=∏ᵢ∈I a i the explicit doubleton coefficient is
`(√3/2)(∏ᵢ a i)(p(I)/p(J) + p(J)/p(I))`. This gives the input to the
strict relaxation obstruction below. The trigonometric specialization is
this explanatory derivation, not a separate checked Lean declaration. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

/-- The symmetric reciprocal-ratio cost arising in the doubleton relaxation. -/
def reciprocalRatioCost (x y : ℝ) : ℝ := x / y + y / x

/-- Swapping two assignments with the same strict input and output order
strictly improves reciprocal-ratio cost. -/
theorem reciprocalRatioCost_swap_strict {a b x y : ℝ}
    (ha : 0 < a) (hx : 0 < x) (hab : a < b) (hxy : x < y) :
    reciprocalRatioCost x a + reciprocalRatioCost y b <
      reciprocalRatioCost y a + reciprocalRatioCost x b := by
  have h₁ : b⁻¹ < a⁻¹ := (inv_lt_inv₀ (ha.trans hab) ha).mpr hab
  have h₂ : y⁻¹ < x⁻¹ := (inv_lt_inv₀ (hx.trans hxy) hx).mpr hxy
  have hp := mul_pos (sub_pos.mpr hxy) (sub_pos.mpr h₁)
  have hq := mul_pos (sub_pos.mpr hab) (sub_pos.mpr h₂)
  simp only [reciprocalRatioCost, div_eq_mul_inv]
  nlinarith only [hp, hq]

/-- Any maximizing assignment for this cost reverses strict ranks. -/
theorem reciprocalRatioAssignment_reverses_ranks {P : Type*} [Fintype P] [DecidableEq P]
    (x : P → ℝ) (hx : ∀ p, 0 < x p) (σ : Equiv.Perm P)
    (hmax : ∀ π : Equiv.Perm P,
      (∑ J, reciprocalRatioCost (x (π J)) (x J)) ≤ ∑ J, reciprocalRatioCost (x (σ J)) (x J))
    {J K : P} (hjk : x J < x K) : ¬ x (σ J) < x (σ K) := by
  classical
  intro hσ
  have hne : J ≠ K := fun h => (lt_irrefl _) (h ▸ hjk)
  let π : Equiv.Perm P := (Equiv.swap J K).trans σ
  let T := ((univ : Finset P).erase J).erase K
  let f (s : Equiv.Perm P) (p : P) := reciprocalRatioCost (x (s p)) (x p)
  have hs (s : Equiv.Perm P) :
      (∑ p, f s p) = (∑ p ∈ T, f s p) + f s K + f s J := by
    rw [Finset.sum_erase_add _ (f s) (by simp [T, hne.symm] : K ∈ (univ : Finset P).erase J),
      Finset.sum_erase_add _ (f s) (Finset.mem_univ J)]
  have hr : (∑ p ∈ T, f π p) = ∑ p ∈ T, f σ p := by
    apply Finset.sum_congr rfl
    intro p hp
    have hp₁ := (Finset.mem_erase.mp ((Finset.mem_erase.mp hp).2)).1
    have hp₂ := (Finset.mem_erase.mp hp).1
    simp [f, π, Equiv.swap_apply_of_ne_of_ne hp₁ hp₂]
  have hstrict := reciprocalRatioCost_swap_strict (hx J) (hx (σ J)) hjk hσ
  have hh := hmax π
  change (∑ p, f π p) ≤ ∑ p, f σ p at hh
  rw [hs π, hs σ, hr] at hh
  simp only [f, π, Equiv.trans_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at hh
  linarith only [hh, hstrict]

/-- A strict rank-reversing optimum sends a bottom block into any larger
top block. The argument uses cardinality, not sorting or enumerating the
permutations. -/
theorem reciprocalRatioAssignment_maps_bottom_into_top
    {P : Type*} [Fintype P] [DecidableEq P] (x : P → ℝ) (hx : ∀ p, 0 < x p)
    (L H : Finset P) (hlh : L.card < H.card)
    (hl : ∀ J ∈ L, ∀ K ∉ L, x J < x K)
    (hh : ∀ J ∉ H, ∀ K ∈ H, x J < x K)
    (σ : Equiv.Perm P)
    (hmax : ∀ π : Equiv.Perm P,
      (∑ J, reciprocalRatioCost (x (π J)) (x J)) ≤ ∑ J, reciprocalRatioCost (x (σ J)) (x J)) :
    ∀ J ∈ L, σ J ∈ H := by
  intro J hJ
  by_contra hσJ
  have he : ∃ K ∈ H, σ.symm K ∉ L := by
    by_contra! hout
    have hs : H.map σ.symm.toEmbedding ⊆ L := by
      intro K hk
      obtain ⟨K', hk', rfl⟩ := Finset.mem_map.mp hk
      exact hout K' hk'
    have hc := Finset.card_le_card hs
    rw [Finset.card_map] at hc
    exact (not_le_of_gt hlh) hc
  obtain ⟨K, hK, hkL⟩ := he
  apply reciprocalRatioAssignment_reverses_ranks x hx σ hmax (hl J hJ (σ.symm K) hkL)
  simpa using hh (σ J) hσJ K hK

/-- A vertex permutation cannot send the three edges of a triangle to
three edges sharing a vertex. This distinguishes a pair permutation from
an induced vertex permutation without enumerating permutations. -/
theorem induced_pairs_cannot_send_triangle_to_star
    {ι : Type*} [DecidableEq ι] (σ : Equiv.Perm ι) {a b c v : ι}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ (v ∈ ({a,b} : Finset ι).map σ.toEmbedding ∧
       v ∈ ({a,c} : Finset ι).map σ.toEmbedding ∧
       v ∈ ({b,c} : Finset ι).map σ.toEmbedding) := by
  intro h
  simp only [Finset.mem_map_equiv, Finset.mem_insert, Finset.mem_singleton] at h
  obtain ⟨h₁, h₂, h₃⟩ := h
  rcases h₁ with h | h
  · exact h₃.elim (fun e => hab (h.symm.trans e)) (fun e => hac (h.symm.trans e))
  · exact h₂.elim (fun e => hab (e.symm.trans h)) (fun e => hbc (h.symm.trans e))

/-- If a strictly bottom block contains the three edges of a triangle and a
larger strictly top block consists of edges incident to one vertex, no
induced permutation attains the unconstrained reciprocal-ratio optimum. -/
theorem induced_pair_assignment_strictly_relaxed_of_triangle_star
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : SubsetLayer ι 2 → ℝ) (hx : ∀ p, 0 < x p)
    (L H : Finset (SubsetLayer ι 2)) (hlh : L.card < H.card)
    (hl : ∀ J ∈ L, ∀ K ∉ L, x J < x K)
    (hh : ∀ J ∉ H, ∀ K ∈ H, x J < x K)
    {a b c v : ι} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (habL : (⟨{a,b}, card_pair hab⟩ : SubsetLayer ι 2) ∈ L)
    (hacL : (⟨{a,c}, card_pair hac⟩ : SubsetLayer ι 2) ∈ L)
    (hbcL : (⟨{b,c}, card_pair hbc⟩ : SubsetLayer ι 2) ∈ L)
    (hstar : ∀ J ∈ H, v ∈ J.val)
    (σ : Equiv.Perm ι) :
    ∃ π : Equiv.Perm (SubsetLayer ι 2),
      (∑ J, reciprocalRatioCost (x (subsetLayerPerm 2 σ J)) (x J)) <
      ∑ J, reciprocalRatioCost (x (π J)) (x J) := by
  by_contra! hmax
  have hmap := reciprocalRatioAssignment_maps_bottom_into_top x hx L H hlh hl hh
    (subsetLayerPerm 2 σ) hmax
  apply induced_pairs_cannot_send_triangle_to_star σ hab hac hbc
  exact ⟨hstar _ (hmap _ habL), hstar _ (hmap _ hacL), hstar _ (hmap _ hbcL)⟩

end

end MOC
