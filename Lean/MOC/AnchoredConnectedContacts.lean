import MOC.ContactFibreGluing
import MOC.MatchingQuartet
import MOC.MatchingTriangle

/-! At height zero, anchored cycle contacts propagate the reality of
the gauged kernel along any spanning graph. The argument needs distinct
anchor values, not global simplicity. -/

open BigOperators Matrix

namespace MOC
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The forward anchored cycle retains just one off-diagonal factor in
the anchored kernel; the other two factors meet its unit row or column. -/
theorem anchored_kernel_cycle_product (x y : ι → ℂ) (o i j : ι)
    (hoi : o ≠ i) (hoj : o ≠ j) (hij : i ≠ j) (hx : x o = 0) (hy : y o = 0) :
    let K := anchoredMatchingKernel x y
    kernelMatchingProduct K (Equiv.swap o i * Equiv.swap i j) =
      (∏ s ∈ ({o,i,j} : Finset ι)ᶜ, K s s) * K j i := by
  intro K
  let S : Finset ι := {o,i,j}
  let σ := Equiv.swap o i * Equiv.swap i j
  let f (s : ι) := K (σ s) s
  have hp : (∏ s ∈ Sᶜ, f s) = ∏ s ∈ Sᶜ, K s s := by
    apply Finset.prod_congr rfl
    intro s hs
    have h : s ≠ o ∧ s ≠ i ∧ s ≠ j := by
      simpa [S, not_or] using Finset.mem_compl.mp hs
    simp [f, σ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h.1 h.2.1,
      Equiv.swap_apply_of_ne_of_ne h.2.1 h.2.2]
  have hσo : σ o = i := by simp [σ, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hoi hoj]
  have hσi : σ i = j := by simp [σ, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hoj.symm hij.symm]
  have hσj : σ j = o := by simp [σ, Equiv.Perm.mul_apply]
  have hs : (∏ s ∈ S, f s) = K j i := by
    change (∏ s ∈ ({o,i,j} : Finset ι), f s) = _
    rw [Finset.prod_insert (show o ∉ ({i,j} : Finset ι) by simp [hoi,hoj]),
      Finset.prod_insert (show i ∉ ({j} : Finset ι) by simp [hij]), Finset.prod_singleton]
    simp [f, hσo, hσi, hσj, K, anchoredMatchingKernel, hx, hy]
  change (∏ s, f s) = _
  rw [← Finset.prod_compl_mul_prod S f, hp, hs]

omit [Fintype ι] [DecidableEq ι] in
private theorem real_product_of_real_entries {f : ι → ℂ} (s : Finset ι)
    (hf : ∀ i ∈ s, (f i).im = 0) : (∏ i ∈ s, f i).im = 0 := by
  have h : (∏ i ∈ s, f i) = ((∏ i ∈ s, (f i).re : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro i hi
    exact Complex.ext (by simp) (by simp [hf i hi])
  rw [h, Complex.ofReal_im]

omit [Fintype ι] in
private theorem rankOne_real_diag_propagates (x y : ι → ℂ) (o : ι)
    (hx : x o = 0) (hy : y o = 0)
    (hdiag : ∀ j, (x j * y j).im = 0)
    (hnz : ∀ j, j ≠ o → x j * y j ≠ 0)
    (R : {j : ι // j ≠ o} → {j : ι // j ≠ o} → Prop)
    (hedge : ∀ i j, R i j → (x j * y i).im = 0)
    (hconn : ∀ i j, Relation.ReflTransGen R i j) :
    ∀ i j, (x j * y i).im = 0 := by
  have htrans (i j k : {j : ι // j ≠ o})
      (h₁ : (x j * y i).im = 0) (h₂ : (x k * y j).im = 0) :
      (x k * y i).im = 0 := by
    have h : (x k * y i) * (x j * y j) = (x j * y i) * (x k * y j) := by ring
    have hi := congrArg Complex.im h
    change ((x k * y i) * (x j * y j)).im = ((x j * y i) * (x k * y j)).im at hi
    simp only [Complex.mul_im (x k * y i) (x j * y j),
      Complex.mul_im (x j * y i) (x k * y j), hdiag j, h₁, h₂, mul_zero, zero_mul, zero_add, add_zero] at hi
    have hj : (x j * y j).re ≠ 0 :=
      fun he => hnz j j.property (Complex.ext (by simpa using he) (by simpa using hdiag j))
    exact (mul_eq_zero.mp hi).resolve_right hj
  have hpath (i j : {j : ι // j ≠ o}) (h : Relation.ReflTransGen R i j) :
      (x j * y i).im = 0 := by
    induction h with
    | refl => exact hdiag i
    | tail _ hEdge ih => exact htrans _ _ _ ih (hedge _ _ hEdge)
  intro i j
  by_cases hi : i = o
  · simp [hi, hy]
  by_cases hj : j = o
  · simp [hj, hx]
  exact hpath ⟨i,hi⟩ ⟨j,hj⟩ (hconn _ _)

/-- All anchor swaps and one oriented three-cycle for each edge of a
connected graph on the nonanchor labels force collinearity at height
zero. A connected graph need not be a star, and values may repeat away
from the anchor in either spectrum. Products other than the pivot and
anchor swaps may vanish. -/
theorem matching_line_of_zero_height_anchored_connected
    (a b : ι → ℂ) (η : ℂ) (hη : η ≠ 0) (o : ι)
    (ha : ∀ j, j ≠ o → a j ≠ a o) (hb : ∀ j, j ≠ o → b j ≠ b o)
    (hbaseNZ : matchingProduct a b 1 ≠ 0)
    (hswapNZ : ∀ j, j ≠ o → matchingProduct a b (Equiv.swap o j) ≠ 0)
    (hp : (η * matchingProduct a b 1).re = 0)
    (hs : ∀ j, j ≠ o → (η * matchingProduct a b (Equiv.swap o j)).re = 0)
    (R : {j : ι // j ≠ o} → {j : ι // j ≠ o} → Prop)
    (hedge : ∀ i j, R i j → i ≠ j ∧
      ((η * matchingProduct a b (Equiv.swap o (i : ι) * Equiv.swap (i : ι) (j : ι))).re = 0 ∨
        (η * matchingProduct a b (Equiv.swap o (j : ι) * Equiv.swap (j : ι) (i : ι))).re = 0))
    (hconn : ∀ i j, Relation.ReflTransGen R i j) :
    ∀ σ, (η * matchingProduct a b σ).re = 0 := by
  let A : Matrix ι ι ℂ := Matrix.of fun r s => a r + b s
  have hf (σ : Equiv.Perm ι) (hn : matchingProduct a b σ ≠ 0) (j : ι) :
      a (σ j) + b j ≠ 0 := Finset.prod_ne_zero_iff.mp hn j (Finset.mem_univ _)
  have hrow (j : ι) : a j + b o ≠ 0 := by
    by_cases h : j = o
    · simpa [h] using hf 1 hbaseNZ o
    · simpa only [Equiv.swap_apply_left] using hf (Equiv.swap o j) (hswapNZ j h) o
  have hcol (j : ι) : a o + b j ≠ 0 := by
    by_cases h : j = o
    · simpa [h] using hf 1 hbaseNZ o
    · simpa only [Equiv.swap_apply_right] using hf (Equiv.swap o j) (hswapNZ j h) j
  let x (r : ι) := (a r - a o) / (a r + b o)
  let y (s : ι) := (b o - b s) / (a o + b s)
  let K := anchoredMatchingKernel x y
  let L (r : ι) := (a r + b o) / (a o + b o)
  let T (s : ι) := a o + b s
  let d : ℂ := η * ((∏ r, L r) * ∏ s, T s)
  obtain ⟨hx, hy, hA⟩ := additive_eq_gauged_anchored a b o hcol hrow
  have hscale (σ : Equiv.Perm ι) : η * matchingProduct a b σ = d * kernelMatchingProduct K σ := by
    have he : A = Matrix.of fun r s => L r * T s * K r s := by
      ext r s
      exact hA r s
    change η * kernelMatchingProduct A σ = _
    rw [he, gauged_kernelMatchingProduct]
    exact (mul_assoc η _ _).symm
  change x o = 0 at hx
  change y o = 0 at hy
  have hKnz (σ : Equiv.Perm ι) (hn : matchingProduct a b σ ≠ 0) :
      d * kernelMatchingProduct K σ ≠ 0 := by
    rw [← hscale]
    exact mul_ne_zero hη hn
  have hKone := hKnz 1 hbaseNZ
  have hdiag (i : ι) : (K i i).im = 0 := by
    by_cases hi : i = o
    · simp [K, hi, anchoredMatchingKernel, hx]
    have he := anchored_entry_eq_profile_ratio x y o i hi hx hy 1 rfl d (hKnz _ (by simpa only [one_mul] using hswapNZ i hi))
    change K i i = _ at he
    rw [he, ← hscale 1, ← hscale (1 * Equiv.swap o i)]
    simp only [Complex.div_im, hp, one_mul, hs i hi, mul_zero, zero_mul, sub_self, zero_div]
  have hres (i j : ι) : (K i j).im = (x i * y j).im := by simp [K, anchoredMatchingKernel]
  have hD (i j : ι) :
      let C := ∏ s ∈ ({o,i,j} : Finset ι)ᶜ, K s s
      (d * C).re = 0 ∧ (d * C).im ≠ 0 := by
    intro C
    have hc : C.im = 0 := real_product_of_real_entries _ (fun i _ => hdiag i)
    have hk : (kernelMatchingProduct K 1).im = 0 :=
      real_product_of_real_entries _ (fun i _ => hdiag i)
    have hm : (kernelMatchingProduct K 1).re ≠ 0 := fun h =>
      hKone (by
        have hz : kernelMatchingProduct K 1 = 0 :=
          Complex.ext (by simpa using h) (by simpa using hk)
        rw [hz, mul_zero])
    have hdr : d.re = 0 := by
      rw [hscale, Complex.mul_re, hk, mul_zero, sub_zero] at hp
      exact (mul_eq_zero.mp hp).resolve_right hm
    have hdn : d ≠ 0 := fun h => hKone (by simp [h])
    have hkn (s : ι) : K s s ≠ 0 := by
      have hh := right_ne_zero_of_mul hKone
      exact (Finset.prod_ne_zero_iff.mp hh) s (Finset.mem_univ _)
    have hcn : C ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hkn i)
    have hreal : (d * C).re = 0 := by simp [Complex.mul_re, hc, hdr]
    exact ⟨hreal, fun h => (mul_ne_zero hdn hcn) (Complex.ext hreal h)⟩
  have hdiagres (i : ι) : (x i * y i).im = 0 := by rw [← hres]; exact hdiag i
  have hnres (i : ι) (hi : i ≠ o) : x i * y i ≠ 0 :=
    mul_ne_zero (div_ne_zero (sub_ne_zero.mpr (ha i hi)) (hrow i))
      (div_ne_zero (sub_ne_zero.mpr (hb i hi).symm) (hcol i))
  have hforward (i j : {j : ι // j ≠ o}) (hne : i ≠ j)
      (hc : (η * matchingProduct a b (Equiv.swap o (i : ι) * Equiv.swap (i : ι) (j : ι))).re = 0) :
      (x j * y i).im = 0 := by
    have hij : (i : ι) ≠ j := fun he => hne (Subtype.ext he)
    have h := anchored_kernel_cycle_product x y o i j i.property.symm j.property.symm hij hx hy
    have hd := hD i j
    change kernelMatchingProduct K _ = _ at h
    rw [hscale, h, ← mul_assoc, Complex.mul_re, hd.1, zero_mul, zero_sub, neg_eq_zero] at hc
    rw [← hres]
    exact (mul_eq_zero.mp hc).resolve_left hd.2
  have he (i j) (h : R i j) : (x j * y i).im = 0 := by
    obtain ⟨hne,hleft | hright⟩ := hedge i j h
    · exact hforward i j hne hleft
    · have hz := hforward j i hne.symm hright
      have h := congrArg Complex.im
        (show (x j * y i) * (x i * y j) = (x i * y i) * (x j * y j) by ring)
      change ((x j * y i) * (x i * y j)).im = ((x i * y i) * (x j * y j)).im at h
      simp only [Complex.mul_im (x j * y i) (x i * y j),
        Complex.mul_im (x i * y i) (x j * y j), hz, hdiagres, mul_zero, zero_mul, zero_add, add_zero] at h
      have hnz : x i * y j ≠ 0 :=
        mul_ne_zero (left_ne_zero_of_mul (hnres i i.property)) (right_ne_zero_of_mul (hnres j j.property))
      exact (mul_eq_zero.mp h).resolve_right
        (fun he => hnz (Complex.ext (by simpa using he) (by simpa using hz)))
  have hK (i j) : (K i j).im = 0 := by
    rw [hres]
    exact rankOne_real_diag_propagates x y o hx hy hdiagres hnres R he hconn j i
  have hP (σ : Equiv.Perm ι) : (kernelMatchingProduct K σ).im = 0 :=
    real_product_of_real_entries _ (fun i _ => hK (σ i) i)
  have hbase : (kernelMatchingProduct K 1).re ≠ 0 :=
    fun he => hKone (by
      have hzero : kernelMatchingProduct K 1 = 0 :=
        Complex.ext (by simpa using he) (by simpa using hP 1)
      rw [hzero, mul_zero])
  have hdr : d.re = 0 := by
    rw [hscale, Complex.mul_re, hP, mul_zero, sub_zero] at hp
    exact (mul_eq_zero.mp hp).resolve_right hbase
  intro σ
  rw [hscale, Complex.mul_re, hdr, hP, zero_mul, mul_zero, sub_self]

/-- A nondegenerate contact rectangle fixes the height at zero. On a
connected graph each edge can be certified by either oriented cycle,
or by its nonanchor transposition when the common height is supporting. -/
theorem holds_of_anchored_connected_with_rectangle
    (a b : ι → ℂ) (η : ℂ) (hη : η ≠ 0) (H : ℝ) (r : Equiv.Perm ι) (o : ι)
    (ha : ∀ j, j ≠ o → a (r j) ≠ a (r o)) (hb : ∀ j, j ≠ o → b j ≠ b o)
    (hn : ∀ σ, matchingProduct a b σ ≠ 0)
    (hp : (η * matchingProduct a b r).re = H)
    (hs : ∀ j, j ≠ o → (η * matchingProduct a b (r * Equiv.swap o j)).re = H)
    (hmax : ∀ σ, (η * matchingProduct a b σ).re ≤ H)
    (R : {j : ι // j ≠ o} → {j : ι // j ≠ o} → Prop)
    (hedge : ∀ i j, R i j → i ≠ j ∧
      ((η * matchingProduct a b (r * (Equiv.swap o (i : ι) * Equiv.swap (i : ι) (j : ι)))).re = H ∨
       (η * matchingProduct a b (r * (Equiv.swap o (j : ι) * Equiv.swap (j : ι) (i : ι)))).re = H ∨
       (η * matchingProduct a b (r * Equiv.swap (i : ι) (j : ι))).re = H))
    (hconn : ∀ i j, Relation.ReflTransGen R i j)
    (p q s t : ι) (σ : Equiv.Perm ι)
    (hpq : p ≠ q) (hps : p ≠ s) (hpt : p ≠ t) (hqs : q ≠ s) (hqt : q ≠ t) (hst : s ≠ t)
    (hapq : a (σ p) ≠ a (σ q)) (hast : a (σ s) ≠ a (σ t))
    (hbpq : b p ≠ b q) (hbst : b s ≠ b t)
    (h₀₀ : (η * matchingProduct a b σ).re = H)
    (h₀₁ : (η * matchingProduct a b (σ * Equiv.swap p q)).re = H)
    (h₁₀ : (η * matchingProduct a b (σ * Equiv.swap s t)).re = H)
    (h₁₁ : (η * matchingProduct a b (σ * Equiv.swap p q * Equiv.swap s t)).re = H)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) : Holds a b U := by
  let A : Matrix ι ι ℂ := Matrix.of fun l m => a l + b m
  have hentry : ∀ l m, a l + b m ≠ 0 := kernel_nonzero_of_profile_nonzero A hn
  have hz := matchingProduct_disjoint_swaps_common_height_eq_zero_of_unequal_pairs
    a b σ p q s t hpq hps hpt hqs hqt hst hapq hast hbpq hbst hentry hη h₀₀ h₀₁ h₁₀ h₁₁
  rw [hz] at hp hs hmax hedge
  let a' := a ∘ r
  have hprof (τ : Equiv.Perm ι) : matchingProduct a' b τ = matchingProduct a b (r * τ) := rfl
  have hhconn (i j : {j : ι // j ≠ o}) (he : R i j) :
      i ≠ j ∧
      ((η * matchingProduct a' b (Equiv.swap o (i : ι) * Equiv.swap (i : ι) (j : ι))).re = 0 ∨
       (η * matchingProduct a' b (Equiv.swap o (j : ι) * Equiv.swap (j : ι) (i : ι))).re = 0) := by
    obtain ⟨hij,h₁ | h₂ | h₃⟩ := hedge i j he
    · exact ⟨hij,Or.inl (by rwa [hprof])⟩
    · exact ⟨hij,Or.inr (by rwa [hprof])⟩
    · refine ⟨hij,Or.inl ?_⟩
      have hne : (i : ι) ≠ (j : ι) := fun h => hij (Subtype.ext h)
      have h := congrArg (fun z : ℂ => (η * z).re)
        (matchingProduct_triangle_identity a b r o i j i.property.symm j.property.symm hne)
      simp only [mul_add, Complex.add_re, hp, hs _ i.property, hs _ j.property, h₃,
        zero_add, add_zero] at h
      rw [hprof, ← mul_assoc]
      have hrev := hmax (r * Equiv.swap (i : ι) (j : ι) * Equiv.swap o (i : ι))
      have hfwd := hmax (r * Equiv.swap o (i : ι) * Equiv.swap (i : ι) (j : ι))
      linarith only [h,hrev,hfwd]
  have hline := matching_line_of_zero_height_anchored_connected a' b η hη o ha hb
    (by rw [hprof]; exact hn _) (fun j _ => by rw [hprof]; exact hn _) (by rwa [hprof, mul_one])
    (fun j hj => by rw [hprof]; exact hs j hj) R hhconn hconn
  letI : Nonempty ι := ⟨o⟩
  apply holds_of_matching_line_through_origin a b η hη _ U hU
  intro τ
  simpa only [hprof, ← mul_assoc, mul_inv_cancel, one_mul] using hline (r⁻¹ * τ)

end
end MOC
