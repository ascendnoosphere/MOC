import MOC.AdjacentMinorSupport
import MOC.ContactWeightPositivity

/-! Positive laws for projected objectives that split additively across
compatible nested subset-image statistics. A general nonlinear function
of a pair of image sets is not asserted to have the same expectation. -/

open BigOperators Finset Matrix

namespace MOC
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem projected_image_expectation (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (J : Finset ι) (f : Finset ι → ℝ) :
    (∑ I, subsetMinorSq U I J * f I) =
      ∑ σ : Equiv.Perm ι, realSignedWeight U σ * f (J.map σ.toEmbedding) := by
  classical
  rw [← Finset.sum_fiberwise univ (fun σ : Equiv.Perm ι => J.map σ.toEmbedding)]
  apply Finset.sum_congr rfl
  intro I _
  have hsum : (∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I),
      realSignedWeight U σ) = subsetMinorSq U I J := by
    simpa only [Complex.re_sum, Complex.ofReal_re, realSignedWeight] using
      congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
  rw [← hsum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [(Finset.mem_filter.mp hσ).2]

/-- A common positive law on two image statistics preserves all additive
objectives of those statistics. Only the two marginal laws are used;
no common law for all minors is needed. -/
theorem projected_hull_of_two_image_law
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ)
    (J K : Finset ι) (f g : Finset ι → ℝ)
    (hfg : ∀ σ : Equiv.Perm ι,
      (η * matchingProduct a b σ).re = f (J.map σ.toEmbedding) + g (K.map σ.toEmbedding))
    (p : Finset ι → Finset ι → ℝ) (hp : ∀ I L, 0 ≤ p I L)
    (hr : ∀ I, ∑ L, p I L = subsetMinorSq U I J)
    (hc : ∀ L, ∑ I, p I L = subsetMinorSq U L K)
    (hreal : ∀ I L, p I L ≠ 0 → ∃ σ : Equiv.Perm ι,
      J.map σ.toEmbedding = I ∧ K.map σ.toEmbedding = L) :
    (η * determinantValue a b U).re ∈ convexHull ℝ
      (Set.range (fun σ : Equiv.Perm ι => (η * matchingProduct a b σ).re)) := by
  classical
  let w (q : Finset ι × Finset ι) := p q.1 q.2
  let v (q : Finset ι × Finset ι) := f q.1 + g q.2
  let S := (univ : Finset (Finset ι × Finset ι)).filter (fun q => w q ≠ 0)
  have hs : ∑ q ∈ S, w q = 1 := calc
    _ = ∑ q, w q := Finset.sum_filter_ne_zero _
    _ = ∑ I, ∑ L, p I L := Fintype.sum_prod_type _
    _ = 1 := by simp_rw [hr]; exact sum_subsetMinorSq U hU J
  have hpoint : (η * determinantValue a b U).re =
      (∑ I, subsetMinorSq U I J * f I) + ∑ L, subsetMinorSq U L K * g L := by
    rw [projected_image_expectation U hU, projected_image_expectation U hU,
      ← Finset.sum_add_distrib, ← real_signed_determinant a b U hU,
      Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [mul_left_comm η, Complex.re_ofReal_mul, hfg, mul_add]
  have hsum : (∑ q ∈ S, w q • v q) = (η * determinantValue a b U).re := calc
    _ = ∑ q, w q • v q := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro q _ hq
      have hz : w q = 0 := by simpa [S] using hq
      simp [hz]
    _ = _ := by
      rw [Fintype.sum_prod_type, hpoint]
      simp only [w, v, smul_eq_mul, mul_add, Finset.sum_add_distrib]
      congr 1
      · simp_rw [← Finset.sum_mul, hr]
      · rw [Finset.sum_comm]
        simp_rw [← Finset.sum_mul, hc]
  rw [← hsum]
  apply (convex_convexHull ℝ _).sum_mem (fun q _ => hp q.1 q.2) hs
  intro q hq
  obtain ⟨σ, hσ₁, hσ₂⟩ := hreal q.1 q.2 ((Finset.mem_filter.mp hq).2)
  exact subset_convexHull ℝ _ ⟨σ, (hfg σ).trans (by simp [v, hσ₁, hσ₂])⟩

/-- Gluing two nonnegative finite transports through a common marginal
preserves the endpoint marginals and composes the support relations. -/
theorem glue_positive_image_transport
    {α : Type*} [Fintype α] (R S : α → α → Prop) (p q : α → α → ℝ)
    (hp : ∀ x y, 0 ≤ p x y) (hq : ∀ y z, 0 ≤ q y z)
    (hR : ∀ x y, p x y ≠ 0 → R x y) (hS : ∀ y z, q y z ≠ 0 → S y z)
    (hmid : ∀ y, ∑ x, p x y = ∑ z, q y z) :
    ∃ w : α → α → ℝ,
      (∀ x z, 0 ≤ w x z) ∧
      (∀ x z, w x z ≠ 0 → ∃ y, R x y ∧ S y z) ∧
      (∀ x, ∑ z, w x z = ∑ y, p x y) ∧
      (∀ z, ∑ x, w x z = ∑ y, q y z) := by
  classical
  let m (y : α) := ∑ x, p x y
  let w (x z : α) := ∑ y, p x y * q y z / m y
  have hm (y : α) : 0 ≤ m y := Finset.sum_nonneg fun x _ => hp x y
  have hqzero (y z : α) (hy : m y = 0) : q y z = 0 := by
    have hh : (∑ z, q y z) = 0 := (hmid y).symm.trans hy
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => hq y z)).mp hh _ (mem_univ _)
  have hpzero (x y : α) (hy : m y = 0) : p x y = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hp x y)).mp hy _ (mem_univ _)
  refine ⟨w, fun x z => Finset.sum_nonneg fun y _ => div_nonneg (mul_nonneg (hp x y) (hq y z)) (hm y), ?_, ?_, ?_⟩
  · intro x z hn
    by_contra hbad
    apply hn
    unfold w
    apply Finset.sum_eq_zero
    intro y _
    by_cases hp' : p x y = 0
    · simp [hp']
    by_cases hq' : q y z = 0
    · simp [hq']
    exact False.elim (hbad ⟨y, hR x y hp', hS y z hq'⟩)
  · intro x
    unfold w
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [← Finset.sum_div, ← Finset.mul_sum, ← hmid]
    change p x y * m y / m y = p x y
    by_cases hy : m y = 0
    · simp [hy, hpzero x y hy]
    · exact mul_div_cancel_right₀ _ hy
  · intro z
    unfold w
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [← Finset.sum_div, ← Finset.sum_mul]
    change m y * q y z / m y = q y z
    by_cases hy : m y = 0
    · simp [hy, hqzero y z hy]
    · rw [mul_comm]
      exact mul_div_cancel_right₀ _ hy

/-- The individual squared-minor distributions for arbitrary nested
column sets admit an inclusion-supported positive two-marginal law.
It is constructed by composing the adjacent transports. -/
theorem exists_nested_minor_transport {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : IsUnitary U) (J K : Finset (Fin n)) (hJK : J ⊆ K) :
    ∃ μ : Finset (Fin n) → Finset (Fin n) → ℝ,
      (∀ I L, 0 ≤ μ I L) ∧ (∀ I L, μ I L ≠ 0 → I ⊆ L) ∧
      (∀ I, ∑ L, μ I L = subsetMinorSq U I J) ∧
      (∀ L, ∑ I, μ I L = subsetMinorSq U L K) := by
  classical
  have h (D : Finset (Fin n)) :
      ∃ μ : Finset (Fin n) → Finset (Fin n) → ℝ,
        (∀ I L, 0 ≤ μ I L) ∧ (∀ I L, μ I L ≠ 0 → I ⊆ L) ∧
        (∀ I, ∑ L, μ I L = subsetMinorSq U I J) ∧
        (∀ L, ∑ I, μ I L = subsetMinorSq U L (J ∪ D)) := by
    induction D using Finset.induction_on with
    | empty =>
      simp only [Finset.union_empty]
      refine ⟨fun I L => if I = L then subsetMinorSq U I J else 0, ?_, ?_, ?_, ?_⟩
      · intro I L
        change 0 ≤ if I = L then subsetMinorSq U I J else 0
        split_ifs <;> simp only [subsetMinorSq_nonneg, le_refl]
      · intro I L h
        by_cases he : I = L
        · exact he ▸ Finset.Subset.refl _
        · exact False.elim (h (if_neg he))
      · intro I
        simp
      · intro L
        simp
    | insert k D hk ih =>
      by_cases hkJ : k ∈ J
      · have he : J ∪ insert k D = J ∪ D := by
          ext x
          simp only [Finset.mem_union, Finset.mem_insert]
          constructor
          · rintro (hx | he | hx)
            · exact Or.inl hx
            · exact Or.inl (he.symm ▸ hkJ)
            · exact Or.inr hx
          · rintro (hx | hx)
            · exact Or.inl hx
            · exact Or.inr (Or.inr hx)
        simpa only [he] using ih
      have hni : k ∉ J ∪ D := by simp [hkJ, hk]
      obtain ⟨p, hp, hnest, hr, hc⟩ := ih
      obtain ⟨q, hq, hnest', hr', hc'⟩ :=
        exists_adjacent_minor_transport U hU (J ∪ D) k hni
      obtain ⟨w, hw, hcomp, hrows, hcols⟩ := glue_positive_image_transport
        (· ⊆ ·) (· ⊆ ·) p q hp hq hnest hnest' (fun L => (hc L).trans (hr' L).symm)
      refine ⟨w, hw, ?_, fun I => (hrows I).trans (hr I), fun L => ?_⟩
      · intro I L h
        obtain ⟨T, hIT, hTL⟩ := hcomp I L h
        exact hIT.trans hTL
      · rw [hcols L, hc' L, ← Finset.union_insert]
  simpa only [Finset.union_eq_right.mpr hJK] using h K


private theorem exists_perm_of_nested_images (J K I L : Finset ι)
    (hJ : J ⊆ K) (hI : I ⊆ L) (hj : I.card = J.card) (hk : L.card = K.card) :
    ∃ σ : Equiv.Perm ι, J.map σ.toEmbedding = I ∧ K.map σ.toEmbedding = L := by
  classical
  let e : K ≃ L := Fintype.equivOfCardEq (by simpa using hk.symm)
  let f : J ≃ I := Fintype.equivOfCardEq (by simpa using hj.symm)
  let u : {x : K // (x : ι) ∈ J} ≃ J := Equiv.subtypeSubtypeEquivSubtype (fun {_} h => hJ h)
  let v : {x : L // (x : ι) ∈ I} ≃ I := Equiv.subtypeSubtypeEquivSubtype (fun {_} h => hI h)
  let z : {x : K // (e x : ι) ∈ I} ≃ {x : L // (x : ι) ∈ I} :=
    e.subtypeEquiv (fun _ => Iff.rfl)
  let t : {x : K // (x : ι) ∈ J} ≃ {x : K // (e x : ι) ∈ I} :=
    u.trans (f.trans (v.symm.trans z.symm))
  let E : K ≃ L := t.extendSubtype.trans e
  let σ : Equiv.Perm ι := E.extendSubtype
  refine ⟨σ, ?_, ?_⟩
  · refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      change σ y ∈ I
      have h := E.extendSubtype_apply_of_mem y (hJ hy)
      change σ y = (E ⟨y, hJ hy⟩ : ι) at h
      rw [h]
      change (e (t.extendSubtype ⟨y, hJ hy⟩) : ι) ∈ I
      have hy' : ((⟨y, hJ hy⟩ : K) : ι) ∈ J := hy
      rw [t.extendSubtype_apply_of_mem _ hy']
      exact (t ⟨⟨y, hJ hy⟩, hy'⟩).property
    · rw [Finset.card_map, hj]
  · refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      change σ y ∈ L
      have h := E.extendSubtype_apply_of_mem y hy
      change σ y = (E ⟨y, hy⟩ : ι) at h
      rw [h]
      exact (E ⟨y, hy⟩).property
    · rw [Finset.card_map, hk]

/-- Any projected matching objective that splits into two arbitrary
scores of nested image sets belongs to the projected matching hull.
The scores need not have one sign or be linear in indicator functions. -/
theorem projected_hull_of_nested_image_scores {n : ℕ}
    (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (η : ℂ) (J K : Finset (Fin n)) (hJK : J ⊆ K) (f g : Finset (Fin n) → ℝ)
    (hfg : ∀ σ : Equiv.Perm (Fin n), (η * matchingProduct a b σ).re =
      f (J.map σ.toEmbedding) + g (K.map σ.toEmbedding)) :
    (η * determinantValue a b U).re ∈ convexHull ℝ
      (Set.range (fun σ : Equiv.Perm (Fin n) => (η * matchingProduct a b σ).re)) := by
  obtain ⟨p, hp, hnest, hr, hc⟩ := exists_nested_minor_transport U hU J K hJK
  apply projected_hull_of_two_image_law a b U hU η J K f g hfg p hp hr hc
  intro I L hn
  have hpos : 0 < p I L := lt_of_le_of_ne (hp I L) hn.symm
  have hi : 0 < subsetMinorSq U I J := by
    rw [← hr]
    exact hpos.trans_le (Finset.single_le_sum (fun L _ => hp I L) (mem_univ L))
  have hl : 0 < subsetMinorSq U L K := by
    rw [← hc]
    exact hpos.trans_le (Finset.single_le_sum (fun I _ => hp I L) (mem_univ I))
  have hI : I.card = J.card := by
    by_contra hz
    simp [subsetMinorSq, hz] at hi
  have hL : L.card = K.card := by
    by_contra hz
    simp [subsetMinorSq, hz] at hl
  exact exists_perm_of_nested_images J K I L hJK (hnest I L hn) hI hL


omit [DecidableEq ι] in
private theorem matchingProduct_real_projection
    (a b : ι → ℝ) (σ : Equiv.Perm ι) :
    (matchingProduct (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) σ).re =
      ∏ j, (a (σ j) + b j) := by
  unfold matchingProduct
  have hc : (∏ j, ((a (σ j) : ℂ) + (b j : ℂ))) =
      ((∏ j, (a (σ j) + b j) : ℝ) : ℂ) := by
    change (∏ j, ((a (σ j) : ℂ) + (b j : ℂ))) = Complex.ofRealHom (∏ j, (a (σ j) + b j))
    rw [map_prod]
    simp [map_add]
  rw [hc, Complex.ofReal_re]

/-- Three different levels in the second spectrum, with an injective first
real spectrum and no zero cross-sum, exclude every one-subset factorization.
A swap inside one side of a candidate partition preserves the image set
but changes the matching product. -/
theorem projected_real_matching_not_one_image
    (a b : ι → ℝ) (ha : Function.Injective a) (hnz : ∀ i j, a i + b j ≠ 0)
    (i j k : ι) (hb₁ : b i ≠ b j) (hb₂ : b i ≠ b k) (hb₃ : b j ≠ b k)
    (J : Finset ι) (f : Finset ι → ℝ) :
    ¬ (∀ σ : Equiv.Perm ι,
      (matchingProduct (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) σ).re =
        f (J.map σ.toEmbedding)) := by
  classical
  intro hrep
  have hex : ∃ x y : ι, (x ∈ J ↔ y ∈ J) ∧ b x ≠ b y := by
    by_cases h₁ : i ∈ J ↔ j ∈ J
    · exact ⟨i, j, h₁, hb₁⟩
    by_cases h₂ : i ∈ J ↔ k ∈ J
    · exact ⟨i, k, h₂, hb₂⟩
    exact ⟨j, k, by tauto, hb₃⟩
  obtain ⟨x, y, hxy, hby⟩ := hex
  have hne : x ≠ y := fun h => hby (congrArg b h)
  let σ := Equiv.swap x y
  have hmap : J.map σ.toEmbedding = J := by
    ext z
    simp only [Finset.mem_map_equiv, σ, Equiv.symm_swap]
    rcases eq_or_ne z x with rfl | hzx
    · simpa only [Equiv.swap_apply_left] using hxy.symm
    rcases eq_or_ne z y with rfl | hzy
    · simpa only [Equiv.swap_apply_right] using hxy
    · rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]
  have hrep1 := hrep (Equiv.refl ι)
  have hmap1 : J.map (Equiv.refl ι).toEmbedding = J := by simp
  rw [hmap1] at hrep1
  have he := hrep1.trans ((hrep σ).trans (congrArg f hmap)).symm
  simp only [matchingProduct_real_projection, Equiv.refl_apply,
    Finset.map_refl] at he
  have hy : y ∈ (Finset.univ : Finset ι).erase x := Finset.mem_erase.mpr ⟨hne.symm, mem_univ _⟩
  simp only [← Finset.mul_prod_erase Finset.univ _ (mem_univ x),
    ← Finset.mul_prod_erase (Finset.univ.erase x) _ hy] at he
  have hout :
      (∏ z ∈ (Finset.univ.erase x).erase y, (a (σ z) + b z)) =
        ∏ z ∈ (Finset.univ.erase x).erase y, (a z + b z) := by
    apply Finset.prod_congr rfl
    intro z hz
    have hy' := Finset.ne_of_mem_erase hz
    have hx' := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hz)
    simp [σ, Equiv.swap_apply_of_ne_of_ne hx' hy']
  rw [hout] at he
  simp only [σ, Equiv.swap_apply_left, Equiv.swap_apply_right] at he
  let R := ∏ z ∈ (Finset.univ.erase x).erase y, (a z + b z)
  have hRn : R ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun z _ => hnz z z)
  have he' : ((a x + b x) * (a y + b y)) * R =
      ((a y + b x) * (a x + b y)) * R := by
    dsimp [R]
    simpa only [mul_assoc] using he
  have he'' := mul_right_cancel₀ hRn he'
  have hz : (a x - a y) * (b y - b x) = 0 := by
    linear_combination he''
  exact mul_ne_zero (sub_ne_zero.mpr (ha.ne hne)) (sub_ne_zero.mpr hby.symm) hz


private theorem matchingProduct_two_values_factor (a : ι → ℂ)
    (J : Finset ι) (c d : ℂ) (σ : Equiv.Perm ι) :
    matchingProduct a (fun j => if j ∈ J then c else d) σ =
      ∏ i, (a i + if i ∈ J.map σ.toEmbedding then c else d) := by
  classical
  unfold matchingProduct
  rw [← Equiv.prod_comp σ (fun i => a i + if i ∈ J.map σ.toEmbedding then c else d)]
  simp [Finset.mem_map_equiv]

/-- Strict enlargement on actual spectral data, not merely on artificial
permutation scores: midpoint interpolation between two two-valued lists
produces a sum of two nested image scores, but neither side of any single
subset partition can keep three different spectral levels separated. -/
theorem nested_image_scores_strictly_extend_one_image :
    ∃ a b : Fin 3 → ℂ, ∃ J K : Finset (Fin 3), J ⊆ K ∧
      (∃ f g : Finset (Fin 3) → ℝ, ∀ σ : Equiv.Perm (Fin 3),
        (matchingProduct a b σ).re = f (J.map σ.toEmbedding) + g (K.map σ.toEmbedding)) ∧
      (∀ L : Finset (Fin 3), ∀ h : Finset (Fin 3) → ℝ, ¬ ∀ σ : Equiv.Perm (Fin 3),
        (matchingProduct a b σ).re = h (L.map σ.toEmbedding)) := by
  classical
  let x (i : Fin 3) : ℝ := (i.val : ℝ) + 1
  let a (i : Fin 3) : ℂ := x i
  let J : Finset (Fin 3) := {0}
  let K : Finset (Fin 3) := {0, 1}
  let y₀ (i : Fin 3) : ℝ := if i ∈ J then 3 else 1
  let y₁ (i : Fin 3) : ℝ := if i ∈ K then 3 else 1
  let y (i : Fin 3) : ℝ := (y₀ i + y₁ i) / 2
  let b (i : Fin 3) : ℂ := y i
  let b₀ (i : Fin 3) : ℂ := if i ∈ J then 3 else 1
  let b₁ (i : Fin 3) : ℂ := if i ∈ K then 3 else 1
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  refine ⟨a, b, J, K, by simp [J, K], ?_, ?_⟩
  · let s (L : Finset (Fin 3)) : ℝ := ((∏ i, (a i + if i ∈ L then 3 else 1)) : ℂ).re / 2
    refine ⟨s, s, fun σ => ?_⟩
    have hmid : matchingProduct a b σ =
        (matchingProduct a b₀ σ + matchingProduct a b₁ σ) / 2 := by
      simp only [matchingProduct, Fin.prod_univ_three]
      norm_num [b, y, y₀, y₁, b₀, b₁, J, K, h20, h21]
      ring
    rw [hmid, matchingProduct_two_values_factor a J 3 1 σ,
      matchingProduct_two_values_factor a K 3 1 σ]
    norm_num [s, Complex.add_re, Complex.div_re,
      Complex.normSq_ofNat]
    ring
  · intro L h
    apply projected_real_matching_not_one_image x y _ _ 0 1 2 _ _ _ L h
    · intro i j he
      apply Fin.ext
      dsimp only [x] at he
      exact_mod_cast add_right_cancel he
    · intro i j
      have hx : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
      have h0 : 0 < y₀ j := by unfold y₀; split_ifs <;> norm_num
      have h1 : 0 < y₁ j := by unfold y₁; split_ifs <;> norm_num
      apply ne_of_gt
      dsimp [x, y]
      linarith
    · norm_num [y, y₀, y₁, J, K, h20, h21]
    · norm_num [y, y₀, y₁, J, K, h20, h21]
    · norm_num [y, y₀, y₁, J, K, h20, h21]


/-- If the complex matching products, not just one projection, split
across nested image scores, the spectral determinant hull follows. -/
theorem holds_of_nested_complex_image_scores {n : ℕ}
    (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (J K : Finset (Fin n)) (hJK : J ⊆ K) (f g : Finset (Fin n) → ℂ)
    (hfg : ∀ σ : Equiv.Perm (Fin n), matchingProduct a b σ =
      f (J.map σ.toEmbedding) + g (K.map σ.toEmbedding)) :
    Holds a b U := by
  rw [holds_iff_directional]
  intro η
  have h := projected_hull_of_nested_image_scores a b U hU η J K hJK
    (fun I => (η * f I).re) (fun L => (η * g L).re) (fun σ => by
      rw [hfg σ, mul_add, Complex.add_re])
  by_contra! hn
  have hsub : Set.range (fun σ : Equiv.Perm (Fin n) => (η * matchingProduct a b σ).re) ⊆
      Set.Iio (η * determinantValue a b U).re := by
    rintro _ ⟨σ, rfl⟩
    exact hn σ
  have hh : (η * determinantValue a b U).re < (η * determinantValue a b U).re :=
    convexHull_min hsub (convex_Iio (𝕜 := ℝ) _) h
  exact (lt_irrefl _) hh

end
end MOC
