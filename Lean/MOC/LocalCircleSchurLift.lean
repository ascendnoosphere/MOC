import MOC.NormalCompressionReduction
import MOC.Support
import Mathlib.Data.Fin.Tuple.Basic

open BigOperators Matrix

namespace MOC

noncomputable section

/-- An affine interlace of the reciprocal spectra lifts each regular child
matching to the parent hull. The deleted partner has value `r`. -/
theorem schurMatchingProduct_mem_hull_of_ne {n : ℕ}
    (h : Fin (n + 1) → ℂ) (a x : Fin n → ℂ) (r t c d : ℂ)
    (lam : Fin (n + 1) → ℝ) (δ : Fin n → ℝ)
    (hl : ∀ i, lam i.castSucc ≤ δ i) (hu : ∀ i, δ i ≤ lam i.succ)
    (hd : d ≠ 0) (hh : ∀ i, h i + r ≠ 0) (ha : ∀ i, a i + r ≠ 0)
    (hx : ∀ i, x i - r ≠ 0)
    (hhl : ∀ i, (h i + r)⁻¹ = c + d * (lam i : ℂ))
    (hal : ∀ i, (a i + r)⁻¹ = c + d * (δ i : ℂ))
    (ht : ∏ i, (h i + r) = t * ∏ i, (a i + r)) :
    t * (∏ i, (a i + x i)) ∈ convexHull ℝ (Set.range (matchingProduct h (Fin.cons r x))) := by
  classical
  let z : Fin n → ℂ := fun i => (x i - r)⁻¹
  let D : ℂ := ∏ i, (h i + r)
  let E : ℂ := ∏ i, (x i - r)
  let L := LinearMap.mulLeft ℝ (D * E)
  have hfactor (b w : ℂ) (hb : b + r ≠ 0) (hw : w - r ≠ 0) :
      (b + r) * ((w - r) * ((w - r)⁻¹ + (b + r)⁻¹)) = b + w := by
    field_simp [hb, hw]
    ring
  have hchild :
      L (∏ i, (z i + (c + d * (δ i : ℂ)))) = t * ∏ i, (a i + x i) := by
    change (D * E) * (∏ i, (z i + (c + d * (δ i : ℂ)))) = _
    rw [show D = t * ∏ i, (a i + r) from ht]
    rw [mul_assoc, mul_assoc]
    congr 1
    simp only [E, z, ← hal, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => hfactor (a i) (x i) (ha i) (hx i))
  rw [← hchild]
  apply convexHull_min _ ((convex_convexHull ℝ _).linear_preimage L)
    (affine_interlacing_prod_mem_rectangular_hull z lam δ hl hu c d hd)
  rintro _ ⟨f, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : Fin (n + 1), m ∉ Set.range f := by
    by_contra! hsurj
    have he := Fintype.card_congr (Equiv.ofBijective f ⟨f.injective, hsurj⟩)
    simp only [Fintype.card_fin] at he
    omega
  let σ : Equiv.Perm (Fin (n + 1)) :=
    Equiv.ofBijective (Fin.cons m f)
      (Finite.injective_iff_bijective.mp (Fin.cons_injective_of_injective hm f.injective))
  have hprod : (h m + r) * (∏ i, (h (f i) + r)) = D := by
    change (h (σ 0) + r) * (∏ i : Fin n, (h (σ i.succ) + r)) = _
    calc
      _ = ∏ i : Fin (n + 1), (h (σ i) + r) :=
        (Fin.prod_univ_succ (fun i => h (σ i) + r)).symm
      _ = D := Equiv.prod_comp σ (fun i => h i + r)
  refine subset_convexHull ℝ _ ⟨σ, ?_⟩
  unfold matchingProduct
  rw [Fin.prod_univ_succ]
  change (h m + r) * (∏ i, (h (f i) + x i)) =
    (D * E) * (∏ i, (z i + (c + d * (lam (f i) : ℂ))))
  rw [← hprod, mul_assoc, mul_assoc]
  congr 1
  simp only [E, z, ← hhl, ← Finset.prod_mul_distrib]
  exact (Finset.prod_congr rfl (fun i _ => hfactor (h (f i)) (x i) (hh (f i)) (hx i))).symm

/-- The lift also applies when some retained partner values equal the deleted
partner value. -/
theorem schurMatchingProduct_mem_hull {n : ℕ}
    (h : Fin (n + 1) → ℂ) (a x : Fin n → ℂ) (r t c d : ℂ)
    (lam : Fin (n + 1) → ℝ) (δ : Fin n → ℝ)
    (hl : ∀ i, lam i.castSucc ≤ δ i) (hu : ∀ i, δ i ≤ lam i.succ)
    (hd : d ≠ 0) (hh : ∀ i, h i + r ≠ 0) (ha : ∀ i, a i + r ≠ 0)
    (hhl : ∀ i, (h i + r)⁻¹ = c + d * (lam i : ℂ))
    (hal : ∀ i, (a i + r)⁻¹ = c + d * (δ i : ℂ))
    (ht : ∏ i, (h i + r) = t * ∏ i, (a i + r)) :
    t * (∏ i, (a i + x i)) ∈ convexHull ℝ (Set.range (matchingProduct h (Fin.cons r x))) := by
  classical
  let P (y : Fin n → ℂ) := t * ∏ i, (a i + y i)
  let M (σ : Equiv.Perm (Fin (n + 1))) (y : Fin n → ℂ) :=
    matchingProduct h (Fin.cons r y) σ
  by_contra hbad
  obtain ⟨L, q, hq, hP⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _)
    (Set.finite_range (matchingProduct h (Fin.cons r x))).isClosed_convexHull hbad
  have hPm : Continuous (fun y => L (P y)) := by
    apply L.continuous.comp
    exact continuous_const.mul (continuous_finset_prod _ fun i _ =>
      continuous_const.add (continuous_apply i))
  have hM (σ : Equiv.Perm (Fin (n + 1))) : Continuous (fun y => L (M σ y)) := by
    apply L.continuous.comp
    unfold M matchingProduct
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    exact continuous_const.mul (continuous_finset_prod _ fun i _ =>
      continuous_const.add (continuous_apply i))
  let O := ⋂ σ : Equiv.Perm (Fin (n + 1)), {y | L (M σ y) < L (P y)}
  have hO : IsOpen O := isOpen_iInter_of_finite (fun σ => isOpen_lt (hM σ) hPm)
  have hxO : x ∈ O := Set.mem_iInter.mpr fun σ =>
    (hq _ (subset_convexHull ℝ _ ⟨σ, rfl⟩)).trans hP
  have hdense : Dense (Set.pi Set.univ (fun _ : Fin n => ({r}ᶜ : Set ℂ))) :=
    dense_pi Set.univ (fun _ _ => dense_compl_singleton r)
  obtain ⟨y, hyO, hy⟩ := hdense.inter_open_nonempty O hO ⟨x, hxO⟩
  have hy' (i : Fin n) : y i - r ≠ 0 :=
    sub_ne_zero.mpr (hy i (Set.mem_univ i))
  have hyHull := schurMatchingProduct_mem_hull_of_ne h a y r t c d lam δ
    hl hu hd hh ha hy' hhl hal ht
  have hsep : P y ∈ {z | L z < L (P y)} := by
    apply convexHull_min _ (convex_halfSpace_lt L.toLinearMap.isLinear _) hyHull
    rintro _ ⟨σ, rfl⟩
    exact Set.mem_iInter.mp hyO σ
  exact (lt_irrefl (L (P y))) hsep

private def pivotLabel (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n + 1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (Sum.inl ()) Sum.inr
  left_inv := by
    rintro (i | i)
    · cases i
      rfl
    · rfl
  right_inv := by intro i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Scaling the child hull maps it into the parent hull while all labels of
the untouched block keep their partners. -/
theorem schurMatchingHull_subset {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (h : Fin (n + 1) → ℂ) (a : Fin n → ℂ) (g : κ → ℂ) (b : Fin n ⊕ κ → ℂ)
    (r t c d : ℂ) (lam : Fin (n + 1) → ℝ) (δ : Fin n → ℝ)
    (hl : ∀ i, lam i.castSucc ≤ δ i) (hu : ∀ i, δ i ≤ lam i.succ)
    (hd : d ≠ 0) (hh : ∀ i, h i + r ≠ 0) (ha : ∀ i, a i + r ≠ 0)
    (hhl : ∀ i, (h i + r)⁻¹ = c + d * (lam i : ℂ))
    (hal : ∀ i, (a i + r)⁻¹ = c + d * (δ i : ℂ))
    (ht : ∏ i, (h i + r) = t * ∏ i, (a i + r)) :
    convexHull ℝ (Set.range (matchingProduct (Sum.elim a g) b)) ⊆
      (LinearMap.mulLeft ℝ t) ⁻¹'
        convexHull ℝ (Set.range (matchingProduct (Sum.elim h g)
          (Sum.elim (Fin.cons r (b ∘ Sum.inl)) (b ∘ Sum.inr)))) := by
  classical
  let bP : Fin (n + 1) ⊕ κ → ℂ :=
    Sum.elim (Fin.cons r (b ∘ Sum.inl)) (b ∘ Sum.inr)
  let K := convexHull ℝ (Set.range (matchingProduct (Sum.elim h g) bP))
  have hK : Convex ℝ K := convex_convexHull ℝ _
  apply convexHull_min _ (hK.linear_preimage (LinearMap.mulLeft ℝ t))
  rintro _ ⟨σ, rfl⟩
  let x (i : Fin n) := b (σ.symm (Sum.inl i))
  let y (j : κ) := b (σ.symm (Sum.inr j))
  let F := ∏ j : κ, (g j + y j)
  have hchild : matchingProduct (Sum.elim a g) b σ = (∏ i, (a i + x i)) * F := by
    rw [← Equiv.symm_symm σ, matchingProduct_inverse, Fintype.prod_sum_type]
    rfl
  let L := LinearMap.mulRight ℝ F
  change t * matchingProduct (Sum.elim a g) b σ ∈ K
  rw [hchild, ← mul_assoc]
  change t * (∏ i, (a i + x i)) ∈ L ⁻¹' K
  apply convexHull_min _ (hK.linear_preimage L)
    (schurMatchingProduct_mem_hull h a x r t c d lam δ hl hu hd hh ha hhl hal ht)
  rintro _ ⟨τ, rfl⟩
  let e : Unit ⊕ (Fin n ⊕ κ) ≃ Fin (n + 1) ⊕ κ :=
    (Equiv.sumAssoc Unit (Fin n) κ).symm.trans ((pivotLabel n).sumCongr (Equiv.refl κ))
  let σp : Equiv.Perm (Fin (n + 1) ⊕ κ) :=
    e.symm.trans (((Equiv.refl Unit).sumCongr σ).trans e)
  let τp : Equiv.Perm (Fin (n + 1) ⊕ κ) := τ.sumCongr (Equiv.refl κ)
  have he₁ : e (Sum.inl ()) = Sum.inl 0 := rfl
  have he₂ (i : Fin n) : e (Sum.inr (Sum.inl i)) = Sum.inl i.succ := rfl
  have he₃ (j : κ) : e (Sum.inr (Sum.inr j)) = Sum.inr j := rfl
  have hB₀ : bP (σp.symm (Sum.inl 0)) = r := by
    change bP (e (Sum.map id σ.symm (e.symm (Sum.inl 0)))) = r
    rw [← he₁, Equiv.symm_apply_apply]
    change bP (e (Sum.inl ())) = r
    rw [he₁]
    rfl
  have hbP (j : Fin n ⊕ κ) : bP (e (Sum.inr j)) = b j := by
    rcases j with i | j
    · rw [he₂]
      rfl
    · rw [he₃]
      rfl
  have hB (j : Fin n ⊕ κ) : bP (σp.symm (e (Sum.inr j))) = b (σ.symm j) := by
    change bP (e (Sum.map id σ.symm (e.symm (e (Sum.inr j))))) = b (σ.symm j)
    rw [Equiv.symm_apply_apply]
    exact hbP (σ.symm j)
  apply subset_convexHull ℝ _
  refine ⟨σp.trans τp, ?_⟩
  unfold matchingProduct
  rw [← Equiv.prod_comp σp.symm (fun j => Sum.elim h g ((σp.trans τp) j) + bP j)]
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [Fintype.prod_sum_type, Fin.prod_univ_succ, Fin.prod_univ_succ]
  change ((h (τ 0) + bP (σp.symm (Sum.inl 0))) *
      (∏ i : Fin n, (h (τ i.succ) + bP (σp.symm (Sum.inl i.succ))))) *
      (∏ j : κ, (g j + bP (σp.symm (Sum.inr j)))) =
    ((h (τ 0) + r) * ∏ i : Fin n, (h (τ i.succ) + x i)) * F
  simp only [hB₀, ← he₂, ← he₃, hB, x, F, y]

end

end MOC
