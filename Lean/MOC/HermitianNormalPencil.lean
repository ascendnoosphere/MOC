import MOC.FiveNonreal
import MOC.InterlacingCommonLaw
import MOC.WeakHermitianCompressionInterlacing
import Mathlib.Data.Fin.Tuple.Sort

/-! The interlacing lift at a real pivot retains the squared unitary
entries as the masses of the possible assignments at that pivot. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {n : ℕ}

private theorem exists_omitted_label (f : Fin n ↪ Fin (n + 1)) :
    ∃ j, j ∉ Set.range f := by
  by_contra! h
  have he := Fintype.card_congr (Equiv.ofBijective f ⟨f.injective, h⟩)
  simp only [Fintype.card_fin] at he
  omega

private def omittedLabel (f : Fin n ↪ Fin (n + 1)) : Fin (n + 1) :=
  Classical.choose (exists_omitted_label f)

private theorem omittedLabel_not_mem (f : Fin n ↪ Fin (n + 1)) :
    omittedLabel f ∉ Set.range f :=
  Classical.choose_spec (exists_omitted_label f)

private theorem map_eq_erase_of_not_mem_range (f : Fin n ↪ Fin (n + 1)) (j : Fin (n + 1))
    (hj : j ∉ Set.range f) : Finset.univ.map f = Finset.univ.erase j := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hi
    exact Finset.mem_erase.mpr ⟨fun h => hj ⟨k, h⟩, Finset.mem_univ _⟩
  · simp

private theorem omittedLabel_eq_iff (f : Fin n ↪ Fin (n + 1)) (j : Fin (n + 1)) :
    omittedLabel f = j ↔ j ∉ Set.range f := by
  classical
  constructor
  · intro h
    rw [← h]
    exact omittedLabel_not_mem f
  · intro h
    by_contra hne
    have hj : j ∈ Finset.univ.map f := by
      rw [map_eq_erase_of_not_mem_range f _ (omittedLabel_not_mem f)]
      exact Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩
    obtain ⟨k, _, hk⟩ := Finset.mem_map.mp hj
    exact h ⟨k, hk⟩

private theorem partialMatchingFunction_at_negative_knot
    (a : Fin (n + 1) → ℝ) (f : Fin n ↪ Fin (n + 1)) (j : Fin (n + 1)) :
    partialMatchingFunction a f (fun _ => -(a j : ℂ)) =
      if omittedLabel f = j then ∏ k ∈ Finset.univ.erase j, ((a k : ℂ) - (a j : ℂ))
      else 0 := by
  classical
  unfold partialMatchingFunction
  by_cases h : omittedLabel f = j
  · rw [if_pos h]
    simp_rw [← sub_eq_add_neg]
    rw [← Finset.prod_map Finset.univ f (fun k => (a k : ℂ) - (a j : ℂ)),
      map_eq_erase_of_not_mem_range f j ((omittedLabel_eq_iff f j).mp h)]
  · rw [if_neg h]
    obtain ⟨k, hk⟩ := Classical.not_not.mp (mt (omittedLabel_eq_iff f j).mpr h)
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk, add_neg_cancel])

private theorem unitary_conjugation_sub_scalar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (V : Matrix ι ι ℂ) (hV : IsUnitary V) (z : ℂ) :
    V * diagonal (fun i => (x i : ℂ) - z) * Vᴴ =
      V * diagonal (fun i => (x i : ℂ)) * Vᴴ - z • (1 : Matrix ι ι ℂ) := by
  rw [← Matrix.diagonal_sub (fun i => (x i : ℂ)) (fun _ : ι => z),
    ← Matrix.smul_one_eq_diagonal, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hV.1]

private theorem compression_product_at_negative_knot
    (a : Fin (n + 1) → ℝ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hU : IsUnitary U) (p j : Fin (n + 1)) (δ : Fin n → ℝ)
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : IsUnitary W)
    (hC : (U * diagonal (fun i => (a i : ℂ)) * Uᴴ).submatrix p.succAbove p.succAbove =
      W * diagonal (fun i => (δ i : ℂ)) * Wᴴ) :
    (∏ i, ((δ i : ℂ) - (a j : ℂ))) =
      (Complex.normSq (U p j) : ℂ) * ∏ i ∈ Finset.univ.erase j, ((a i : ℂ) - (a j : ℂ)) := by
  have hsub :
      (U * diagonal (fun i => (a i : ℂ) - (a j : ℂ)) * Uᴴ).submatrix
        p.succAbove p.succAbove =
      W * diagonal (fun i => (δ i : ℂ) - (a j : ℂ)) * Wᴴ := by
    rw [unitary_conjugation_sub_scalar a U hU, unitary_conjugation_sub_scalar δ W hW,
      Matrix.submatrix_sub, Matrix.submatrix_smul,
      Matrix.submatrix_one _ Fin.succAbove_right_injective, hC]
  rw [← Matrix.det_diagonal, ← det_unitary_conjugation W _ hW, ← hsub,
    det_principal_unitary_diagonalization (fun i => (a i : ℂ) - (a j : ℂ)) hU p,
    Finset.sum_eq_single j]
  · intro i _ hi
    rw [Finset.prod_eq_zero (i := j) (Finset.mem_erase.mpr ⟨hi.symm, Finset.mem_univ _⟩)
      (sub_self (a j : ℂ)), mul_zero]
  · simp

/-- A Hermitian principal compression with simple parent spectrum has one
interlacing law for every diagonal partner. The total weight of injections
omitting parent label `j` is the squared modulus of the deleted row entry. -/
theorem exists_hermitian_compression_injection_weights
    (a : Fin (n + 1) → ℝ) (ha : StrictMono a)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U) (p : Fin (n + 1)) :
    ∃ (δ : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℂ)
        (s : Finset (Fin n ↪ Fin (n + 1))) (w : (Fin n ↪ Fin (n + 1)) → ℝ),
      IsUnitary W ∧
      (U * diagonal (fun i => (a i : ℂ)) * Uᴴ).submatrix p.succAbove p.succAbove =
        W * diagonal (fun i => (δ i : ℂ)) * Wᴴ ∧
      (∀ f ∈ s, 0 ≤ w f) ∧ (∑ f ∈ s, w f = 1) ∧
      (∀ b : Fin n → ℂ, ∑ f ∈ s, (w f : ℂ) * partialMatchingFunction a f b =
        ∏ i, ((δ i : ℂ) + b i)) ∧
      ∀ j, ∑ f ∈ s.filter (fun f => j ∉ Set.range f), w f = Complex.normSq (U p j) := by
  classical
  obtain ⟨δ, W, hW, hδ, hC⟩ :=
    exists_interlacing_of_hermitian_compression a ha.monotone U hU p
  obtain ⟨s, w, hw, hmass, hrep⟩ :=
    exists_interlacing_injection_weights a δ (fun i => (hδ i).1) (fun i => (hδ i).2)
  refine ⟨δ, W, s, w, hW, hC, hw, hmass, hrep, fun j => ?_⟩
  let q : ℂ := ∏ i ∈ Finset.univ.erase j, ((a i : ℂ) - (a j : ℂ))
  have hq : q ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact sub_ne_zero.mpr (fun eq => (Finset.mem_erase.mp hi).1
      (ha.injective (Complex.ofReal_injective eq)))
  have hsum := hrep (fun _ => -(a j : ℂ))
  simp_rw [partialMatchingFunction_at_negative_knot, mul_ite, mul_zero,
    ← Finset.sum_filter, ← Finset.sum_mul, ← Complex.ofReal_sum] at hsum
  have hcomp := compression_product_at_negative_knot a U hU p j δ W hW hC
  have hmassFactor :
      ((∑ f ∈ s.filter (fun f => omittedLabel f = j), w f : ℝ) : ℂ) * q =
        (Complex.normSq (U p j) : ℂ) * q := by
    dsimp only [q]
    rw [← hcomp]
    simpa only [sub_eq_add_neg] using hsum
  have hfilter : s.filter (fun f => omittedLabel f = j) =
      s.filter (fun f => j ∉ Set.range f) := by
    ext f
    simp only [Finset.mem_filter, omittedLabel_eq_iff]
  rw [← hfilter]
  exact Complex.ofReal_injective (mul_right_cancel₀ hq hmassFactor)

private def extendPartialMatching (p : Fin (n + 1)) (f : Fin n ↪ Fin (n + 1)) :
    Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' p).trans ((finSuccEquiv n).symm.trans
    (Equiv.ofBijective (Fin.cons (omittedLabel f) f)
      (Finite.injective_iff_bijective.mp
        (Fin.cons_injective_of_injective (omittedLabel_not_mem f) f.injective))))

private theorem extendPartialMatching_apply_pivot (p : Fin (n + 1))
    (f : Fin n ↪ Fin (n + 1)) :
    extendPartialMatching p f p = omittedLabel f := by
  simp only [extendPartialMatching, Equiv.trans_apply, finSuccEquiv'_at,
    finSuccEquiv_symm_none, Equiv.ofBijective_apply, Fin.cons_zero]

private theorem extendPartialMatching_apply_succAbove (p : Fin (n + 1))
    (f : Fin n ↪ Fin (n + 1)) (k : Fin n) :
    extendPartialMatching p f (p.succAbove k) = f k := by
  simp only [extendPartialMatching, Equiv.trans_apply, finSuccEquiv'_succAbove,
    finSuccEquiv_symm_some, Equiv.ofBijective_apply, Fin.cons_succ]

/-- For a regular real partner pivot, each fiber of matchings with the
same eigenvalue at that pivot has the prescribed squared unitary mass
in the directional bound obtained from the smaller Hermitian problem. -/
theorem hermitian_real_pivot_fixed_mass_bound
    (hSmall : HermitianByNormal (Fin n))
    (a : Fin (n + 1) → ℝ) (b : Fin (n + 1) → ℂ) (ha : Function.Injective a)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U)
    (p : Fin (n + 1)) (hp : (b p).im = 0)
    (hb : ∀ k ≠ p, b k - b p ≠ 0) (hab : ∀ i, (a i : ℂ) + b p ≠ 0)
    (η : ℂ) (bound : Fin (n + 1) → ℝ)
    (hbound : ∀ σ : Equiv.Perm (Fin (n + 1)),
      (η * matchingProduct (fun i => (a i : ℂ)) b σ).re ≤ bound (σ p)) :
    (η * determinantValue (fun i => (a i : ℂ)) b U).re ≤
      ∑ i, Complex.normSq (U i p) * bound i := by
  classical
  let A : Fin (n + 1) → ℂ := fun i => a i
  let α : Fin n → ℂ := fun k => (b (p.succAbove k) - b p)⁻¹
  let β : Fin (n + 1) → ℂ := fun i => (A i + b p)⁻¹
  let x : Fin (n + 1) → ℝ := fun i => (a i + (b p).re)⁻¹
  have hr : ((b p).re : ℂ) = b p :=
    Complex.ext rfl (by simpa only [Complex.ofReal_im] using hp.symm)
  have hβreal : (fun i => (x i : ℂ)) = β := by
    funext i
    simp only [x, β, A, Complex.ofReal_inv, Complex.ofReal_add, hr]
  have hx : Function.Injective x :=
    fun _ _ he => ha (add_right_cancel (inv_injective he))
  let e := Tuple.sort x
  let lam := x ∘ e
  have hlam : StrictMono lam :=
    (Tuple.monotone_sort x).strictMono_of_injective (hx.comp e.injective)
  have hβlam (i : Fin (n + 1)) : (lam i : ℂ) = β (e i) := congrFun hβreal (e i)
  have hU' : IsUnitary Uᴴ :=
    ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hU.2,
      by simpa only [Matrix.conjTranspose_conjTranspose] using hU.1⟩
  let V := Uᴴ.submatrix (Equiv.refl _) e
  have hV : IsUnitary V := unitary_reindex (Equiv.refl _) e hU'
  have hrelabel :
      V * diagonal (fun i => (lam i : ℂ)) * Vᴴ = Uᴴ * diagonal β * (Uᴴ)ᴴ := by
    rw [show (fun i => (lam i : ℂ)) = β ∘ e from funext hβlam]
    dsimp only [V]
    rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_diagonal_equiv β e,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv] <;> rfl
  obtain ⟨δ, W, s, w, hW, hC, hw, _, hrep, hm⟩ :=
    exists_hermitian_compression_injection_weights lam hlam V hV p
  have hspec : poleCompression b A Uᴴ p = W * diagonal (fun i => (δ i : ℂ)) * Wᴴ := by
    rw [← hC, hrelabel]
    rfl
  have hW' : IsUnitary Wᴴ :=
    ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hW.2,
      by simpa only [Matrix.conjTranspose_conjTranspose] using hW.1⟩
  let D := poleFactor b A p
  have hdet :
      determinantValue A b U = D * determinantValue (fun i => (δ i : ℂ)) α Wᴴ := by
    have hswap : determinantValue A b U = determinantValue b A Uᴴ := by
      rw [← determinantValue_left_conjugation b A U hU]
      change (diagonal A + U * diagonal b * Uᴴ).det =
        (U * diagonal b * Uᴴ + diagonal A).det
      exact congrArg Matrix.det (add_comm _ _)
    rw [hswap, determinantValue_pole b A Uᴴ hU' p hb hab,
      ← determinantValue_left_conjugation _ _ W hW]
    change D * (diagonal α + poleCompression b A Uᴴ p).det =
      D * (W * diagonal (fun i => (δ i : ℂ)) * Wᴴ + diagonal α).det
    rw [hspec, add_comm (diagonal α)]
  obtain ⟨τ, hτ⟩ := (holds_iff_directional _ _ _).mp (hSmall δ α Wᴴ hW') (η * D)
  let π (f : Fin n ↪ Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
    (extendPartialMatching p (τ.toEmbedding.trans f)).trans e
  have hπpivot (f : Fin n ↪ Fin (n + 1)) : π f p = e (omittedLabel f) := by
    have he : omittedLabel (τ.toEmbedding.trans f) = omittedLabel f :=
      (omittedLabel_eq_iff _ _).mpr (fun hm => by
        obtain ⟨k, hk⟩ := hm
        exact omittedLabel_not_mem f ⟨τ k, hk⟩)
    simp only [π, Equiv.trans_apply, extendPartialMatching_apply_pivot, he]
  have hπprod (f : Fin n ↪ Fin (n + 1)) :
      matchingProduct A b (π f) = D * partialMatchingFunction lam f (α ∘ τ.symm) := by
    have hswap : matchingProduct A b (π f) = matchingProduct b A (π f).symm := by
      rw [matchingProduct_inverse]
      simp only [matchingProduct, add_comm]
    rw [hswap, matchingProduct_pole b A p _ hb hab]
    congr 1
    unfold poleMatchingProduct partialMatchingFunction
    rw [← Equiv.prod_comp τ (fun i => (lam (f i) : ℂ) + (α ∘ τ.symm) i)]
    apply Finset.prod_congr rfl
    intro k _
    simp only [Equiv.symm_symm, π, Equiv.trans_apply, extendPartialMatching_apply_succAbove,
      Function.comp_apply, Equiv.symm_apply_apply]
    change α k + β (e (f (τ k))) = (lam (f (τ k)) : ℂ) + α k
    rw [hβlam]
    exact add_comm _ _
  have hlaw :
      (∑ f ∈ s, (w f : ℂ) * partialMatchingFunction lam f (α ∘ τ.symm)) =
        matchingProduct (fun i => (δ i : ℂ)) α τ := by
    rw [hrep]
    unfold matchingProduct
    rw [← Equiv.prod_comp τ (fun i => (δ i : ℂ) + (α ∘ τ.symm) i)]
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  have hweighted :
      D * matchingProduct (fun i => (δ i : ℂ)) α τ =
        ∑ f ∈ s, (w f : ℂ) * matchingProduct A b (π f) := by
    rw [← hlaw, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    rw [hπprod f, mul_left_comm D]
  have hfiber :
      (∑ f ∈ s, w f * bound (e (omittedLabel f))) =
        ∑ i, Complex.normSq (U i p) * bound i := by
    rw [← Finset.sum_fiberwise s omittedLabel (fun f => w f * bound (e (omittedLabel f))),
      ← Equiv.sum_comp e (fun i => Complex.normSq (U i p) * bound i)]
    apply Finset.sum_congr rfl
    intro i _
    have hsum :
        (∑ f ∈ s.filter (fun f => omittedLabel f = i), w f * bound (e (omittedLabel f))) =
          ∑ f ∈ s.filter (fun f => omittedLabel f = i), w f * bound (e i) := by
      apply Finset.sum_congr rfl
      intro f hf
      rw [(Finset.mem_filter.mp hf).2]
    have hfilter : s.filter (fun f => omittedLabel f = i) =
        s.filter (fun f => i ∉ Set.range f) := by
      ext f
      simp only [Finset.mem_filter, omittedLabel_eq_iff]
    rw [hsum, ← Finset.sum_mul, hfilter, hm i]
    change Complex.normSq (star (U (e i) p)) * bound (e i) =
      Complex.normSq (U (e i) p) * bound (e i)
    simp only [Complex.star_def, Complex.normSq_conj]
  calc
    (η * determinantValue A b U).re ≤
        ((η * D) * matchingProduct (fun i => (δ i : ℂ)) α τ).re := by
      simpa only [hdet, mul_assoc] using hτ
    _ = ∑ f ∈ s, w f * (η * matchingProduct A b (π f)).re := by
      rw [mul_assoc, hweighted, Finset.mul_sum, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro f _
      rw [mul_left_comm η, Complex.re_ofReal_mul]
    _ ≤ ∑ f ∈ s, w f * bound (e (omittedLabel f)) :=
      Finset.sum_le_sum (fun f hf => mul_le_mul_of_nonneg_left
        (by simpa only [hπpivot f] using hbound (π f)) (hw f hf))
    _ = ∑ i, Complex.normSq (U i p) * bound i := hfiber

/-- If only two distinct real labels have positive mass, their scaled
conditional slope hulls are tested separately at the two opposite real
parameters. Common witnesses at these parameters give a law for the
whole complex pencil. -/
theorem affine_pencil_of_two_group_real_anchors
    (a b : ℝ) (hne : a ≠ b) (d₀ d₁ : ℂ) (K L : Set ℂ)
    (hA : d₀ - (a : ℂ) * d₁ ∈ (fun y : ℂ => ((b : ℂ) - (a : ℂ)) * y) '' L)
    (hB : d₀ - (b : ℂ) * d₁ ∈ (fun x : ℂ => ((a : ℂ) - (b : ℂ)) * x) '' K) :
    ∃ x ∈ K, ∃ y ∈ L, ∀ z : ℂ,
      d₀ + z * d₁ = ((a : ℂ) + z) * x + ((b : ℂ) + z) * y := by
  obtain ⟨y, hy, hAy⟩ := hA
  obtain ⟨x, hx, hBx⟩ := hB
  have hneC : (b : ℂ) - (a : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (fun h => hne (Complex.ofReal_injective h.symm))
  have hsum : d₁ = x + y := by
    apply mul_right_cancel₀ hneC
    linear_combination hBx - hAy
  refine ⟨x, hx, y, hy, fun z => ?_⟩
  rw [hsum] at hAy ⊢
  linear_combination -hAy

end

end MOC
