import MOC.HermitianByNormal
import MOC.SupportedCompressionReduction
import Mathlib.Tactic.FunProp

/-! A real pole in the partner reduces the order. The real-pivot reduction
preserves the number of nonreal labels, as in Shitov, *A further sufficient condition for the determinantal
conjecture*, DOI: 10.4213/im9292e. -/

open Matrix Filter
open scoped Topology

namespace MOC

/-- The number of nonreal entries of an enumerated spectrum, with multiplicity. -/
noncomputable def nonrealCount {ι : Type*} [Fintype ι] (b : ι → ℂ) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => (b i).im ≠ 0).card

/-- The Hermitian-by-normal inclusion with a bound on the partner's nonreal labels. -/
def HermitianByNormalAtMost (ι : Type*) [Fintype ι] [DecidableEq ι] (k : ℕ) : Prop :=
  ∀ (a : ι → ℝ) (b : ι → ℂ) (U : Matrix ι ι ℂ), IsUnitary U →
    nonrealCount b ≤ k → Holds (fun i => (a i : ℂ)) b U

private theorem nonrealCount_le_card {ι : Type*} [Fintype ι] (b : ι → ℂ) :
    nonrealCount b ≤ Fintype.card ι := by
  classical
  simpa only [nonrealCount] using
    (Finset.card_filter_le (s := (Finset.univ : Finset ι)) fun i => (b i).im ≠ 0)

/-- Shifting by a real number and inverting preserves real and nonreal labels. -/
theorem inv_sub_real_im_eq_zero_iff (z : ℂ) (r : ℝ) :
    ((z - (r : ℂ))⁻¹).im = 0 ↔ z.im = 0 := by
  rw [Complex.inv_im, Complex.sub_im, Complex.ofReal_im, sub_zero, div_eq_zero_iff,
    neg_eq_zero, Complex.normSq_eq_zero]
  exact or_iff_left_of_imp fun h => by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] using
      congrArg Complex.im h

private theorem nonrealCount_pole {n : ℕ} (b : Fin (n + 1) → ℂ) (p : Fin (n + 1))
    (hp : (b p).im = 0) (r : ℝ) :
    nonrealCount (fun i => (b (p.succAbove i) - (r : ℂ))⁻¹) = nonrealCount b := by
  classical
  unfold nonrealCount
  rw [← Finset.card_map p.succAboveEmb]
  congr 1
  ext j
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.coe_succAboveEmb]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact (not_congr (inv_sub_real_im_eq_zero_iff _ r)).mp hi
  · intro hj
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq (show j ≠ p by
      intro h
      exact hj (h.symm ▸ hp))
    exact ⟨i, (not_congr (inv_sub_real_im_eq_zero_iff _ r)).mpr hj, rfl⟩

private theorem holds_of_regular_real_pivot {n : ℕ}
    (a : Fin (n + 1) → ℝ) (b : Fin (n + 1) → ℂ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hU : IsUnitary U) (p : Fin (n + 1)) (hp : (b p).im = 0)
    (ha : Function.Injective a) (hbp : ∀ i ≠ p, b i - b p ≠ 0)
    (hab : ∀ i, (a i : ℂ) + b p ≠ 0)
    (hSmall : ∀ (a' : Fin n → ℝ) (V : Matrix (Fin n) (Fin n) ℂ), IsUnitary V →
      Holds (fun i => (a' i : ℂ)) (fun i => (b (p.succAbove i) - b p)⁻¹) V) :
    Holds (fun i => (a i : ℂ)) b U := by
  let A : Fin (n + 1) → ℂ := fun i => a i
  let α : Fin n → ℂ := fun i => (b (p.succAbove i) - b p)⁻¹
  let β : Fin (n + 1) → ℂ := fun i => (A i + b p)⁻¹
  let V := Uᴴ
  let C := (V * diagonal β * Vᴴ).submatrix p.succAbove p.succAbove
  have hV : IsUnitary V := ⟨by simpa [V] using hU.2, by simpa [V] using hU.1⟩
  have hreal : ((b p).re : ℂ) = b p := Complex.ext rfl (by simpa only [Complex.ofReal_im] using hp.symm)
  have hβreal : β = fun i => (((a i + (b p).re)⁻¹ : ℝ) : ℂ) := by
    funext i
    simp [β, A, Complex.ofReal_inv, Complex.ofReal_add, hreal]
  have hβinj : Function.Injective β := by
    intro i j h
    exact ha (Complex.ofReal_injective (add_right_cancel (inv_injective h)))
  have hC : C.IsHermitian := by
    change ((V * diagonal β * Vᴴ).submatrix p.succAbove p.succAbove).IsHermitian
    apply Matrix.IsHermitian.submatrix
    apply Matrix.isHermitian_mul_mul_conjTranspose
    rw [hβreal]
    exact Matrix.isHermitian_diagonal_iff.mpr (fun i => by
      simp [isSelfAdjoint_iff, Complex.star_def])
  have hCnormal : IsStarNormal C := ⟨by
    show Cᴴ * C = C * Cᴴ
    rw [hC.eq]⟩
  obtain ⟨c, hc, hsub⟩ :=
    exists_compression_spectrum_with_matchingHull_subset α β V hV p hβinj.injOn hCnormal
  let W : Matrix (Fin n) (Fin n) ℂ := hC.eigenvectorUnitary
  let lam : Fin n → ℝ := hC.eigenvalues
  have hW : IsUnitary W :=
    ⟨Matrix.mem_unitaryGroup_iff.mp hC.eigenvectorUnitary.2,
      Matrix.mem_unitaryGroup_iff'.mp hC.eigenvectorUnitary.2⟩
  have hspec : C = W * diagonal (fun j => (lam j : ℂ)) * Wᴴ := by
    simpa only [W, lam, Function.comp_apply, Matrix.star_eq_conjTranspose] using hC.spectral_theorem
  have hroots : (Finset.univ : Finset (Fin n)).val.map c =
      (Finset.univ : Finset (Fin n)).val.map (fun j => (lam j : ℂ)) := by
    rw [← hc]
    change C.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map (fun j => (lam j : ℂ))
    rw [hspec, roots_unitary_diagonalization _ hW]
  obtain ⟨e, he⟩ := exists_perm_of_equal_multisets _ _ hroots
  have hW' : IsUnitary Wᴴ := ⟨by simpa using hW.2, by simpa using hW.1⟩
  have hsmall : Holds α (fun j => (lam j : ℂ)) W :=
    (holds_swap_iff α (fun j => (lam j : ℂ)) hW).mp (hSmall lam Wᴴ hW')
  have hdet : (diagonal α + C).det ∈ convexHull ℝ (Set.range (rectangularMatchingProduct α β)) := by
    apply hsub
    have hrange : Set.range (matchingProduct α c) =
        Set.range (matchingProduct α (fun j => (lam j : ℂ))) := by
      rw [he]
      exact matchingRange_relabel α _ (Equiv.refl _) e
    rw [hspec, hrange]
    exact hsmall
  rw [← rectangular_matching_range α β p] at hdet
  exact (holds_swap_iff A b hU).mp
    ((holds_iff_poleCompression b A V hV p hbp hab).mpr hdet)

private theorem eventually_affine_ne_zero (c d : ℂ) (hd : d ≠ 0) :
    ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), c + (t : ℂ) * d ≠ 0 := by
  by_cases hc : c = 0
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simpa only [hc, zero_add] using mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) hd
  · have hcont : Continuous (fun t : ℝ => c + (t : ℂ) * d) := by fun_prop
    exact (hcont.continuousAt.eventually_ne (by simpa using hc)).filter_mono nhdsWithin_le_nhds

/-- A real partner label reduces the problem to reciprocal real translates
of the remaining partner labels. -/
theorem holds_of_real_pivot_of_transformed_partner {n : ℕ}
    (a : Fin (n + 1) → ℝ) (b : Fin (n + 1) → ℂ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hU : IsUnitary U) (p : Fin (n + 1)) (hp : (b p).im = 0)
    (hSmall : ∀ (r : ℝ) (a' : Fin n → ℝ) (V : Matrix (Fin n) (Fin n) ℂ), IsUnitary V →
      Holds (fun i => (a' i : ℂ)) (fun i => (b (p.succAbove i) - (r : ℂ))⁻¹) V) :
    Holds (fun i => (a i : ℂ)) b U := by
  let ar (t : ℝ) (i : Fin (n + 1)) := a i + t * (i.val : ℝ)
  let ac (t : ℝ) (i : Fin (n + 1)) := (ar t i : ℂ)
  let bp (t : ℝ) := Function.update b p (b p + (t : ℂ))
  have hbp_at (t : ℝ) : bp t p = b p + (t : ℂ) := Function.update_self p _ _
  have hreal : ((b p).re : ℂ) = b p :=
    Complex.ext rfl (by simpa only [Complex.ofReal_im] using hp.symm)
  have hbp_real (t : ℝ) : (((b p).re + t : ℝ) : ℂ) = bp t p := by
    rw [Complex.ofReal_add, hreal, hbp_at]
  have hac₀ : ac 0 = fun i => (a i : ℂ) := by ext i; simp [ac, ar]
  have hbp₀ : bp 0 = b := by simp [bp, Function.update_eq_self]
  have hregA : ∀ᶠ t in 𝓝[≠] (0 : ℝ), Function.Injective (ar t) := by
    change ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ i j : Fin (n + 1), ar t i = ar t j → i = j
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ _ => hij
    have hd : (i.val : ℂ) - (j.val : ℂ) ≠ 0 := by
      intro hz
      exact hij (Fin.ext (Nat.cast_injective (sub_eq_zero.mp hz)))
    filter_upwards [eventually_affine_ne_zero ((a i : ℂ) - (a j : ℂ)) _ hd] with t hne he
    exfalso
    apply hne
    have he' := congrArg Complex.ofReal he
    simp only [ar, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_natCast] at he'
    linear_combination he'
  have hregB : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ i ≠ p, bp t i - bp t p ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : i = p
    · exact Eventually.of_forall fun _ h => (h hi).elim
    filter_upwards [eventually_affine_ne_zero (b i - b p) (-1) (by norm_num)] with t ht _
    convert ht using 1
    simp only [bp, Function.update_of_ne hi, Function.update_self]
    ring
  have hregAB : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ i, ac t i + bp t p ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro i
    have hd : (i.val : ℂ) + 1 ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re, Complex.zero_re] at hre
      have hnonneg : 0 ≤ (i.val : ℝ) := by positivity
      linarith
    filter_upwards [eventually_affine_ne_zero ((a i : ℂ) + b p) _ hd] with t ht
    convert ht using 1
    simp only [ac, ar, hbp_at, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_natCast]
    ring
  have hholds : ∀ᶠ t in 𝓝[≠] (0 : ℝ), Holds (ac t) (bp t) U := by
    filter_upwards [hregA, hregB, hregAB] with t htA htB htAB
    apply holds_of_regular_real_pivot (ar t) (bp t) U hU p
      (by rw [← hbp_real, Complex.ofReal_im]) htA htB htAB
    intro a' V hV
    have hb (i : Fin n) : bp t (p.succAbove i) = b (p.succAbove i) :=
      Function.update_of_ne (Fin.succAbove_ne p i) _ _
    simpa only [hb, hbp_real] using hSmall ((b p).re + t) a' V hV
  by_contra hbad
  rw [holds_iff_directional, not_forall] at hbad
  obtain ⟨z, hz⟩ := hbad
  push_neg at hz
  have hca : Continuous ac := continuous_pi fun i => by dsimp [ac, ar]; fun_prop
  have hcb : Continuous bp := continuous_pi fun i => by
    by_cases hi : i = p
    · subst i
      simp_rw [hbp_at]
      fun_prop
    · simpa [bp, Function.update_of_ne hi] using (continuous_const : Continuous (fun _ : ℝ => b i))
  have hd : Continuous (fun t => (z * determinantValue (ac t) (bp t) U).re) := by
    unfold determinantValue
    fun_prop
  have hm (σ : Equiv.Perm (Fin (n + 1))) :
      Continuous (fun t => (z * matchingProduct (ac t) (bp t) σ).re) := by
    have hprod : Continuous (fun t => matchingProduct (ac t) (bp t) σ) := by
      unfold matchingProduct
      apply continuous_finset_prod
      intro i _
      fun_prop
    fun_prop
  have hsep : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ σ : Equiv.Perm (Fin (n + 1)),
      (z * matchingProduct (ac t) (bp t) σ).re < (z * determinantValue (ac t) (bp t) U).re := by
    apply Filter.eventually_all.mpr
    intro σ
    exact ((hm σ).continuousAt.eventually_lt hd.continuousAt
      (by simpa only [hac₀, hbp₀] using hz σ)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, hts, hth⟩ := (hsep.and hholds).exists
  obtain ⟨σ, hσ⟩ := (holds_iff_directional _ _ _).mp hth z
  exact (not_le_of_gt (hts σ)) hσ

/-- A real partner label reduces the problem with at most `k` nonreal labels
by one order. -/
theorem holds_of_real_pivot {n k : ℕ} (hSmall : HermitianByNormalAtMost (Fin n) k)
    (a : Fin (n + 1) → ℝ) (b : Fin (n + 1) → ℂ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hU : IsUnitary U) (hcount : nonrealCount b ≤ k) (p : Fin (n + 1)) (hp : (b p).im = 0) :
    Holds (fun i => (a i : ℂ)) b U := by
  apply holds_of_real_pivot_of_transformed_partner a b U hU p hp
  intro r a' V hV
  exact hSmall a' _ V hV (by rwa [nonrealCount_pole b p hp r])

/-- The all-orders assertion with at most `k` nonreal partner labels is
equivalent to the Hermitian-by-normal conjectures through order `k`. -/
theorem hermitianByNormalAtMost_iff_orders_le (k : ℕ) :
    (∀ n : ℕ, HermitianByNormalAtMost (Fin n) k) ↔
      ∀ n : ℕ, n ≤ k → HermitianByNormal (Fin n) := by
  constructor
  · intro h n hn a b U hU
    exact h n a b U hU ((nonrealCount_le_card b).trans (by simpa using hn))
  · intro h n
    induction n with
    | zero =>
      intro a b U hU _
      exact h 0 (Nat.zero_le _) a b U hU
    | succ n ih =>
      intro a b U hU hcount
      by_cases hn : n + 1 ≤ k
      · exact h (n + 1) hn a b U hU
      have hex : ∃ p, (b p).im = 0 := by
        by_contra! hnone
        have he : nonrealCount b = n + 1 := by simp [nonrealCount, hnone]
        exact hn (he ▸ hcount)
      obtain ⟨p, hp⟩ := hex
      exact holds_of_real_pivot ih a b U hU hcount p hp

/-- Shitov's three-nonreal-eigenvalue theorem in the spectral formulation. -/
theorem hermitianByNormalAtMost_three (n : ℕ) : HermitianByNormalAtMost (Fin n) 3 :=
  (hermitianByNormalAtMost_iff_orders_le 3).mpr
    (fun m hm a b U hU => conjecture_le_three hm _ b U hU) n

/-- The five-nonreal-eigenvalue assertion reduces exactly to orders four and five. -/
theorem hermitianByNormalAtMost_five_iff :
    (∀ n : ℕ, HermitianByNormalAtMost (Fin n) 5) ↔
      HermitianByNormal (Fin 4) ∧ HermitianByNormal (Fin 5) := by
  rw [hermitianByNormalAtMost_iff_orders_le]
  constructor
  · intro h
    exact ⟨h 4 (by decide), h 5 le_rfl⟩
  · rintro ⟨hfour, hfive⟩ n hn
    by_cases h : n ≤ 3
    · exact fun a b U hU => conjecture_le_three h _ b U hU
    have hn' : n = 4 ∨ n = 5 := by omega
    rcases hn' with rfl | rfl
    · exact hfour
    · exact hfive

/-- In the all-orders problem, orders above three with an entirely nonreal
partner spectrum suffice. A real entry permits induction on the order. -/
theorem hermitianByNormal_iff_nonreal_partners :
    (∀ n : ℕ, HermitianByNormal (Fin n)) ↔
      ∀ (n : ℕ), 4 ≤ n →
        ∀ (a : Fin n → ℝ) (b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
          IsUnitary U → (∀ i, (b i).im ≠ 0) → Holds (fun i => (a i : ℂ)) b U := by
  constructor
  · intro h n _ a b U hU _
    exact h n a b U hU
  · intro h n
    induction n with
    | zero =>
      exact fun a b U hU => conjecture_zero (fun i => (a i : ℂ)) b U hU
    | succ n ih =>
      intro a b U hU
      by_cases hn : 4 ≤ n + 1
      · by_cases hb : ∀ i, (b i).im ≠ 0
        · exact h (n + 1) hn a b U hU hb
        · push_neg at hb
          obtain ⟨p, hp⟩ := hb
          exact holds_of_real_pivot (k := n + 1) (fun a' b' V hV _ => ih a' b' V hV)
            a b U hU (by simpa using nonrealCount_le_card b) p hp
      · have hsmall : n + 1 ≤ 3 := Nat.le_of_lt_succ (Nat.lt_of_not_ge hn)
        exact conjecture_le_three hsmall (fun i => (a i : ℂ)) b U hU

end MOC
