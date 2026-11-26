import MOC.RankTwoKernelInclusion
import MOC.Support
import MOC.TwoValues

/-! Exact projective compression for a spectrum with at most three values.
The final theorem is an equivalence of two tests. It does not prove the
rectangular convex-hull bound. -/

open BigOperators Matrix
open scoped Topology

namespace MOC

noncomputable section

variable {κ ν : Type*} [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]

/-- The retained labels have values `β` or `α` according to `s`.
The deleted labels have value `γ`. -/
def threeValuePoleSpectrum (s : κ → Bool) (α β γ : ℂ) : κ ⊕ ν → ℂ :=
  Sum.elim (fun i => if s i then β else α) (fun _ => γ)

/-- The three row types after sending `α`, `β`, and `γ` to `0`, `1`, and the pole. -/
def threeValuePoleKernel (s : κ → Bool) (z : κ ⊕ ν → ℂ) :
    Matrix (κ ⊕ ν) (κ ⊕ ν) ℂ :=
  Matrix.of fun i j => Sum.elim (fun k => (if s k then 1 else 0) + z j)
    (fun _ => 1) i

/-- The matching product has one factor for each retained label.
The factors for the deleted labels are one. -/
def threeValuePoleMatching (s : κ → Bool) (z : κ ⊕ ν → ℂ)
    (σ : Equiv.Perm (κ ⊕ ν)) : ℂ :=
  ∏ i : κ, ((if s i then 1 else 0) + z (σ.symm (.inl i)))

/-- A diagonal projection plus the compression of the transformed partner. -/
def threeValuePoleCompression (s : κ → Bool) (z : κ ⊕ ν → ℂ)
    (U : Matrix (κ ⊕ ν) (κ ⊕ ν) ℂ) : Matrix κ κ ℂ :=
  diagonal (fun i => if s i then 1 else 0) +
    U.submatrix Sum.inl id * diagonal z * (U.submatrix Sum.inl id)ᴴ

omit [DecidableEq κ] [DecidableEq ν] in
theorem threeValuePoleMatching_eq_kernel (s : κ → Bool) (z : κ ⊕ ν → ℂ)
    (σ : Equiv.Perm (κ ⊕ ν)) :
    threeValuePoleMatching s z σ = kernelMatchingProduct (threeValuePoleKernel s z) σ := by
  rw [kernelMatchingProduct, ← Equiv.prod_comp σ.symm
    (fun j => threeValuePoleKernel s z (σ j) j)]
  simp only [Equiv.apply_symm_apply, Fintype.prod_sum_type, threeValuePoleKernel,
    Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Finset.prod_const_one, mul_one,
    threeValuePoleMatching]

theorem threeValuePoleCompression_coisometry
    (U : Matrix (κ ⊕ ν) (κ ⊕ ν) ℂ) (hU : IsUnitary U) :
    U.submatrix Sum.inl id * (U.submatrix Sum.inl id)ᴴ = 1 := by
  rw [Matrix.conjTranspose_submatrix,
    ← Matrix.submatrix_mul U Uᴴ Sum.inl id Sum.inl Function.bijective_id,
    hU.1, Matrix.submatrix_one Sum.inl Sum.inl_injective]

theorem threeValuePoleCompression_eq_kernel (s : κ → Bool) (z : κ ⊕ ν → ℂ)
    (U : Matrix (κ ⊕ ν) (κ ⊕ ν) ℂ) (hU : IsUnitary U) :
    (threeValuePoleCompression s z U).det =
      kernelDeterminantValue (threeValuePoleKernel s z) U := by
  let W : Matrix (κ ⊕ ν) (κ ⊕ ν) ℂ :=
    Matrix.of fun i j => threeValuePoleKernel s z i j * U i j
  let N := U * diagonal z * Uᴴ
  have hN (i j : κ ⊕ ν) : N i j = ∑ k, z k * U i k * Uᴴ k j := by
    change ((U * diagonal z) * Uᴴ) i j = _
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hW (i j : κ ⊕ ν) : (W * Uᴴ) i j =
      Sum.elim (fun k => (if s k then 1 else 0) * (1 : Matrix (κ ⊕ ν) (κ ⊕ ν) ℂ) i j +
        N i j) (fun _ => (1 : Matrix (κ ⊕ ν) (κ ⊕ ν) ℂ) i j) i := by
    cases i with
    | inl i =>
      simp only [Matrix.mul_apply, W, Matrix.of_apply, threeValuePoleKernel, Sum.elim_inl,
        add_mul, mul_assoc, Finset.sum_add_distrib]
      rw [← Finset.mul_sum]
      have hunit := congrArg (fun A : Matrix (κ ⊕ ν) (κ ⊕ ν) ℂ => A (.inl i) j) hU.1
      change (∑ k, U (.inl i) k * Uᴴ k j) = _ at hunit
      rw [hunit, hN]
      simp only [mul_assoc]
    | inr i =>
      change (∑ k, 1 * U (.inr i) k * Uᴴ k j) = _
      simpa only [one_mul, Matrix.mul_apply] using
        congrArg (fun A : Matrix (κ ⊕ ν) (κ ⊕ ν) ℂ => A (.inr i) j) hU.1
  have hret : N.submatrix Sum.inl Sum.inl =
      U.submatrix Sum.inl id * diagonal z * (U.submatrix Sum.inl id)ᴴ := by
    rw [Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul (U * diagonal z) Uᴴ Sum.inl id Sum.inl Function.bijective_id,
      Matrix.submatrix_mul U (diagonal z) Sum.inl id id Function.bijective_id,
      Matrix.submatrix_id_id]
  have hblock : W * Uᴴ = Matrix.fromBlocks (threeValuePoleCompression s z U)
      (N.submatrix Sum.inl Sum.inr) 0 1 := by
    ext i j : 1
    rw [hW]
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simp only [Sum.elim_inl, Matrix.fromBlocks_apply₁₁, threeValuePoleCompression,
          Matrix.add_apply, ← hret, Matrix.submatrix_apply, Matrix.one_apply,
          Sum.inl.injEq, Matrix.diagonal_apply]
        by_cases hij : i = j <;> simp [hij]
      | inr j => simp [Matrix.one_apply]
    | inr i =>
      cases j <;> simp [Matrix.one_apply]
  have hd : (W * Uᴴ).det = (threeValuePoleCompression s z U).det := by
    rw [hblock, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
  have hunit : U.det * Uᴴ.det = 1 := by rw [← Matrix.det_mul, hU.1, Matrix.det_one]
  rw [← hd, Matrix.det_mul, kernelDeterminantValue]
  change W.det * Uᴴ.det = W.det / U.det
  have hstar : Uᴴ.det = 1 / U.det :=
    (eq_div_iff (det_ne_zero_of_unitary hU)).mpr (by simpa only [mul_comm] using hunit)
  rw [hstar]
  ring

omit [DecidableEq κ] [DecidableEq ν] in
theorem threeValuePoleMatching_transport (s : κ → Bool) (b : κ ⊕ ν → ℂ)
    (α β γ : ℂ) (hαβ : α ≠ β)
    (hb : ∀ j, b j + γ ≠ 0) (σ : Equiv.Perm (κ ⊕ ν)) :
    let h := (β - γ) / (β - α)
    let z := fun j => -h * (b j + α) / (b j + γ)
    let c : κ ⊕ ν → ℂ := Sum.elim (fun i => if s i then 1 - h else -h) (fun _ => 1)
    threeValuePoleMatching s z σ =
      ((∏ i, c i) / ∏ j, (b j + γ)) * matchingProduct (threeValuePoleSpectrum s α β γ) b σ := by
  dsimp only
  let h := (β - γ) / (β - α)
  let c : κ ⊕ ν → ℂ := Sum.elim (fun i => if s i then 1 - h else -h) (fun _ => 1)
  let a : κ ⊕ ν → ℂ := threeValuePoleSpectrum s α β γ
  let z := fun j => -h * (b j + α) / (b j + γ)
  have hterm (i : κ ⊕ ν) :
      Sum.elim (fun k => (if s k then 1 else 0) + z (σ.symm i)) (fun _ => 1) i =
      c i * (a i + b (σ.symm i)) / (b (σ.symm i) + γ) := by
    cases i with
    | inl i =>
      cases hi : s i <;>
        simp only [Sum.elim_inl, hi, Bool.false_eq_true, if_false, if_true, zero_add,
          z, c, a, threeValuePoleSpectrum]
      · ring
      · dsimp only [h]
        field_simp [hb (σ.symm (.inl i)), sub_ne_zero.mpr hαβ.symm]
        ring
    | inr i =>
      simp only [Sum.elim_inr, c, a, threeValuePoleSpectrum, one_mul]
      rw [add_comm γ, div_self (hb _)]
  have hprod := congrArg (fun f : κ ⊕ ν → ℂ => ∏ i, f i) (funext hterm)
  dsimp only at hprod
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib] at hprod
  have hleft : (∏ i, Sum.elim
      (fun k => (if s k then 1 else 0) + z (σ.symm i)) (fun _ => (1 : ℂ)) i) =
      threeValuePoleMatching s z σ := by
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.prod_const_one, mul_one, threeValuePoleMatching]
  change threeValuePoleMatching s z σ = ((∏ i, c i) / ∏ j, (b j + γ)) * matchingProduct a b σ
  rw [hleft, Equiv.prod_comp σ.symm (fun j => b j + γ),
    ← matchingProduct_inverse a b σ.symm] at hprod
  simpa only [Equiv.symm_symm, div_mul_eq_mul_div] using hprod

theorem threeValuePoleCompression_transport (s : κ → Bool) (b : κ ⊕ ν → ℂ)
    (U : Matrix (κ ⊕ ν) (κ ⊕ ν) ℂ) (hU : IsUnitary U)
    (α β γ : ℂ) (hαβ : α ≠ β) (hb : ∀ j, b j + γ ≠ 0) :
    let h := (β - γ) / (β - α)
    let z := fun j => -h * (b j + α) / (b j + γ)
    let c : κ ⊕ ν → ℂ := Sum.elim (fun i => if s i then 1 - h else -h) (fun _ => 1)
    (threeValuePoleCompression s z U).det =
      ((∏ i, c i) / ∏ j, (b j + γ)) * determinantValue (threeValuePoleSpectrum s α β γ) b U := by
  dsimp only
  rw [threeValuePoleCompression_eq_kernel s _ U hU,
    kernelDeterminantValue_eq_sum_signed, ← signed_determinant _ _ U hU, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← threeValuePoleMatching_eq_kernel,
    threeValuePoleMatching_transport s b α β γ hαβ hb σ]
  ring

theorem holds_threeValue_iff_poleCompression (s : κ → Bool) (b : κ ⊕ ν → ℂ)
    (U : Matrix (κ ⊕ ν) (κ ⊕ ν) ℂ) (hU : IsUnitary U)
    (α β γ : ℂ) (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hb : ∀ j, b j + γ ≠ 0) :
    let h := (β - γ) / (β - α)
    let z := fun j => -h * (b j + α) / (b j + γ)
    Holds (threeValuePoleSpectrum s α β γ) b U ↔
      (threeValuePoleCompression s z U).det ∈
        convexHull ℝ (Set.range (threeValuePoleMatching s z)) := by
  dsimp only
  let h := (β - γ) / (β - α)
  let c : κ ⊕ ν → ℂ := Sum.elim (fun i => if s i then 1 - h else -h) (fun _ => 1)
  have hden : β - α ≠ 0 := sub_ne_zero.mpr hαβ.symm
  have hh : h ≠ 0 := div_ne_zero (sub_ne_zero.mpr hβγ) hden
  have hone : 1 - h ≠ 0 := by
    intro hz
    have he : (β - γ) / (β - α) = 1 := (sub_eq_zero.mp hz).symm
    have he' := (div_eq_iff hden).mp he
    apply hαγ
    linear_combination he'
  have hc (i : κ ⊕ ν) : c i ≠ 0 := by
    cases i with
    | inl i =>
      cases hi : s i <;> simp only [c, Sum.elim_inl, hi, Bool.false_eq_true, if_false, if_true]
      · exact neg_ne_zero.mpr hh
      · exact hone
    | inr i => exact one_ne_zero
  have hscale : (∏ i, c i) / ∏ j, (b j + γ) ≠ 0 :=
    div_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hc i)
      (Finset.prod_ne_zero_iff.mpr fun j _ => hb j)
  exact (hull_common_factor_iff hscale
    (threeValuePoleCompression_transport s b U hU α β γ hαβ hb)
    (threeValuePoleMatching_transport s b α β γ hαβ hb)).symm

private theorem isClosed_finite_hull_test {T J : Type*} [TopologicalSpace T]
    [Fintype J] [Nonempty J] (d : T → ℂ) (p : T → J → ℂ)
    (hd : Continuous d) (hp : ∀ j, Continuous fun t => p t j) :
    IsClosed {t | d t ∈ convexHull ℝ (Set.range (p t))} := by
  classical
  have he : {t | d t ∈ convexHull ℝ (Set.range (p t))} =
      ⋂ η : ℂ, ⋃ j : J, {t | (η * d t).re ≤ (η * p t j).re} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro h η
      obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ
        (fun j => (η * p t j).re) Finset.univ_nonempty
      refine ⟨j, ?_⟩
      let f : ℂ →ₗ[ℝ] ℝ := Complex.reLm.comp (LinearMap.mulLeft ℝ η)
      apply convexHull_min (t := {z | f z ≤ f (p t j)}) ?_
        (convex_halfSpace_le f.isLinear _) h
      rintro _ ⟨k, rfl⟩
      exact hj k (Finset.mem_univ k)
    · exact mem_hull_of_directional_bound (p t) (d t)
  rw [he]
  exact isClosed_iInter fun η => isClosed_iUnion_of_finite fun j =>
    isClosed_le (Complex.continuous_re.comp (continuous_const.mul hd))
      (Complex.continuous_re.comp (continuous_const.mul (hp j)))

private theorem mem_closed_partner_test {J : Type*} [Fintype J]
    (S : Set (J → ℂ)) (hS : IsClosed S) (b : J → ℂ) (c : ℂ)
    (h : ∀ x : J → ℂ, (∀ j, x j ≠ c) → x ∈ S) : b ∈ S := by
  let B (t : ℂ) (j : J) := b j + t
  have hB : Continuous B := continuous_pi fun j => by
    dsimp only [B]
    fun_prop
  have hlim : Filter.Tendsto B (𝓝[≠] (0 : ℂ)) (𝓝 b) := by
    have hz : B 0 = b := funext fun j => add_zero (b j)
    rw [← hz]
    exact hB.continuousAt.continuousWithinAt
  have hreg : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ∀ j, B t j ≠ c := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : b j = c
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change b j + t ≠ c
      rw [hj]
      exact fun he => ht (add_left_cancel (he.trans (add_zero c).symm))
    · have hc : Continuous fun t : ℂ => B t j := by
        dsimp only [B]
        fun_prop
      exact (hc.continuousAt.eventually_ne (by simpa only [B, add_zero] using hj)).filter_mono
        nhdsWithin_le_nhds
  exact hS.mem_of_tendsto hlim (hreg.mono fun t ht => h (B t) ht)

/-- The three-value inclusion for this partition and mixer is equivalent to
the rectangular two-level bound. Neither test restricts the partner list. -/
theorem three_value_test_iff_pole_compression_test (s : κ → Bool)
    (U : Matrix (κ ⊕ ν) (κ ⊕ ν) ℂ) (hU : IsUnitary U) :
    (∀ (α β γ : ℂ) (b : κ ⊕ ν → ℂ),
      Holds (threeValuePoleSpectrum s α β γ) b U) ↔
    ∀ z : κ ⊕ ν → ℂ, (threeValuePoleCompression s z U).det ∈
      convexHull ℝ (Set.range (threeValuePoleMatching s z)) := by
  constructor
  · intro h z
    let S := {z : κ ⊕ ν → ℂ | (threeValuePoleCompression s z U).det ∈
      convexHull ℝ (Set.range (threeValuePoleMatching s z))}
    have hS : IsClosed S := by
      apply isClosed_finite_hull_test
      · unfold threeValuePoleCompression
        fun_prop
      · intro σ
        unfold threeValuePoleMatching
        apply continuous_finset_prod
        intro i _
        fun_prop
    apply mem_closed_partner_test S hS z 1
    intro x hx
    let b (j : κ ⊕ ν) := 2 * x j / (1 - x j)
    have hb (j : κ ⊕ ν) : b j + 2 ≠ 0 := by
      have hj : 1 - x j ≠ 0 := sub_ne_zero.mpr (hx j).symm
      have he : b j + 2 = 2 / (1 - x j) := by
        dsimp only [b]
        field_simp [hj]
        ring
      rw [he]
      exact div_ne_zero (by norm_num) hj
    have he (j : κ ⊕ ν) : -((1 - 2) / (1 - 0) : ℂ) * (b j + 0) / (b j + 2) = x j := by
      have hj : 1 - x j ≠ 0 := sub_ne_zero.mpr (hx j).symm
      norm_num only [sub_zero, add_zero, div_one] at ⊢
      dsimp only [b]
      field_simp [hj, hb j]
      ring
    have hh := (holds_threeValue_iff_poleCompression s b U hU 0 1 2
      (by norm_num) (by norm_num) (by norm_num) hb).mp
        (h 0 1 2 b)
    rw [show (fun j => -((1 - 2) / (1 - 0)) * (b j + 0) / (b j + 2)) = x from funext he] at hh
    exact hh
  · intro h α β γ b
    by_cases hαβ : α = β
    · apply holds_of_two_values_left _ b U hU α γ
      rintro (i | i)
      · cases hi : s i <;> simp [threeValuePoleSpectrum, hi, hαβ]
      · exact Or.inr rfl
    by_cases hαγ : α = γ
    · apply holds_of_two_values_left _ b U hU α β
      rintro (i | i)
      · cases hi : s i <;> simp [threeValuePoleSpectrum, hi]
      · exact Or.inl hαγ.symm
    by_cases hβγ : β = γ
    · apply holds_of_two_values_left _ b U hU α β
      rintro (i | i)
      · cases hi : s i <;> simp [threeValuePoleSpectrum, hi]
      · exact Or.inr hβγ.symm
    let a : κ ⊕ ν → ℂ := threeValuePoleSpectrum s α β γ
    have hc : IsClosed {b : κ ⊕ ν → ℂ | Holds a b U} := by
      apply isClosed_finite_hull_test
      · unfold determinantValue
        fun_prop
      · intro σ
        unfold matchingProduct
        apply continuous_finset_prod
        intro j _
        fun_prop
    apply mem_closed_partner_test _ hc b (-γ)
    intro x hx
    have hb (j : κ ⊕ ν) : x j + γ ≠ 0 := by
      exact fun he => hx j (eq_neg_of_add_eq_zero_left he)
    exact (holds_threeValue_iff_poleCompression s x U hU α β γ hαβ hαγ hβγ hb).mpr (h _)

end

end MOC
