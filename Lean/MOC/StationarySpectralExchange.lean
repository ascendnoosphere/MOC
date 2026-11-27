import MOC.StationaryPivot

/-! Exchange bounds for a determinant support maximum. The exchange sum
identity holds for every unitary mixer. The scalar pivot bounds use the
stationary disk or Laurent coefficient identities as explicit premises. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Swap the signed labels `a i` and `-b j` and evaluate the determinant
at the original mixer. -/
def oppositeExchangeDet (a b : ι → ℂ) (U : Matrix ι ι ℂ) (i j : ι) : ℂ :=
  determinantValue (Function.update a i (-b j)) (Function.update b j (-a i)) U

private theorem matchingProduct_oppositeExchange (a b : ι → ℂ) (σ : Equiv.Perm ι)
    (i j : ι) :
    matchingProduct (Function.update a i (-b j)) (Function.update b j (-a i)) σ +
      (if σ j = i then matchingProduct a b σ else 0) =
    matchingProduct a b σ - matchingProduct (a ∘ Equiv.swap i (σ j)) b σ := by
  let p (k : ι) := a (σ k) + b k
  let x (k : ι) := (Function.update a i (-b j)) (σ k) + (Function.update b j (-a i)) k
  let s (k : ι) := a (Equiv.swap i (σ j) (σ k)) + b k
  change (∏ k, x k) + (if σ j = i then ∏ k, p k else 0) = (∏ k, p k) - ∏ k, s k
  let S := (Finset.univ : Finset ι).erase j
  have hsplit (f : ι → ℂ) : (∏ k, f k) = f j * ∏ k ∈ S, f k :=
    (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j)).symm
  by_cases hj : σ j = i
  · have hs : s = p := by funext k; simp [s, p, hj]
    have hx : x j = -p j := by
      dsimp only [x, p]
      rw [hj, Function.update_self, Function.update_self]
      ring
    have hp : (∏ k ∈ S, x k) = ∏ k ∈ S, p k := by
      apply Finset.prod_congr rfl
      intro k hk
      have hkj := (Finset.mem_erase.mp hk).1
      have hki : σ k ≠ i := fun h => hkj (σ.injective (h.trans hj.symm))
      simp only [x, p, Function.update_of_ne hki, Function.update_of_ne hkj]
    rw [if_pos hj, hs, hsplit x, hsplit p, hx, hp]
    ring
  · let k := σ.symm i
    have hk : σ k = i := σ.apply_symm_apply i
    have hkj : k ≠ j := fun h => hj ((congrArg σ h).symm.trans hk)
    have hkS : k ∈ S := Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩
    have hsplit₂ (f : ι → ℂ) :
        (∏ l, f l) = f j * (f k * ∏ l ∈ S.erase k, f l) := by
      rw [hsplit f, ← Finset.mul_prod_erase S f hkS]
    have hxj : x j = a (σ j) - a i := by simp [x, hj, sub_eq_add_neg]
    have hxk : x k = b k - b j := by
      dsimp only [x]
      rw [hk, Function.update_self, Function.update_of_ne hkj]
      ring
    have hsj : s j = a i + b j := by simp [s, Equiv.swap_apply_right]
    have hsk : s k = a (σ j) + b k := by simp [s, hk, Equiv.swap_apply_left]
    have hout (l : ι) (hl : l ∈ S.erase k) : l ≠ j ∧ σ l ≠ i ∧ σ l ≠ σ j := by
      have hlk := (Finset.mem_erase.mp hl).1
      have hlj := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
      exact ⟨hlj, fun h => hlk (σ.injective (h.trans hk.symm)), σ.injective.ne hlj⟩
    have hxp : (∏ l ∈ S.erase k, x l) = ∏ l ∈ S.erase k, p l := by
      apply Finset.prod_congr rfl
      intro l hl
      obtain ⟨hlj, hli, _⟩ := hout l hl
      simp only [x, p, Function.update_of_ne hli, Function.update_of_ne hlj]
    have hsp : (∏ l ∈ S.erase k, s l) = ∏ l ∈ S.erase k, p l := by
      apply Finset.prod_congr rfl
      intro l hl
      obtain ⟨_, hli, hlj⟩ := hout l hl
      simp only [s, p, Equiv.swap_apply_of_ne_of_ne hli hlj]
    rw [if_neg hj, hsplit₂ x, hsplit₂ p, hsplit₂ s, hxj, hxk, hsj, hsk, hxp, hsp]
    simp only [p, hk]
    ring

/-- The total opposite-exchange expression equals the sum of support
losses over the ordered transpositions of the first spectrum. The equality
before projection is complex and includes zero entries of the mixer. -/
theorem sum_oppositeExchangeDet (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    (∑ i, ∑ j, ((Complex.normSq (U i j) : ℂ) * determinantValue a b U +
      oppositeExchangeDet a b U i j)) =
    ∑ i, ∑ k, (determinantValue a b U - determinantValue (a ∘ Equiv.swap i k) b U) := by
  let d := determinantValue a b U
  let p := matchingProduct a b
  let w := signedWeight U
  let x (i j : ι) (σ : Equiv.Perm ι) :=
    matchingProduct (Function.update a i (-b j)) (Function.update b j (-a i)) σ +
      if σ j = i then p σ else 0
  let s (i k : ι) (σ : Equiv.Perm ι) := p σ - matchingProduct (a ∘ Equiv.swap i k) b σ
  have eqx (j : ι) : (∑ i, ((Complex.normSq (U i j) : ℂ) * d + oppositeExchangeDet a b U i j)) =
      ∑ i, ∑ σ, w σ * x i j σ := by
    have hcross (i : ι) : oppositeExchangeDet a b U i j =
        ∑ σ, w σ * matchingProduct (Function.update a i (-b j))
          (Function.update b j (-a i)) σ := (signed_determinant _ _ U hU).symm
    have haux : (∑ i, (Complex.normSq (U i j) : ℂ) * d) =
        ∑ i, ∑ σ, w σ * (if σ j = i then p σ else 0) := by
      calc
        _ = ∑ i, marginal w i j * d := by simp only [w, marginal_signedWeight U hU]
        _ = ∑ σ, w σ * d := (sum_weighted_evaluation w j (fun _ => d)).symm
        _ = d := by rw [← Finset.sum_mul, show (∑ σ, w σ) = 1 from
          sum_signedWeight U (det_ne_zero_of_unitary hU), one_mul]
        _ = _ := by
          rw [Finset.sum_comm]
          simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, w, p, d,
            signed_determinant a b U hU]
    calc
      _ = (∑ i, oppositeExchangeDet a b U i j) + ∑ i, (Complex.normSq (U i j) : ℂ) * d := by
        rw [Finset.sum_add_distrib, add_comm]
      _ = _ := by simp only [hcross, haux, x, mul_add, Finset.sum_add_distrib]
  have eqs (i k : ι) : d - determinantValue (a ∘ Equiv.swap i k) b U =
      ∑ σ, w σ * s i k σ := by
    dsimp only [d]
    rw [← signed_determinant a b U hU, ← signed_determinant (a ∘ Equiv.swap i k) b U hU]
    simp only [w, s, p, mul_sub, Finset.sum_sub_distrib]
  have hxs (i : ι) (σ : Equiv.Perm ι) : (∑ j, x i j σ) = ∑ k, s i k σ := by
    have h (j : ι) : x i j σ = s i (σ j) σ := matchingProduct_oppositeExchange a b σ i j
    simp_rw [h]
    exact Equiv.sum_comp σ (fun k => s i k σ)
  calc
    _ = ∑ j, ∑ i, ((Complex.normSq (U i j) : ℂ) * d + oppositeExchangeDet a b U i j) :=
      Finset.sum_comm
    _ = ∑ j, ∑ i, ∑ σ, w σ * x i j σ := Finset.sum_congr rfl (fun j _ => eqx j)
    _ = ∑ i, ∑ j, ∑ σ, w σ * x i j σ := Finset.sum_comm
    _ = ∑ i, ∑ σ, ∑ j, w σ * x i j σ := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ i, ∑ σ, ∑ k, w σ * s i k σ := by simp only [← Finset.mul_sum, hxs]
    _ = ∑ i, ∑ k, ∑ σ, w σ * s i k σ := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := by simp only [← eqs, d]

/-- The opposite exchange of the stationary disk coefficients bounds the
original support excess. The pivot radius may be zero. -/
theorem oppositeExchange_lower_bound_of_stationaryDisk
    {r c κ ℓ D Dx H : ℝ} (hstationary : ℓ = κ * r)
    (hD : D = c + κ * r ^ 2 - 2 * ℓ * r)
    (hDx : Dx = -κ - c * r ^ 2 + 2 * ℓ * r)
    (hboundary : c + κ - 2 * ℓ ≤ H) :
    (1 + r) ^ 2 * (D - H) ≤ r ^ 2 * D + Dx := by
  have hexchange : r ^ 2 * D + Dx = -(1 - r ^ 2) ^ 2 * κ := by
    rw [hD, hDx, hstationary]
    ring
  have hloss : D - (c + κ - 2 * ℓ) = -(1 - r) ^ 2 * κ := by
    rw [hD, hstationary]
    ring
  calc
    _ ≤ (1 + r) ^ 2 * (D - (c + κ - 2 * ℓ)) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left hboundary D) (sq_nonneg _)
    _ = _ := by rw [hloss, hexchange]; ring

/-- The two unit-circle endpoint bounds control the stationary Laurent
coefficient and the excess at a positive interior pivot. -/
theorem stationary_laurent_pivot_bounds {r k β D lo hi : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hD : D = β + k * (r + 1 / r))
    (hhi : β + 2 * k ≤ hi) (hlo : lo ≤ β - 2 * k) (hexcess : hi < D) :
    0 < k ∧ D - hi ≤ k * ((1 - r) ^ 2 / r) ∧ 4 * k ≤ hi - lo := by
  have hdiff : D - (β + 2 * k) = k * ((1 - r) ^ 2 / r) := by
    rw [hD]
    field_simp [hr.ne'] <;> ring
  have hpos : 0 < (1 - r) ^ 2 / r := div_pos (pow_pos (sub_pos.mpr hr1) _) hr
  have hk : 0 < k := by
    by_contra! hn
    have hnonpos := mul_nonpos_of_nonpos_of_nonneg hn hpos.le
    linarith only [hdiff, hhi, hexcess, hnonpos]
  exact ⟨hk, by linarith only [hdiff, hhi], by linarith only [hhi, hlo]⟩

end

end MOC
