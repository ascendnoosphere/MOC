import MOC.ExtendedCases
import MOC.CommonWeights

/-! Exact interpolation across a two-port gate between two unitary blocks.
The normalized signed-weight convention is that of Merikoski–Virtanen
(DOI: 10.1016/0024-3795(89)90709-X). -/

open BigOperators Matrix Finset

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def bridgeRows (U : Matrix ι ι ℂ) (p q : ι) (c s : ℂ) : Matrix ι ι ℂ :=
  fun i j => if i = p then c * U p j + s * U q j else
    if i = q then -star s * U p j + star c * U q j else U i j

private theorem peel_prod (f : ι → ℂ) {x y : ι} (hxy : y ≠ x) :
    (∏ j, f j) = f x * f y * ∏ j ∈ (univ.erase x).erase y, f j := by
  rw [← Finset.mul_prod_erase _ f (Finset.mem_univ x),
    ← Finset.mul_prod_erase _ f (Finset.mem_erase.mpr ⟨hxy, Finset.mem_univ y⟩),
    mul_assoc]

private theorem peel_sum (f : ι → ℕ) {x y : ι} (hxy : y ≠ x) :
    (∑ j, f j) = f x + f y + ∑ j ∈ (univ.erase x).erase y, f j := by
  rw [← Finset.add_sum_erase _ f (Finset.mem_univ x),
    ← Finset.add_sum_erase _ f (Finset.mem_erase.mpr ⟨hxy, Finset.mem_univ y⟩),
    add_assoc]

private theorem bridge_ports_balance (side : ι → Bool) (σ : Equiv.Perm ι) {x y : ι}
    (hxy : y ≠ x) (hports : side (σ x) ≠ side (σ y))
    (h : ∀ j, j ≠ x → j ≠ y → side (σ j) = side j) :
    (side x = side (σ x) ∧ side y = side (σ y)) ∨
      (side x = side (σ y) ∧ side y = side (σ x)) := by
  let f (j : ι) : ℕ := if side j then 1 else 0
  have hs : (∑ j, (f ∘ σ) j) = ∑ j, f j := Equiv.sum_comp σ f
  rw [peel_sum (f ∘ σ) hxy, peel_sum f hxy] at hs
  have hr : ∑ j ∈ (univ.erase x).erase y, (f ∘ σ) j =
      ∑ j ∈ (univ.erase x).erase y, f j := by
    apply sum_congr rfl
    intro j hj
    rw [mem_erase, mem_erase] at hj
    simp only [Function.comp_apply, f, h j hj.2.1 hj.1]
  rw [hr] at hs
  have he : (f ∘ σ) x + (f ∘ σ) y = f x + f y := Nat.add_right_cancel hs
  simp only [Function.comp_apply, f] at he
  cases hx : side x <;> cases hy : side y <;>
    cases hx' : side (σ x) <;> cases hy' : side (σ y) <;>
      simp_all

/-- The two-port gate mixes whole signed weight arrays, not just spectral
objectives or one choice of minors. -/
theorem bridge_leibnizTerm (U : Matrix ι ι ℂ) (side : ι → Bool)
    (hblock : ∀ i j, side i ≠ side j → U i j = 0) {p q : ι}
    (hpq : side p ≠ side q) (c s : ℂ) (σ : Equiv.Perm ι) :
    leibnizTerm (bridgeRows U p q c s) σ =
      (Complex.normSq c : ℂ) * leibnizTerm U σ +
      (Complex.normSq s : ℂ) * leibnizTerm U (Equiv.swap p q * σ) := by
  let τ := Equiv.swap p q
  let x := σ.symm p
  let y := σ.symm q
  have hpq' : p ≠ q := fun h => hpq (congrArg side h)
  have hx : σ x = p := σ.apply_symm_apply p
  have hy : σ y = q := σ.apply_symm_apply q
  have hxy : y ≠ x := fun h => hpq' (by simpa only [hx,hy] using congrArg σ h.symm)
  have hn (j : ι) (hjx : j ≠ x) (hjy : j ≠ y) : σ j ≠ p ∧ σ j ≠ q :=
    ⟨fun he => hjx (σ.injective (he.trans hx.symm)),
      fun he => hjy (σ.injective (he.trans hy.symm))⟩
  have hτx : (τ * σ) x = q := by simp [τ,Equiv.Perm.mul_apply,hx]
  have hτy : (τ * σ) y = p := by simp [τ,Equiv.Perm.mul_apply,hy]
  have hτn (j : ι) (hjx : j ≠ x) (hjy : j ≠ y) : (τ * σ) j = σ j := by
    exact Equiv.swap_apply_of_ne_of_ne (hn j hjx hjy).1 (hn j hjx hjy).2
  have hsgn :
      ((Equiv.Perm.sign (τ * σ) : ℤ) : ℂ) = -((Equiv.Perm.sign σ : ℤ) : ℂ) := by
    simp [τ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hpq']
  let P := ∏ j ∈ (univ.erase x).erase y, U (σ j) j
  have hP₁ : ∏ j ∈ (univ.erase x).erase y, bridgeRows U p q c s (σ j) j = P := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [mem_erase, mem_erase] at hj
    simp [bridgeRows, (hn j hj.2.1 hj.1).1, (hn j hj.2.1 hj.1).2]
  have hP₂ : ∏ j ∈ (univ.erase x).erase y, U ((τ * σ) j) j = P := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [mem_erase, mem_erase] at hj
    rw [hτn j hj.2.1 hj.1]
  change leibnizTerm _ σ = _ * leibnizTerm U σ + _ * leibnizTerm U (τ * σ)
  simp only [leibnizTerm, peel_prod _ hxy, hsgn, hP₁, hP₂, hx, hy, hτx, hτy]
  by_cases h : ∀ j, j ≠ x → j ≠ y → side (σ j) = side j
  · rcases bridge_ports_balance side σ hxy (by simpa [hx,hy] using hpq) h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · rw [hx] at h₁; rw [hy] at h₂
      have h₃ := hblock q x (fun he => hpq (h₁.symm.trans he.symm))
      have h₄ := hblock p y (fun he => hpq (he.trans h₂))
      simp [bridgeRows, hpq', Ne.symm hpq', h₃,h₄,P, Complex.normSq_eq_conj_mul_self]
      ring
    · rw [hy] at h₁; rw [hx] at h₂
      have h₃ := hblock p x (fun he => hpq (he.trans h₁))
      have h₄ := hblock q y (fun he => hpq (h₂.symm.trans he.symm))
      simp [bridgeRows,hpq',Ne.symm hpq',h₃,h₄,P, Complex.normSq_eq_conj_mul_self]
      ring
  · push_neg at h
    obtain ⟨j,hjx,hjy,hj⟩ := h
    have hzero : P = 0 := Finset.prod_eq_zero
      (mem_erase.mpr ⟨hjy,mem_erase.mpr ⟨hjx,mem_univ j⟩⟩) (hblock (σ j) j hj)
    have hz := hzero
    dsimp [P] at hz
    simp [hzero,hz]

theorem bridge_det (U : Matrix ι ι ℂ) (side : ι → Bool)
    (hblock : ∀ i j, side i ≠ side j → U i j = 0) {p q : ι}
    (hpq : side p ≠ side q) {c s : ℂ}
    (hnorm : Complex.normSq c + Complex.normSq s = 1) :
    (bridgeRows U p q c s).det = U.det := by
  have hsum : ∑ σ : Equiv.Perm ι, leibnizTerm U (Equiv.swap p q * σ) =
      ∑ σ : Equiv.Perm ι, leibnizTerm U σ :=
    Equiv.sum_comp (Equiv.mulLeft (Equiv.swap p q)) (leibnizTerm U)
  rw [Matrix.det_apply', Matrix.det_apply']
  change (∑ σ, leibnizTerm _ σ) = ∑ σ, leibnizTerm U σ
  simp_rw [bridge_leibnizTerm U side hblock hpq, Finset.sum_add_distrib, ← Finset.mul_sum,
    hsum, ← add_mul, ← Complex.ofReal_add, hnorm, Complex.ofReal_one, one_mul]

theorem bridge_signedWeight (U : Matrix ι ι ℂ) (side : ι → Bool)
    (hblock : ∀ i j, side i ≠ side j → U i j = 0) {p q : ι}
    (hpq : side p ≠ side q) {c s : ℂ}
    (hnorm : Complex.normSq c + Complex.normSq s = 1) (σ : Equiv.Perm ι) :
    signedWeight (bridgeRows U p q c s) σ =
      (Complex.normSq c : ℂ) * signedWeight U σ +
      (Complex.normSq s : ℂ) * signedWeight U (Equiv.swap p q * σ) := by
  simp only [signedWeight, bridge_det U side hblock hpq hnorm,
    bridge_leibnizTerm U side hblock hpq]
  rw [add_div, mul_div_assoc, mul_div_assoc]

private def rowInner (x y : ι → ℂ) : ℂ :=
  ∑ k, x k * star (y k)

omit [DecidableEq ι] in
private theorem rowInner_add_left (x y z : ι → ℂ) :
    rowInner (x+y) z = rowInner x z + rowInner y z := by
  simp [rowInner, Pi.add_apply, add_mul, Finset.sum_add_distrib]

omit [DecidableEq ι] in
private theorem rowInner_add_right (x y z : ι → ℂ) :
    rowInner x (y+z) = rowInner x y + rowInner x z := by
  simp [rowInner, Pi.add_apply, star_add, mul_add, Finset.sum_add_distrib]

omit [DecidableEq ι] in
private theorem rowInner_smul_left (c : ℂ) (x y : ι → ℂ) :
    rowInner (c • x) y = c * rowInner x y := by
  simp [rowInner, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

omit [DecidableEq ι] in
private theorem rowInner_smul_right (c : ℂ) (x y : ι → ℂ) :
    rowInner x (c • y) = star c * rowInner x y := by
  simp only [rowInner, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The canonical normalized two-row gate preserves unitarity. -/
theorem bridgeRows_unitary (U : Matrix ι ι ℂ) (hU : IsUnitary U) {p q : ι}
    (hpq : p ≠ q) {c s : ℂ} (hnorm : Complex.normSq c + Complex.normSq s = 1) :
    IsUnitary (bridgeRows U p q c s) := by
  let V := bridgeRows U p q c s
  have hrow (i j : ι) : rowInner (U i) (U j) = (1 : Matrix ι ι ℂ) i j :=
    congrArg (fun N : Matrix ι ι ℂ => N i j) hU.1
  have hp : V p = c • U p + s • U q := by
    funext k
    simp [V,bridgeRows]
  have hq : V q = (-star s) • U p + star c • U q := by
    funext k
    simp [V,bridgeRows,hpq.symm]
  have hn (i : ι) (hip : i ≠ p) (hiq : i ≠ q) : V i = U i := by
    funext k
    simp [V,bridgeRows,hip,hiq]
  have hcast : ((Complex.normSq c : ℝ) : ℂ) + ((Complex.normSq s : ℝ) : ℂ) = 1 := by
    exact_mod_cast hnorm
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self] at hcast
  simp only [starRingEnd_apply] at hcast
  have hleft : V * Vᴴ = 1 := by
    ext i j : 1
    change rowInner (V i) (V j) = (1 : Matrix ι ι ℂ) i j
    by_cases hi : i = p
    · by_cases hj : j = p
      · rw [hi,hj,hp]
        simp only [rowInner_add_left,rowInner_add_right,rowInner_smul_left,rowInner_smul_right,
          hrow,Matrix.one_apply_eq,Matrix.one_apply_ne hpq,Matrix.one_apply_ne hpq.symm,
          mul_zero,add_zero,zero_add,mul_one]
        linear_combination hcast
      · by_cases hj' : j = q
        · rw [hi,hj',hp,hq]
          simp only [rowInner_add_left,rowInner_add_right,rowInner_smul_left,rowInner_smul_right,
            hrow,Matrix.one_apply_eq,Matrix.one_apply_ne hpq,Matrix.one_apply_ne hpq.symm,
            star_neg,star_star,mul_zero,add_zero,zero_add,mul_one]
          ring
        · rw [hi,hp,hn j hj hj']
          simp only [rowInner_add_left,rowInner_smul_left,hrow,
            Matrix.one_apply_ne (Ne.symm hj),Matrix.one_apply_ne (Ne.symm hj'),mul_zero,zero_add]
    · by_cases hi' : i = q
      · by_cases hj : j = p
        · rw [hi',hj,hq,hp]
          simp only [rowInner_add_left,rowInner_add_right,rowInner_smul_left,rowInner_smul_right,
            hrow,Matrix.one_apply_eq,Matrix.one_apply_ne hpq,Matrix.one_apply_ne hpq.symm,
            star_neg,star_star,mul_zero,add_zero,zero_add,mul_one]
          ring
        · by_cases hj' : j = q
          · rw [hi',hj',hq]
            simp only [rowInner_add_left,rowInner_add_right,rowInner_smul_left,rowInner_smul_right,
              hrow,Matrix.one_apply_eq,Matrix.one_apply_ne hpq,Matrix.one_apply_ne hpq.symm,
              star_neg,star_star,mul_zero,add_zero,zero_add,mul_one]
            linear_combination hcast
          · rw [hi',hq,hn j hj hj']
            simp only [rowInner_add_left,rowInner_smul_left,hrow,
              Matrix.one_apply_ne (Ne.symm hj),Matrix.one_apply_ne (Ne.symm hj'),mul_zero,zero_add]
      · by_cases hj : j = p
        · rw [hj,hn i hi hi',hp]
          simp only [rowInner_add_right,rowInner_smul_right,hrow,
            Matrix.one_apply_ne hi,Matrix.one_apply_ne hi',mul_zero,zero_add]
        · by_cases hj' : j = q
          · rw [hj',hn i hi hi',hq]
            simp only [rowInner_add_right,rowInner_smul_right,hrow,
              Matrix.one_apply_ne hi,Matrix.one_apply_ne hi',mul_zero,zero_add]
          · rw [hn i hi hi',hn j hj hj',hrow]
  exact ⟨hleft, Matrix.mul_eq_one_comm.mp hleft⟩

theorem bridge_determinantValue (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (side : ι → Bool)
    (hblock : ∀ i j, side i ≠ side j → U i j = 0) {p q : ι}
    (hpq : side p ≠ side q) {c s : ℂ}
    (hnorm : Complex.normSq c + Complex.normSq s = 1) :
    determinantValue a b (bridgeRows U p q c s) =
      (Complex.normSq c : ℂ) * determinantValue a b U +
      (Complex.normSq s : ℂ) * determinantValue (a ∘ Equiv.swap p q) b U := by
  have hV := bridgeRows_unitary U hU (fun h => hpq (congrArg side h)) hnorm
  rw [← signed_determinant a b _ hV, ← signed_determinant a b U hU,
    ← signed_determinant (a ∘ Equiv.swap p q) b U hU]
  simp_rw [bridge_signedWeight U side hblock hpq hnorm, add_mul, mul_assoc,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  congr 1
  let τ := Equiv.swap p q
  let f := fun σ : Equiv.Perm ι => signedWeight U σ * matchingProduct (a ∘ τ) b σ
  have he := Equiv.sum_comp (Equiv.mulLeft τ) f
  change (∑ σ, signedWeight U (τ * σ) * matchingProduct a b σ) = _
  have hfix (σ : Equiv.Perm ι) : matchingProduct (a ∘ τ) b (τ * σ) = matchingProduct a b σ := by
    simp [matchingProduct, Equiv.Perm.mul_apply, τ]
  change (∑ σ, signedWeight U (τ * σ) * matchingProduct (a ∘ τ) b (τ * σ)) = _ at he
  simpa only [hfix] using he

theorem holds_bridgeRows (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (side : ι → Bool) (hblock : ∀ i j, side i ≠ side j → U i j = 0)
    {p q : ι} (hpq : side p ≠ side q) {c s : ℂ}
    (hnorm : Complex.normSq c + Complex.normSq s = 1)
    (h₀ : Holds a b U) (h₁ : Holds (a ∘ Equiv.swap p q) b U) :
    Holds a b (bridgeRows U p q c s) := by
  have h₁' : determinantValue (a ∘ Equiv.swap p q) b U ∈
      convexHull ℝ (Set.range (matchingProduct a b)) := by
    unfold Holds at h₁
    apply convexHull_mono _ h₁
    rintro _ ⟨σ,rfl⟩
    exact ⟨Equiv.swap p q * σ, rfl⟩
  have h := (convex_convexHull ℝ (Set.range (matchingProduct a b))) h₀ h₁'
    (Complex.normSq_nonneg c) (Complex.normSq_nonneg s) hnorm
  unfold Holds
  rw [bridge_determinantValue a b U hU side hblock hpq hnorm]
  simpa only [Complex.real_smul] using h

/-- Common laws transfer through the bridge at a fixed first spectrum when
the original mixer has a law for both assignments of the two port values. -/
theorem commonWeights_bridgeRows (a : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (side : ι → Bool) (hblock : ∀ i j, side i ≠ side j → U i j = 0)
    {p q : ι} (hpq : side p ≠ side q) {c s : ℂ}
    (hnorm : Complex.normSq c + Complex.normSq s = 1)
    (h₀ : HasCommonWeights a U) (h₁ : HasCommonWeights (a ∘ Equiv.swap p q) U) :
    HasCommonWeights a (bridgeRows U p q c s) := by
  obtain ⟨w,hw,hm,he⟩ := h₀
  obtain ⟨v,hv,hn,hf⟩ := h₁
  let τ := Equiv.swap p q
  let α := Complex.normSq c
  let β := Complex.normSq s
  have hα : 0 ≤ α := Complex.normSq_nonneg c
  have hβ : 0 ≤ β := Complex.normSq_nonneg s
  refine ⟨fun σ => α * w σ + β * v (τ * σ),
    fun σ => add_nonneg (mul_nonneg hα (hw σ)) (mul_nonneg hβ (hv _)), ?_, ?_⟩
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hm]
    have hv' : ∑ σ, v (τ * σ) = ∑ σ, v σ := Equiv.sum_comp (Equiv.mulLeft τ) v
    rw [hv',hn,mul_one,mul_one]
    exact hnorm
  intro b
  rw [bridge_determinantValue a b U hU side hblock hpq hnorm, ← he b, ← hf b]
  have hfix (σ : Equiv.Perm ι) : matchingProduct (a ∘ τ) b (τ * σ) = matchingProduct a b σ := by
    simp [matchingProduct, Equiv.Perm.mul_apply, τ]
  simp_rw [weightedMatchingValue, Complex.ofReal_add, Complex.ofReal_mul, add_mul, mul_assoc,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  congr 1
  let f := fun σ : Equiv.Perm ι => (v σ : ℂ) * matchingProduct (a ∘ τ) b σ
  have hg := Equiv.sum_comp (Equiv.mulLeft τ) f
  change (∑ σ, (v (τ * σ) : ℂ) * matchingProduct (a ∘ τ) b (τ * σ)) = _ at hg
  simpa only [hfix] using hg


/-- A normalized two-port gate joins any two mixers that already satisfy
MOC for all of their spectral pairs, with no sparsity condition inside
the two child blocks. -/
theorem holds_bridge_of_blocks {κ : Type*} [Fintype κ] [DecidableEq κ]
    (L : Matrix ι ι ℂ) (R : Matrix κ κ ℂ) (hL : IsUnitary L) (hR : IsUnitary R)
    (hLc : ∀ a b, Holds a b L) (hRc : ∀ a b, Holds a b R)
    (p : ι) (q : κ) {c s : ℂ} (hnorm : Complex.normSq c + Complex.normSq s = 1)
    (a b : ι ⊕ κ → ℂ) :
    Holds a b (bridgeRows (Matrix.fromBlocks L 0 0 R) (.inl p) (.inr q) c s) := by
  let V := Matrix.fromBlocks L 0 0 R
  let side : ι ⊕ κ → Bool := Sum.elim (fun _ => false) (fun _ => true)
  have hblock (i j : ι ⊕ κ) (hij : side i ≠ side j) : V i j = 0 := by
    cases i <;> cases j <;> simp_all [side,V]
  have hV : IsUnitary V := unitary_directSum_iff.mpr ⟨hL,hR⟩
  have hcovered (a b : ι ⊕ κ → ℂ) : Holds a b V := by
    have hsplit (f : ι ⊕ κ → ℂ) :
        Sum.elim (f ∘ Sum.inl) (f ∘ Sum.inr) = f := by
      funext i
      cases i <;> rfl
    rw [← hsplit a, ← hsplit b]
    exact holds_directSum _ _ _ _ L R (hLc _ _) (hRc _ _)
  exact holds_bridgeRows a b V hV side hblock (by simp [side]) hnorm
    (hcovered _ _) (hcovered _ _)

/-- In particular, a connected order-six mixer made by joining two
order-three mixers obeys MOC for all complex spectra. -/
theorem holds_bridge_of_small_blocks {κ : Type*} [Fintype κ] [DecidableEq κ]
    (hι : Fintype.card ι ≤ 3) (hκ : Fintype.card κ ≤ 3)
    (L : Matrix ι ι ℂ) (R : Matrix κ κ ℂ) (hL : IsUnitary L) (hR : IsUnitary R)
    (p : ι) (q : κ) {c s : ℂ} (hnorm : Complex.normSq c + Complex.normSq s = 1)
    (a b : ι ⊕ κ → ℂ) :
    Holds a b (bridgeRows (Matrix.fromBlocks L 0 0 R) (.inl p) (.inr q) c s) :=
  holds_bridge_of_blocks L R hL hR
    (fun a b => conjecture_of_card_le_three hι a b L hL)
    (fun a b => conjecture_of_card_le_three hκ a b R hR) p q hnorm a b


end

end MOC
