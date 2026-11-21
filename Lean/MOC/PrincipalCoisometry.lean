import MOC.Claim
import MOC.PoleCompression
import MOC.SpectralPerturbation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.Tuple.Basic

/-! The unrestricted spectral conjecture in order `n+1` is equivalent to the
compression problem with a square left frame and an `n` by `n+1` right frame. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {n : ℕ}

/-- The rectangular vertices match each retained left label to a distinct right label. -/
def rectangularMatchingProduct (α : Fin n → ℂ) (β : Fin (n + 1) → ℂ)
    (e : Fin n ↪ Fin (n + 1)) : ℂ :=
  ∏ k, (α k + β (e k))

/-- The square-left CMC problem with one more label on the right. -/
def PrincipalCoisometryConjecture (n : ℕ) : Prop :=
  ∀ (α : Fin n → ℂ) (β : Fin (n + 1) → ℂ) (Y : Matrix (Fin n) (Fin (n + 1)) ℂ),
    Y * Yᴴ = 1 → (diagonal α + Y * diagonal β * Yᴴ).det ∈
      convexHull ℝ (Set.range (rectangularMatchingProduct α β))

private theorem exists_perm_extending_retained (i : Fin (n + 1)) (e : Fin n ↪ Fin (n + 1)) :
    ∃ σ : Equiv.Perm (Fin (n + 1)), ∀ k, σ.symm (i.succAbove k) = e k := by
  classical
  obtain ⟨z, hz⟩ : ∃ z, z ∉ Set.range e := by
    by_contra! h
    have hcard := Fintype.card_le_of_surjective e (fun z => h z)
    simp only [Fintype.card_fin] at hcard
    omega
  let g : Fin (n + 1) → Fin (n + 1) := Fin.insertNth i z e
  have h0 : g i = z := by simp only [g, Fin.insertNth_apply_same]
  have hg (k : Fin n) : g (i.succAbove k) = e k := by
    simp only [g, Fin.insertNth_apply_succAbove]
  have hne (k : Fin n) : g i ≠ g (i.succAbove k) := by
    rw [h0, hg]
    exact fun h => hz ⟨k, h.symm⟩
  have hinj : Function.Injective g := by
    intro j k
    rcases i.eq_self_or_eq_succAbove j with rfl | ⟨j, rfl⟩ <;>
      rcases i.eq_self_or_eq_succAbove k with rfl | ⟨k, rfl⟩
    · exact fun _ => rfl
    · exact fun h => (hne _ h).elim
    · exact fun h => (hne _ h.symm).elim
    · intro h
      simp only [hg] at h
      exact congrArg i.succAbove (e.injective h)
  let τ := Equiv.ofBijective g ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  exact ⟨τ.symm, fun k => hg k⟩

/-- Every rectangular matching extends to a permutation by filling its deleted row. -/
theorem rectangular_matching_range (α : Fin n → ℂ) (β : Fin (n + 1) → ℂ)
    (i : Fin (n + 1)) :
    Set.range (fun σ : Equiv.Perm (Fin (n + 1)) =>
      ∏ k : Fin n, (α k + β (σ.symm (i.succAbove k)))) =
      Set.range (rectangularMatchingProduct α β) := by
  ext z
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨i.succAboveEmb.trans σ.symm.toEmbedding, rfl⟩
  · rintro ⟨e, rfl⟩
    obtain ⟨σ, hσ⟩ := exists_perm_extending_retained i e
    exact ⟨σ, by simp only [hσ, rectangularMatchingProduct]⟩

private theorem retained_rows_coisometry (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hU : IsUnitary U) (i : Fin (n + 1)) :
    U.submatrix i.succAbove id * (U.submatrix i.succAbove id)ᴴ = 1 := by
  rw [Matrix.conjTranspose_submatrix,
    ← Matrix.submatrix_mul U Uᴴ i.succAbove id i.succAbove Function.bijective_id,
    hU.1, Matrix.submatrix_one i.succAbove Fin.succAbove_right_injective]

private theorem retained_rows_conjugation (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (β : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    U.submatrix i.succAbove id * diagonal β * (U.submatrix i.succAbove id)ᴴ =
      (U * diagonal β * Uᴴ).submatrix i.succAbove i.succAbove := by
  rw [Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul (U * diagonal β) Uᴴ i.succAbove id i.succAbove Function.bijective_id,
    Matrix.submatrix_mul U (diagonal β) i.succAbove id id Function.bijective_id,
    Matrix.submatrix_id_id]

/-- A rectangular coisometry completes to a unitary with the omitted row at any index. -/
theorem exists_unitary_retained_rows (Y : Matrix (Fin n) (Fin (n + 1)) ℂ)
    (hY : Y * Yᴴ = 1) (i : Fin (n + 1)) :
    ∃ U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsUnitary U ∧
      U.submatrix i.succAbove id = Y := by
  classical
  let v (k : Fin n) : EuclideanSpace ℂ (Fin (n + 1)) :=
    (WithLp.equiv 2 _).symm (fun j => star (Y k j))
  have hv : Orthonormal ℂ v := by
    apply orthonormal_iff_ite.mpr
    intro k l
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M k l) hY
    dsimp only [v]
    rw [EuclideanSpace.inner_piLp_equiv_symm]
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, dotProduct,
      Pi.star_apply, star_star, mul_comm] using h
  let f : Fin (n + 1) → EuclideanSpace ℂ (Fin (n + 1)) := Fin.insertNth i 0 v
  have hf_retained (k : Fin n) : f (i.succAbove k) = v k := by
    simp only [f, Fin.insertNth_apply_succAbove]
  let e := Equiv.ofInjective i.succAbove Fin.succAbove_right_injective
  let s := Set.range i.succAbove
  have hf : Orthonormal ℂ (s.restrict f) := by
    have he : s.restrict f = v ∘ e.symm := by
      funext k
      have hk := congrArg Subtype.val (e.apply_symm_apply k)
      change i.succAbove (e.symm k) = k.val at hk
      change f k.val = v (e.symm k)
      rw [← hk, hf_retained]
    rw [he]
    exact hv.comp _ e.symm.injective
  obtain ⟨B, hB⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℂ (EuclideanSpace ℂ (Fin (n + 1))) = Fintype.card (Fin (n + 1))) hf
  let U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of fun k j => star (B k j)
  have hU : U * Uᴴ = 1 := by
    ext k l : 1
    have h := orthonormal_iff_ite.mp B.orthonormal k l
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    change (∑ j, B l j * star (B k j)) = if k = l then (1 : ℂ) else 0 at h
    simpa only [U, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, star_star,
      Matrix.one_apply, mul_comm] using h
  refine ⟨U, ⟨hU, Matrix.mul_eq_one_comm.mp hU⟩, ?_⟩
  ext k j : 1
  change star (B (i.succAbove k) j) = Y k j
  rw [hB _ ⟨k, rfl⟩, hf_retained]
  change star (star (Y k j)) = _
  exact star_star _

private theorem diagonal_constant_eq_smul_one {ι : Type*} [DecidableEq ι] (t : ℂ) :
    diagonal (fun _ : ι => t) = t • (1 : Matrix ι ι ℂ) := by
  ext i j : 1
  by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]

/-- The unrestricted order-`n+1` inclusion is exactly the rectangular
coisometry problem with `n` retained rows. -/
theorem conjecture_iff_principalCoisometry (n : ℕ) :
    Conjecture (Fin (n + 1)) ↔ PrincipalCoisometryConjecture n := by
  classical
  let i : Fin (n + 1) := 0
  constructor
  · intro h α β Y hY
    obtain ⟨U, hU, hUY⟩ := exists_unitary_retained_rows Y hY i
    obtain ⟨t, ht⟩ := ((Set.finite_range (fun k => -α k)).union
      (Set.finite_range β)).exists_not_mem
    have hα (k : Fin n) : α k + t ≠ 0 := by
      intro hzero
      exact ht (Or.inl ⟨k, (eq_neg_of_add_eq_zero_right hzero).symm⟩)
    have hβ (j : Fin (n + 1)) : β j - t ≠ 0 := by
      intro hzero
      exact ht (Or.inr ⟨j, sub_eq_zero.mp hzero⟩)
    let a : Fin (n + 1) → ℂ := Fin.insertNth i 0 (fun k => (α k + t)⁻¹)
    let b : Fin (n + 1) → ℂ := fun j => (β j - t)⁻¹
    have ha0 : a i = 0 := Fin.insertNth_apply_same i 0 _
    have haret (k : Fin n) : a (i.succAbove k) = (α k + t)⁻¹ :=
      Fin.insertNth_apply_succAbove i 0 _ k
    have ha (k : Fin (n + 1)) (hk : k ≠ i) : a k - a i ≠ 0 := by
      obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hk
      rw [ha0, sub_zero, haret]
      exact inv_ne_zero (hα l)
    have hb (j : Fin (n + 1)) : b j + a i ≠ 0 := by
      simpa only [ha0, add_zero, b] using inv_ne_zero (hβ j)
    have hαrecip (k : Fin n) : (a (i.succAbove k) - a i)⁻¹ = α k + t := by
      rw [ha0, sub_zero, haret, inv_inv]
    have hβrecip (j : Fin (n + 1)) : (b j + a i)⁻¹ = β j - t := by
      simp only [ha0, add_zero, b, inv_inv]
    have hv (σ : Equiv.Perm (Fin (n + 1))) : poleMatchingProduct a b i σ =
        ∏ k : Fin n, (α k + β (σ.symm (i.succAbove k))) := by
      unfold poleMatchingProduct
      apply Finset.prod_congr rfl
      intro k _
      rw [hαrecip, hβrecip]
      ring
    have hmatrix : diagonal (fun k => α k + t) + Y * diagonal (fun j => β j - t) * Yᴴ =
        diagonal α + Y * diagonal β * Yᴴ := by
      rw [← Matrix.diagonal_add α (fun _ => t), ← Matrix.diagonal_sub β (fun _ => t),
        diagonal_constant_eq_smul_one, diagonal_constant_eq_smul_one,
        Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hY]
      abel
    have hcomp := (holds_iff_poleCompression a b U hU i ha hb).mp (h a b U hU)
    rw [show (fun k => (a (i.succAbove k) - a i)⁻¹) = _ from funext hαrecip, poleCompression,
      show (fun j => (b j + a i)⁻¹) = _ from funext hβrecip,
      ← retained_rows_conjugation U (fun j => β j - t) i, hUY, hmatrix,
      show poleMatchingProduct a b i = _ from funext hv, rectangular_matching_range] at hcomp
    exact hcomp
  · intro h
    apply conjecture_iff_regular_matching_products.mpr
    intro a b U hU hcross hmatch
    have ha (k : Fin (n + 1)) (hk : k ≠ i) : a k - a i ≠ 0 := by
      intro hzero
      have hai := sub_eq_zero.mp hzero
      have he : matchingProduct a b (Equiv.swap k i) = matchingProduct a b (Equiv.refl _) := by
        unfold matchingProduct
        apply Finset.prod_congr rfl
        intro j _
        change a (Equiv.swap k i j) + b j = a j + b j
        by_cases hjk : j = k
        · subst j
          rw [Equiv.swap_apply_left, hai]
        by_cases hji : j = i
        · subst j
          rw [Equiv.swap_apply_right, hai]
        rw [Equiv.swap_apply_of_ne_of_ne hjk hji]
      have hk' := congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ k) (hmatch he)
      exact hk (by simpa only [Equiv.swap_apply_left, Equiv.refl_apply] using hk'.symm)
    have hb (j : Fin (n + 1)) : b j + a i ≠ 0 := by simpa only [add_comm] using hcross i j
    let α (k : Fin n) := (a (i.succAbove k) - a i)⁻¹
    let β (j : Fin (n + 1)) := (b j + a i)⁻¹
    have hcomp := h α β (U.submatrix i.succAbove id) (retained_rows_coisometry U hU i)
    rw [retained_rows_conjugation U β i, ← rectangular_matching_range α β i] at hcomp
    apply (holds_iff_poleCompression a b U hU i ha hb).mpr
    simpa only [α, β, poleCompression, poleMatchingProduct] using hcomp

/-- A square left coisometry may be absorbed into the retained coordinate frame. -/
theorem conjecture_iff_rectangularCompression (n : ℕ) : Conjecture (Fin (n + 1)) ↔
    ∀ (α : Fin n → ℂ) (β : Fin (n + 1) → ℂ) (X : Matrix (Fin n) (Fin n) ℂ)
      (Y : Matrix (Fin n) (Fin (n + 1)) ℂ), X * Xᴴ = 1 → Y * Yᴴ = 1 →
      (X * diagonal α * Xᴴ + Y * diagonal β * Yᴴ).det ∈
        convexHull ℝ (Set.range (rectangularMatchingProduct α β)) := by
  rw [conjecture_iff_principalCoisometry]
  constructor
  · intro h α β X Y hX hY
    have hX' : Xᴴ * X = 1 := Matrix.mul_eq_one_comm.mp hX
    have hY' : (Xᴴ * Y) * (Xᴴ * Y)ᴴ = 1 := by
      calc
        _ = Xᴴ * (Y * Yᴴ) * X := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
        _ = _ := by rw [hY, Matrix.mul_one, hX']
    have hmat : X * (diagonal α + (Xᴴ * Y) * diagonal β * (Xᴴ * Y)ᴴ) * Xᴴ =
        X * diagonal α * Xᴴ + Y * diagonal β * Yᴴ := by
      have hm : X * ((Xᴴ * Y) * diagonal β * (Xᴴ * Y)ᴴ) * Xᴴ =
          Y * diagonal β * Yᴴ := by
        calc
          _ = (X * Xᴴ) * (Y * diagonal β * Yᴴ) * (X * Xᴴ) := by
            simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
          _ = _ := by simp only [hX, Matrix.one_mul, Matrix.mul_one]
      rw [Matrix.mul_add, Matrix.add_mul, hm]
    rw [← hmat, det_unitary_conjugation X _ ⟨hX, hX'⟩]
    exact h α β (Xᴴ * Y) hY'
  · intro h α β Y hY
    simpa only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] using
      h α β 1 Y (by simp) hY

/-- The open orders of MOC are equivalent to square-left CMC with at least three retained rows. -/
theorem mocIsTrue_iff_principalCoisometry :
    MOCIsTrue ↔ ∀ n : ℕ, 3 ≤ n → PrincipalCoisometryConjecture n := by
  rw [mocIsTrue_iff_from_four]
  constructor
  · intro h n hn
    exact (conjecture_iff_principalCoisometry n).mp (h (n + 1) (by omega))
  · intro h m hm
    cases m with
    | zero => omega
    | succ n => exact (conjecture_iff_principalCoisometry n).mpr (h n (by omega))

end

end MOC
