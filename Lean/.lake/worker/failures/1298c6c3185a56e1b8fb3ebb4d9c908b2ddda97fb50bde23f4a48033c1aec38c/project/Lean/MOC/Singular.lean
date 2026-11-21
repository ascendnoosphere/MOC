import MOC.Small
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! The singular determinant case, by the shared spectral moments argument
of Drury and Cload. The two probability laws need at most five labels in total. -/

open BigOperators Matrix
open scoped ComplexInnerProductSpace

namespace MOC

noncomputable section

private structure SharedMoments {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℂ) (c : κ → ℂ) (p : ι → ℝ) (q : κ → ℝ) : Prop where
  left_nonneg : ∀ i, 0 ≤ p i
  right_nonneg : ∀ j, 0 ≤ q j
  left_mass : ∑ i, p i = 1
  right_mass : ∑ j, q j = 1
  first : ∑ i, (p i : ℂ) * a i = ∑ j, (q j : ℂ) * c j
  second : ∑ i, p i * Complex.normSq (a i) = ∑ j, q j * Complex.normSq (c j)

private theorem exists_sparse_weights {β : Type*} [Fintype β] [DecidableEq β]
    (f : β → Fin 4 → ℝ) {x : Fin 4 → ℝ} (hx : x ∈ convexHull ℝ (Set.range f)) :
    ∃ w : β → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧ (∑ j, w j • f j) = x ∧
      (Finset.univ.filter (fun j => w j ≠ 0)).card ≤ 5 := by
  classical
  obtain ⟨η, hη, z, v, hz, hInd, hv, hmass, hsum⟩ := eq_pos_convex_span_of_mem_convexHull hx
  letI : Fintype η := hη
  have hle : Fintype.card η ≤ 5 := by
    calc
      Fintype.card η ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range z)) + 1 :=
        hInd.card_le_finrank_succ
      _ ≤ Module.finrank ℝ (Fin 4 → ℝ) + 1 := Nat.add_le_add_right (Submodule.finrank_le _) _
      _ = 5 := by simp [Module.finrank_fin_fun]
  choose g hg using fun i => hz (Set.mem_range_self i)
  let w (j : β) : ℝ := ∑ i, if g i = j then v i else 0
  refine ⟨w, fun j => Finset.sum_nonneg (fun i _ => by split <;> simp_all [(hv i).le]), ?_, ?_, ?_⟩
  · simpa [w, Finset.sum_comm (f := fun j i => if g i = j then v i else 0)] using hmass
  · calc
      ∑ j, w j • f j = ∑ j, ∑ i, (if g i = j then v i else 0) • f j := by
        simp only [w, Finset.sum_smul]
      _ = ∑ i, v i • f (g i) := by rw [Finset.sum_comm]; simp [ite_smul]
      _ = x := by simpa only [hg] using hsum
  · have hs : Finset.univ.filter (fun j => w j ≠ 0) ⊆ Finset.univ.image g := by
      intro j hj
      by_contra hnj
      have hall (i : η) : g i ≠ j := fun he => hnj (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he⟩)
      exact (Finset.mem_filter.mp hj).2 (by simp [w, hall])
    calc
      _ ≤ (Finset.univ.image g).card := Finset.card_le_card hs
      _ ≤ Fintype.card η := Finset.card_image_le
      _ ≤ 5 := hle

private def taggedLift {ι κ : Type*} (a : ι → ℂ) (c : κ → ℂ) :
    ι ⊕ κ → Fin 4 → ℝ :=
  Sum.elim (fun i => ![(a i).re, (a i).im, Complex.normSq (a i), 1])
    (fun j => ![-(c j).re, -(c j).im, -Complex.normSq (c j), 0])

private theorem taggedLift_barycenter {ι κ : Type*} [Fintype ι] [Fintype κ]
    {a : ι → ℂ} {c : κ → ℂ} {p : ι → ℝ} {q : κ → ℝ}
    (h : SharedMoments a c p q) :
    ![0, 0, 0, (1 / 2 : ℝ)] ∈ convexHull ℝ (Set.range (taggedLift a c)) := by
  let w := Sum.elim (fun i => p i / 2) (fun j => q j / 2)
  apply mem_convexHull_of_exists_fintype w (taggedLift a c)
  · intro k
    cases k with
    | inl i => exact div_nonneg (h.left_nonneg _) (by norm_num)
    | inr j => exact div_nonneg (h.right_nonneg _) (by norm_num)
  · simp only [Fintype.sum_sum_type, w, Sum.elim_inl, Sum.elim_inr, ← Finset.sum_div,
      h.left_mass, h.right_mass]
    norm_num
  · exact fun k => Set.mem_range_self k
  · ext k
    have hre := congrArg Complex.re h.first
    have him := congrArg Complex.im h.first
    simp only [Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, zero_add, add_zero] at hre him
    fin_cases k <;>
      simp [Finset.sum_apply, Fintype.sum_sum_type, w, taggedLift, Matrix.cons_val',
        smul_eq_mul, div_mul_eq_mul_div, mul_neg, Finset.sum_neg_distrib, ← Finset.sum_div,
        hre, him, h.second, h.left_mass] <;> ring

private theorem exists_sparse_sharedMoments {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {a : ι → ℂ} {c : κ → ℂ} {p : ι → ℝ} {q : κ → ℝ}
    (h : SharedMoments a c p q) :
    ∃ p' q', SharedMoments a c p' q' ∧
      (Finset.univ.filter (fun i => p' i ≠ 0)).card +
        (Finset.univ.filter (fun j => q' j ≠ 0)).card ≤ 5 := by
  classical
  obtain ⟨w, hw, hmass, hb, hcard⟩ := exists_sparse_weights _ (taggedLift_barycenter h)
  let p' (i : ι) := 2 * w (.inl i)
  let q' (j : κ) := 2 * w (.inr j)
  have he (k : Fin 4) := congrFun hb k
  have hleft := he 3
  simp [Finset.sum_apply, Fintype.sum_sum_type, taggedLift, smul_eq_mul, Matrix.cons_val'] at hleft
  rw [Fintype.sum_sum_type] at hmass
  refine ⟨p', q', ⟨fun i => mul_nonneg (by norm_num) (hw _), fun j => mul_nonneg (by norm_num) (hw _),
    ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [show ∑ i, p' i = 2 * ∑ i, w (.inl i) by unfold p'; rw [Finset.mul_sum], hleft]; norm_num
  · unfold q'
    rw [← Finset.mul_sum]
    linarith
  · apply Complex.ext
    · have hr := he 0
      simp [Finset.sum_apply, Fintype.sum_sum_type, taggedLift, smul_eq_mul, Matrix.cons_val'] at hr
      simp only [p', q', Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, mul_assoc, ← Finset.mul_sum]
      linarith
    · have hi := he 1
      simp [Finset.sum_apply, Fintype.sum_sum_type, taggedLift, smul_eq_mul, Matrix.cons_val'] at hi
      simp only [p', q', Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, mul_assoc, ← Finset.mul_sum]
      linarith
  · have hs := he 2
    simp [Finset.sum_apply, Fintype.sum_sum_type, taggedLift, smul_eq_mul, Matrix.cons_val'] at hs
    simp only [p', q', mul_assoc, ← Finset.mul_sum]
    linarith
  · have h₁ : Fintype.card {i : ι // p' i ≠ 0} = (Finset.univ.filter (fun i => p' i ≠ 0)).card := by
      simp [Fintype.card_subtype]
    have h₂ : Fintype.card {j : κ // q' j ≠ 0} = (Finset.univ.filter (fun j => q' j ≠ 0)).card := by
      simp [Fintype.card_subtype]
    have h₃ : Fintype.card {k : ι ⊕ κ // w k ≠ 0} =
        (Finset.univ.filter (fun k => w k ≠ 0)).card := by simp [Fintype.card_subtype]
    let e : ({i // p' i ≠ 0} ⊕ {j // q' j ≠ 0}) ≃ {k : ι ⊕ κ // w k ≠ 0} :=
      { toFun := fun s => match s with
          | .inl i => ⟨.inl i, by simpa [p'] using i.property⟩
          | .inr j => ⟨.inr j, by simpa [q'] using j.property⟩
        invFun := fun s => match s with
          | ⟨.inl i, hi⟩ => .inl ⟨i, by simpa [p'] using hi⟩
          | ⟨.inr j, hj⟩ => .inr ⟨j, by simpa [q'] using hj⟩
        left_inv := by rintro (i | j) <;> rfl
        right_inv := by rintro ⟨i | j, h⟩ <;> rfl }
    rw [← h₁, ← h₂, ← Fintype.card_sum, Fintype.card_congr e, h₃]
    exact hcard

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem unitary_star_dot {U : Matrix ι ι ℂ} (hU : IsUnitary U) (x y : ι → ℂ) :
    star (U *ᵥ x) ⬝ᵥ (U *ᵥ y) = star x ⬝ᵥ y := by
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hU.2, Matrix.vecMul_one]

omit [DecidableEq ι] in
private theorem star_dot_normSq (x : ι → ℂ) :
    star x ⬝ᵥ x = ((∑ i, Complex.normSq (x i)) : ℝ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self,
    starRingEnd_apply]

private theorem diagonal_star_dot (x a : ι → ℂ) :
    star x ⬝ᵥ (diagonal a *ᵥ x) = ∑ i, (Complex.normSq (x i) : ℂ) * a i := by
  simp only [dotProduct, Pi.star_apply, Matrix.mulVec_diagonal, Complex.normSq_eq_conj_mul_self,
    starRingEnd_apply]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

private theorem sharedMoments_of_singular (a b : ι → ℂ) {U : Matrix ι ι ℂ}
    (hU : IsUnitary U) (hzero : determinantValue a b U = 0) :
    ∃ p q, SharedMoments a (fun i => -b i) p q := by
  obtain ⟨v, hv, hk⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hzero
  let u := Uᴴ *ᵥ v
  let c : ι → ℂ := fun i => -b i
  have huv : U *ᵥ u = v := by simp [u, Matrix.mulVec_mulVec, hU.1]
  have hcv : U *ᵥ (diagonal c *ᵥ u) = diagonal a *ᵥ v := by
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hk
    change diagonal a *ᵥ v + U *ᵥ (diagonal b *ᵥ u) = 0 at hk
    rw [show diagonal c = -diagonal b by simp [c, Matrix.diagonal_neg],
      Matrix.neg_mulVec, Matrix.mulVec_neg]
    exact (eq_neg_of_add_eq_zero_left hk).symm
  have hmass : ∑ i, Complex.normSq (v i) = ∑ i, Complex.normSq (u i) := by
    have he := unitary_star_dot hU u u
    rw [huv, star_dot_normSq, star_dot_normSq] at he
    exact Complex.ofReal_injective he
  have hfirst : (∑ i, (Complex.normSq (v i) : ℂ) * a i) =
      ∑ i, (Complex.normSq (u i) : ℂ) * c i := by
    have he := unitary_star_dot hU u (diagonal c *ᵥ u)
    rwa [huv, hcv, diagonal_star_dot, diagonal_star_dot] at he
  have hsecond : (∑ i, Complex.normSq (v i) * Complex.normSq (a i)) =
      ∑ i, Complex.normSq (u i) * Complex.normSq (c i) := by
    have he := unitary_star_dot hU (diagonal c *ᵥ u) (diagonal c *ᵥ u)
    rw [hcv, star_dot_normSq, star_dot_normSq] at he
    simpa only [Matrix.mulVec_diagonal, Complex.normSq_mul, mul_comm (Complex.normSq (a _)),
      mul_comm (Complex.normSq (c _))] using Complex.ofReal_injective he
  let s := ∑ i, Complex.normSq (v i)
  have hs : 0 < s := by
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra! hh
      exact hv (funext hh)
    apply Finset.sum_pos' (fun i _ => Complex.normSq_nonneg (v i))
    exact ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩
  have hq : (∑ i, Complex.normSq (u i)) = s := hmass.symm
  refine ⟨fun i => Complex.normSq (v i) / s, fun i => Complex.normSq (u i) / s,
    ⟨fun i => div_nonneg (Complex.normSq_nonneg _) hs.le,
      fun i => div_nonneg (Complex.normSq_nonneg _) hs.le, ?_, ?_, ?_, ?_⟩⟩
  · rw [← Finset.sum_div]
    exact div_self hs.ne'
  · rw [← Finset.sum_div, hq, div_self hs.ne']
  · simp only [Complex.ofReal_div, div_mul_eq_mul_div, ← Finset.sum_div, hfirst, c]
  · simp only [div_mul_eq_mul_div, ← Finset.sum_div, hsecond, c]

private theorem exists_linearIsometry_matching_pair
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (x y x' y' : E) (hn : ∀ (a b : ℂ), ‖a • x + b • y‖ = ‖a • x' + b • y'‖) :
    ∃ L : E →ₗᵢ[ℂ] E, L x = x' ∧ L y = y' := by
  let A : ℂ × ℂ →ₗ[ℂ] E := (LinearMap.id.smulRight x).coprod (LinearMap.id.smulRight y)
  let B : ℂ × ℂ →ₗ[ℂ] E := (LinearMap.id.smulRight x').coprod (LinearMap.id.smulRight y')
  have hab (v : ℂ × ℂ) : ‖A v‖ = ‖B v‖ := hn v.1 v.2
  have hker : LinearMap.ker A ≤ LinearMap.ker B := by
    intro v hv
    have he := hab v
    rw [LinearMap.mem_ker.mp hv, norm_zero, eq_comm, norm_eq_zero] at he
    exact LinearMap.mem_ker.mpr he
  let M : LinearMap.range A →ₗ[ℂ] E :=
    ((LinearMap.ker A).liftQ B hker).comp A.quotKerEquivRange.symm.toLinearMap
  have hM (v : ℂ × ℂ) : M ⟨A v, LinearMap.mem_range_self A _⟩ = B v := by
    change (LinearMap.ker A).liftQ B hker (A.quotKerEquivRange.symm _) = _
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  let L : LinearMap.range A →ₗᵢ[ℂ] E :=
    { toLinearMap := M
      norm_map' := by
        rintro ⟨u, v, rfl⟩
        rw [show M ⟨A v, LinearMap.mem_range_self A v⟩ = B v from hM v]
        exact (hab v).symm }
  refine ⟨L.extend, ?_, ?_⟩
  · simpa [A, B, LinearMap.coprod_apply, LinearMap.smulRight_apply] using
      (L.extend_apply ⟨A (1, 0), LinearMap.mem_range_self A _⟩).trans (hM (1, 0))
  · simpa [A, B, LinearMap.coprod_apply, LinearMap.smulRight_apply] using
      (L.extend_apply ⟨A (0, 1), LinearMap.mem_range_self A _⟩).trans (hM (0, 1))

private theorem unitary_for_two_vectors (x y u v : ι → ℂ)
    (hxx : star x ⬝ᵥ x = star u ⬝ᵥ u) (hxy : star x ⬝ᵥ y = star u ⬝ᵥ v)
    (hyy : star y ⬝ᵥ y = star v ⬝ᵥ v) :
    ∃ U : Matrix ι ι ℂ, IsUnitary U ∧ U *ᵥ x = u ∧ U *ᵥ y = v := by
  let T := (WithLp.equiv 2 (ι → ℂ)).symm
  have hi (a b : ι → ℂ) : ⟪T a, T b⟫ = star a ⬝ᵥ b :=
    (EuclideanSpace.inner_piLp_equiv_symm a b).trans (dotProduct_comm _ _)
  have hyx : ⟪T y, T x⟫ = ⟪T v, T u⟫ := by
    have h : ⟪T x, T y⟫ = ⟪T u, T v⟫ := by simp only [hi, hxy]
    simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) h
  have hn (r s : ℂ) : ‖r • T x + s • T y‖ = ‖r • T u + s • T v‖ := by
    simp only [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, hyx, hi, hxx, hxy, hyy]
  obtain ⟨L, hLx, hLy⟩ := exists_linearIsometry_matching_pair (T x) (T y) (T u) (T v) hn
  let e := LinearIsometryEquiv.ofSurjective L
    (LinearMap.surjective_of_injective (f := L.toLinearMap) L.injective)
  let b := EuclideanSpace.basisFun ι ℂ
  let U := LinearMap.toMatrix b.toBasis b.toBasis L.toLinearMap
  have hmat : U = b.toBasis.toMatrix (b.map e) := by
    ext i j
    rw [show U = LinearMap.toMatrix b.toBasis b.toBasis L.toLinearMap from rfl,
      LinearMap.toMatrix_apply, Basis.toMatrix_apply] <;> rfl
  have hU : U ∈ Matrix.unitaryGroup ι ℂ := by
    rw [hmat]
    exact b.toMatrix_orthonormalBasis_mem_unitary (b.map e)
  have hrepr (w : EuclideanSpace ℂ ι) :
      (b.toBasis.repr w : ι → ℂ) = WithLp.equiv 2 (ι → ℂ) w := by
    funext i
    exact b.coe_toBasis_repr_apply w i
  have hmul (w w' : ι → ℂ) (hw : L (T w) = T w') : U *ᵥ w = w' := by
    have hm := L.toLinearMap.toMatrix_mulVec_repr b.toBasis b.toBasis (T w)
    change U *ᵥ (b.toBasis.repr (T w) : ι → ℂ) = (b.toBasis.repr (L (T w)) : ι → ℂ) at hm
    rw [hw, hrepr, hrepr] at hm
    exact hm
  exact ⟨U, ⟨Matrix.mem_unitaryGroup_iff.mp hU, Matrix.mem_unitaryGroup_iff'.mp hU⟩,
    hmul x u hLx, hmul y v hLy⟩

private theorem singular_of_sharedMoments {a c : ι → ℂ} {p q : ι → ℝ}
    (h : SharedMoments a c p q) :
    ∃ U : Matrix ι ι ℂ, IsUnitary U ∧ determinantValue a (fun i => -c i) U = 0 := by
  let x (i : ι) : ℂ := (Real.sqrt (p i) : ℂ)
  let y (i : ι) : ℂ := (Real.sqrt (q i) : ℂ)
  let A := diagonal a
  let C := diagonal c
  have hx (i : ι) : Complex.normSq (x i) = p i := by
    rw [show x i = (Real.sqrt (p i) : ℂ) from rfl, Complex.normSq_ofReal, ← pow_two,
      Real.sq_sqrt (h.left_nonneg _)]
  have hy (i : ι) : Complex.normSq (y i) = q i := by
    rw [show y i = (Real.sqrt (q i) : ℂ) from rfl, Complex.normSq_ofReal, ← pow_two,
      Real.sq_sqrt (h.right_nonneg _)]
  have hx1 : star x ⬝ᵥ x = 1 := by rw [star_dot_normSq]; simp [hx, h.left_mass]
  have hy1 : star y ⬝ᵥ y = 1 := by rw [star_dot_normSq]; simp [hy, h.right_mass]
  have hxy : star y ⬝ᵥ (C *ᵥ y) = star x ⬝ᵥ (A *ᵥ x) := by
    simpa only [A, C, diagonal_star_dot, hx, hy] using h.first.symm
  have hab : star (C *ᵥ y) ⬝ᵥ (C *ᵥ y) = star (A *ᵥ x) ⬝ᵥ (A *ᵥ x) := by
    rw [star_dot_normSq, star_dot_normSq]
    congr 1
    simpa only [A, C, Matrix.mulVec_diagonal, Complex.normSq_mul, hx, hy,
      mul_comm (Complex.normSq (c _)), mul_comm (Complex.normSq (a _))] using h.second.symm
  obtain ⟨U, hU, hyx, hdiag⟩ := unitary_for_two_vectors y (C *ᵥ y) x (A *ᵥ x)
    (hy1.trans hx1.symm) hxy hab
  refine ⟨U, hU, Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, ?_, ?_⟩⟩
  · intro hz
    simp [hz] at hx1
  · have hy' : Uᴴ *ᵥ x = y := by rw [← hyx, Matrix.mulVec_mulVec, hU.2, Matrix.one_mulVec]
    change (A + U * diagonal (fun i => -c i) * Uᴴ) *ᵥ x = 0
    rw [show diagonal (fun i => -c i) = -C by simp [C, Matrix.diagonal_neg],
      Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hy',
      Matrix.neg_mulVec, Matrix.mulVec_neg, hdiag, add_neg_cancel]

private theorem weighted_squared_distance (c : ι → ℂ) (q : ι → ℝ) (z : ℂ) :
    (∑ j, q j * Complex.normSq (c j - z)) =
      (∑ j, q j * Complex.normSq (c j)) + (∑ j, q j) * Complex.normSq z -
        2 * (((∑ j, (q j : ℂ) * c j) * star z).re) := by
  have he (j : ι) :
      q j * Complex.normSq (c j - z) =
        q j * Complex.normSq (c j) + q j * Complex.normSq z -
          2 * (((q j : ℂ) * c j * star z).re) := by
    rw [Complex.normSq_sub, mul_assoc (q j : ℂ) (c j) (star z),
      Complex.re_ofReal_mul, Complex.star_def]
    ring
  simp only [he, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul,
    Finset.mul_sum, Complex.re_sum]

private theorem opposite_of_one_weight {a c : ι → ℂ} {p q : ι → ℝ}
    (h : SharedMoments a c p q) (hc : (Finset.univ.filter (fun i => p i ≠ 0)).card = 1) :
    ∃ i j, a i = c j := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
  have hn (k : ι) (hk : k ≠ i) : p k = 0 := by
    by_contra hne
    have hm : k ∈ Finset.univ.filter (fun i => p i ≠ 0) := by simp [hne]
    simp [hi, hk] at hm
  have hp : p i = 1 := by
    have hm := h.left_mass
    rw [Finset.sum_eq_single i] at hm
    · exact hm
    · exact fun k _ hk => hn k hk
    · simp
  have h₁ : ∑ j, (q j : ℂ) * c j = a i := by
    rw [← h.first, Finset.sum_eq_single i]
    · simp [hp]
    · exact fun k _ hk => by simp [hn k hk]
    · simp
  have h₂ : ∑ j, q j * Complex.normSq (c j) = Complex.normSq (a i) := by
    rw [← h.second, Finset.sum_eq_single i]
    · simp [hp]
    · exact fun k _ hk => by simp [hn k hk]
    · simp
  have hz : ∑ j, q j * Complex.normSq (c j - a i) = 0 := by
    rw [weighted_squared_distance, h₁, h₂, h.right_mass]
    rw [show (a i * star (a i)).re = Complex.normSq (a i) by
      rw [mul_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]]
    ring
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show ∑ j, q j ≠ 0 from h.right_mass.trans_ne one_ne_zero)
  have hjz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => mul_nonneg (h.right_nonneg j) (Complex.normSq_nonneg _))).mp hz j (Finset.mem_univ _)
  exact ⟨i, j, (sub_eq_zero.mp (Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hjz).resolve_left hj))).symm⟩

omit [DecidableEq ι] in
private theorem restrict_moment_sum {R : Type*} [AddCommMonoid R] (I : Finset ι) (g : ι → R)
    (hg : ∀ i ∉ I, g i = 0) : (∑ i : I, g i) = ∑ i, g i := by
  change (∑ i ∈ I.attach, g i) = _
  rw [Finset.sum_attach]
  exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hg i hi)

private theorem sharedMoments_on_three {a c : ι → ℂ} {p q : ι → ℝ}
    (h : SharedMoments a c p q) {I J : Finset ι}
    (hI : Finset.univ.filter (fun i => p i ≠ 0) ⊆ I)
    (hJ : Finset.univ.filter (fun j => q j ≠ 0) ⊆ J) (f : Fin 3 ≃ I) (g : Fin 3 ≃ J) :
    SharedMoments (fun i => a (f i)) (fun j => c (g j)) (fun i => p (f i)) (fun j => q (g j)) := by
  have hp (i : ι) (hi : i ∉ I) : p i = 0 := by
    by_contra hne
    exact hi (hI (by simp [hne]))
  have hq (j : ι) (hj : j ∉ J) : q j = 0 := by
    by_contra hne
    exact hj (hJ (by simp [hne]))
  refine ⟨fun i => h.left_nonneg _, fun j => h.right_nonneg _, ?_, ?_, ?_, ?_⟩
  · rw [Equiv.sum_comp f (fun i : I => p i), restrict_moment_sum _ _ hp, h.left_mass]
  · rw [Equiv.sum_comp g (fun j : J => q j), restrict_moment_sum _ _ hq, h.right_mass]
  · rw [Equiv.sum_comp f (fun i : I => (p i : ℂ) * a i),
      Equiv.sum_comp g (fun j : J => (q j : ℂ) * c j),
      restrict_moment_sum I (fun i => (p i : ℂ) * a i) (fun i hi => by simp [hp i hi]),
      restrict_moment_sum J (fun j => (q j : ℂ) * c j) (fun j hj => by simp [hq j hj])]
    exact h.first
  · rw [Equiv.sum_comp f (fun i : I => p i * Complex.normSq (a i)),
      Equiv.sum_comp g (fun j : J => q j * Complex.normSq (c j)),
      restrict_moment_sum I (fun i => p i * Complex.normSq (a i)) (fun i hi => by simp [hp i hi]),
      restrict_moment_sum J (fun j => q j * Complex.normSq (c j)) (fun j hj => by simp [hq j hj])]
    exact h.second

omit [DecidableEq ι] in
private theorem zero_in_hull_of_matching_three (a b : ι → ℂ) {κ : Type*}
    [Fintype κ] [DecidableEq κ] (eRow eCol : Fin 3 ⊕ κ ≃ ι)
    (hsmall : 0 ∈ convexHull ℝ (Set.range
      (matchingProduct (a ∘ eRow ∘ Sum.inl) (b ∘ eCol ∘ Sum.inl)))) :
    0 ∈ convexHull ℝ (Set.range (matchingProduct a b)) := by
  let a₁ := a ∘ eRow ∘ Sum.inl
  let b₁ := b ∘ eCol ∘ Sum.inl
  let a₂ := a ∘ eRow ∘ Sum.inr
  let b₂ := b ∘ eCol ∘ Sum.inr
  have hlift (σ : Equiv.Perm (Fin 3)) (τ : Equiv.Perm κ) :
      matchingProduct a₁ b₁ σ * matchingProduct a₂ b₂ τ ∈
        convexHull ℝ (Set.range (matchingProduct a b)) := by
    let π := Equiv.sumCongr σ τ
    let π' : Equiv.Perm ι := (eCol.symm.trans π).trans eRow
    have heq : matchingProduct a b π' =
        matchingProduct (Sum.elim a₁ a₂) (Sum.elim b₁ b₂) π := by
      unfold matchingProduct
      rw [← Equiv.prod_comp eCol (fun j => a (π' j) + b j)]
      apply Finset.prod_congr rfl
      intro j _
      have hrow (i : Fin 3 ⊕ κ) : a (eRow i) = Sum.elim a₁ a₂ i := by cases i <;> rfl
      have hcol (i : Fin 3 ⊕ κ) : b (eCol i) = Sum.elim b₁ b₂ i := by cases i <;> rfl
      simp only [π', Equiv.trans_apply, Equiv.symm_apply_apply, hrow, hcol]
    rw [← matchingProduct_sum, ← heq]
    exact matchingProduct_mem_hull a b π'
  have hprod := mul_mem_of_mem_convexHulls (convex_convexHull ℝ (Set.range (matchingProduct a b)))
    (by rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩; exact hlift σ τ) hsmall
    (matchingProduct_mem_hull a₂ b₂ (Equiv.refl κ))
  simpa only [zero_mul] using hprod

/-- A singular sum of two finite normal spectra satisfies the determinant hull inclusion. -/
theorem holds_of_singular (a b : ι → ℂ) {U : Matrix ι ι ℂ}
    (hU : IsUnitary U) (hzero : determinantValue a b U = 0) : Holds a b U := by
  classical
  by_cases hsmall : Fintype.card ι ≤ 3
  · exact conjecture_of_card_le_three hsmall a b U hU
  let c : ι → ℂ := fun i => -b i
  obtain ⟨p₀, q₀, h₀⟩ := sharedMoments_of_singular a b hU hzero
  obtain ⟨p, q, h, hc⟩ := exists_sparse_sharedMoments h₀
  have hok (i j : ι) (hij : a i = c j) : Holds a b U := by
    unfold Holds
    rw [hzero]
    let σ := Equiv.swap j i
    have he : matchingProduct a b σ = 0 := by
      unfold matchingProduct
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      change a i = -b j at hij
      simp [σ, hij]
    rw [← he]
    exact matchingProduct_mem_hull a b σ
  have hswap : SharedMoments c a q p :=
    ⟨h.right_nonneg, h.left_nonneg, h.right_mass, h.left_mass, h.first.symm, h.second.symm⟩
  by_cases hp : (Finset.univ.filter (fun i => p i ≠ 0)).card = 1
  · obtain ⟨i, j, hij⟩ := opposite_of_one_weight h hp
    exact hok i j hij
  by_cases hq : (Finset.univ.filter (fun j => q j ≠ 0)).card = 1
  · obtain ⟨j, i, hji⟩ := opposite_of_one_weight hswap hq
    exact hok i j hji.symm
  have hpos (w : ι → ℝ) (hw : ∑ i, w i = 1) :
      0 < (Finset.univ.filter (fun i => w i ≠ 0)).card := by
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hw.trans_ne one_ne_zero)
    exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  have hpc := hpos p h.left_mass
  have hqc := hpos q h.right_mass
  have hn : 3 ≤ Finset.univ.card (α := ι) := by simp; omega
  obtain ⟨I, hI, _, h3I⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (Finset.univ.filter fun i => p i ≠ 0)) (by omega) hn
  obtain ⟨J, hJ, _, h3J⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (Finset.univ.filter fun j => q j ≠ 0)) (by omega) hn
  let f : Fin 3 ≃ I := Fintype.equivOfCardEq (by simpa [Fintype.card_coe] using h3I.symm)
  let g : Fin 3 ≃ J := Fintype.equivOfCardEq (by simpa [Fintype.card_coe] using h3J.symm)
  let κ := {j : ι // j ∉ J}
  let e : κ ≃ {i : ι // i ∉ I} := Fintype.equivOfCardEq (by
    simp [κ, Fintype.card_subtype_compl, Fintype.card_coe, h3I, h3J])
  let eRow : Fin 3 ⊕ κ ≃ ι :=
    (Equiv.sumCongr f e).trans (Equiv.sumCompl fun i => i ∈ I)
  let eCol : Fin 3 ⊕ κ ≃ ι :=
    (Equiv.sumCongr g (Equiv.refl κ)).trans (Equiv.sumCompl fun j => j ∈ J)
  obtain ⟨W, hW, hWzero⟩ := singular_of_sharedMoments (sharedMoments_on_three h hI hJ f g)
  have hz : determinantValue (a ∘ eRow ∘ Sum.inl) (b ∘ eCol ∘ Sum.inl) W = 0 := by
    simpa [c, eRow, eCol, Function.comp_def] using hWzero
  have hmem := conjecture_three (a ∘ eRow ∘ Sum.inl) (b ∘ eCol ∘ Sum.inl) W hW
  unfold Holds at hmem ⊢
  rw [hz] at hmem
  rw [hzero]
  exact zero_in_hull_of_matching_three a b eRow eCol hmem

end

end MOC
