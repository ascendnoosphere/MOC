import MOC.ProjectionLeafPivot
import MOC.ProjectionBlockSpectralLabels
import MOC.SparseRow
import MOC.Normal
import MOC.TwoValues
import Mathlib.LinearAlgebra.Matrix.Spectrum

/-! A common matching law for two overlapping two-level normal blocks. -/

open BigOperators Matrix Finset

namespace MOC

noncomputable section

/-- A fixed probability law represents every parameter of the determinant family. -/
private def MatchingLaw {n : ℕ} {θ : Type*} (a b : θ → Fin n → ℂ)
    (det : θ → ℂ) : Prop :=
  ∃ w : Equiv.Perm (Fin n) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
    ∀ x, det x = ∑ σ, (w σ : ℂ) * matchingProduct (a x) (b x) σ

private theorem MatchingLaw.pullback {n : ℕ} {θ ψ : Type*}
    {a b : θ → Fin n → ℂ} {det : θ → ℂ} (h : MatchingLaw a b det) (f : ψ → θ) :
    MatchingLaw (a ∘ f) (b ∘ f) (det ∘ f) := by
  obtain ⟨w, hw, hs, hd⟩ := h
  exact ⟨w, hw, hs, fun x => hd (f x)⟩

private theorem MatchingLaw.swap {n : ℕ} {θ : Type*}
    {a b : θ → Fin n → ℂ} {det : θ → ℂ} (h : MatchingLaw a b det) :
    MatchingLaw b a det := by
  obtain ⟨w, hw, hs, hd⟩ := h
  let e : Equiv.Perm (Equiv.Perm (Fin n)) := Equiv.inv (Equiv.Perm (Fin n))
  refine ⟨w ∘ e, fun σ => hw (e σ), (Equiv.sum_comp e w).trans hs, fun x => ?_⟩
  rw [hd x]
  conv_lhs => rw [← Equiv.sum_comp e (fun σ => (w σ : ℂ) * matchingProduct (a x) (b x) σ)]
  apply Finset.sum_congr rfl
  intro σ _
  change (w σ.symm : ℂ) * matchingProduct (a x) (b x) σ.symm =
    (w σ.symm : ℂ) * matchingProduct (b x) (a x) σ
  rw [matchingProduct_inverse]
  simp only [matchingProduct, add_comm]

private theorem MatchingLaw.extend {n : ℕ} {θ : Type*}
    {a b : θ → Fin (n + 1) → ℂ} {det : θ → ℂ} (i j : Fin (n + 1))
    (h : MatchingLaw (fun x => a x ∘ i.succAbove) (fun x => b x ∘ j.succAbove) det) :
    MatchingLaw a b (fun x => (a x i + b x j) * det x) := by
  classical
  obtain ⟨w, hw, hs, hd⟩ := h
  let f := extendSparseRowMatching i j
  let W (τ : Equiv.Perm (Fin (n + 1))) := ∑ σ, if f σ = τ then w σ else 0
  refine ⟨W, fun τ => Finset.sum_nonneg (fun σ _ => ite_nonneg (hw σ) le_rfl), ?_, ?_⟩
  · unfold W
    rw [Finset.sum_comm]
    simpa only [Finset.sum_ite_eq, Finset.mem_univ, if_true] using hs
  · intro x
    simp only [W, Complex.ofReal_sum, Finset.sum_mul]
    rw [Finset.sum_comm, hd x, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [apply_ite Complex.ofReal, Complex.ofReal_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, f, matchingProduct_extendSparseRowMatching]
    ring

private theorem MatchingLaw.mixture {n : ℕ} {θ : Type*} {a b : θ → Fin n → ℂ}
    {D E : θ → ℂ} (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hD : MatchingLaw a b D) (hE : MatchingLaw a b E) :
    MatchingLaw a b (fun x => (p : ℂ) * D x + (1 - (p : ℂ)) * E x) := by
  obtain ⟨w, hw, hsw, hDw⟩ := hD
  obtain ⟨v, hv, hsv, hEv⟩ := hE
  refine ⟨fun σ => p * w σ + (1 - p) * v σ,
    fun σ => add_nonneg (mul_nonneg hp (hw σ)) (mul_nonneg (sub_nonneg.mpr hp') (hv σ)),
    ?_, ?_⟩
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsw, hsv]
    ring
  · intro x
    change (p : ℂ) * D x + (1 - (p : ℂ)) * E x = _
    rw [hDw x, hEv x, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    push_cast
    ring

section PureProjections

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The trace specifies the multiplicity of the one eigenspace of a Hermitian
projection. Any list with that multiplicity can label its eigenbasis. -/
private theorem exists_projection_tags_diagonalization (a : ι → Bool) (P : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P)
    (ha : (∑ i, if a i = true then (1 : ℝ) else 0) = P.trace.re) :
    ∃ V, IsUnitary V ∧ P = V * diagonal (fun i => if a i then (1 : ℂ) else 0) * Vᴴ := by
  classical
  let W : Matrix ι ι ℂ := hP.eigenvectorUnitary
  have hW : IsUnitary W := ⟨Matrix.mem_unitaryGroup_iff.mp hP.eigenvectorUnitary.2,
    Matrix.mem_unitaryGroup_iff'.mp hP.eigenvectorUnitary.2⟩
  let d (i : ι) : ℂ := hP.eigenvalues i
  have hdiag : P = W * diagonal d * Wᴴ := hP.spectral_theorem
  have h01 (i : ι) : d i = 0 ∨ d i = 1 := by
    rcases projection_eigenvalues_zero_or_one hP hPP i with hi | hi <;> simp [d, hi]
  let b (i : ι) : Bool := decide (d i = 1)
  have hb (i : ι) : (if b i then (1 : ℂ) else 0) = d i := by
    rcases h01 i with hi | hi <;> simp [b, hi]
  have htr : P.trace = ∑ i, d i := by
    rw [hdiag, Matrix.trace_mul_cycle, hW.2, Matrix.one_mul, Matrix.trace_diagonal]
  have hab : (∑ i, if a i = true then (1 : ℝ) else 0) =
      ∑ i, if b i = true then (1 : ℝ) else 0 := by
    rw [ha, htr, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hb i]
    split_ifs <;> simp
  have hc (c : Bool) : Fintype.card {i // a i = c} = Fintype.card {i // b i = c} := by
    have hs (f : ι → Bool) (z : Bool) :
        (∑ i, if f i = z then (1 : ℝ) else 0) = (Fintype.card {i // f i = z} : ℝ) := by
      simp [← Finset.sum_filter, Fintype.card_subtype]
    have ht : Fintype.card {i // a i = true} = Fintype.card {i // b i = true} := by
      rw [hs a true, hs b true] at hab
      exact_mod_cast hab
    cases c
    · have hsum (f : ι → Bool) :
          Fintype.card {i // f i = false} + Fintype.card {i // f i = true} = Fintype.card ι := by
        let e : {i // f i = false} ⊕ {i // f i = true} ≃ ι :=
          (Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivRight (fun i => by cases f i <;> simp)))
            |>.trans (Equiv.sumCompl (fun i => f i = false))
        simpa only [Fintype.card_sum] using Fintype.card_congr e
      have hsa := hsum a
      have hsb := hsum b
      omega
    · exact ht
  let E (c : Bool) : {i // a i = c} ≃ {i // b i = c} := Fintype.equivOfCardEq (hc c)
  let e : Equiv.Perm ι := Equiv.ofFiberEquiv E
  have he (i : ι) : b (e i) = a i := Equiv.ofFiberEquiv_map E i
  have hde : d ∘ e = fun i => if a i then (1 : ℂ) else 0 := by
    funext i
    simp only [Function.comp_apply, ← hb (e i), he]
  let V := W.submatrix (Equiv.refl ι) e
  refine ⟨V, unitary_reindex (Equiv.refl ι) e hW, ?_⟩
  calc
    P = W * diagonal d * Wᴴ := hdiag
    _ = (W * diagonal d * Wᴴ).submatrix (Equiv.refl ι) (Equiv.refl ι) := rfl
    _ = _ := by
      rw [← Matrix.submatrix_mul_equiv _ _ (Equiv.refl ι) e (Equiv.refl ι),
        ← Matrix.submatrix_mul_equiv _ _ (Equiv.refl ι) e e,
        Matrix.submatrix_diagonal_equiv, hde, Matrix.conjTranspose_submatrix]


/-- A fixed pair of Hermitian projections and their spectral labels admit one
matching law for all scalar shifts and multiples. -/
private theorem exists_projection_pair_matching_law (a b : ι → Bool) (P Q : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (ha : (∑ i, if a i = true then (1 : ℝ) else 0) = P.trace.re)
    (hb : (∑ i, if b i = true then (1 : ℝ) else 0) = Q.trace.re) :
    ∃ w : Equiv.Perm ι → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
      ∀ s k t l : ℂ, (s • (1 : Matrix ι ι ℂ) + k • P + (t • (1 : Matrix ι ι ℂ) + l • Q)).det =
        ∑ σ, (w σ : ℂ) * matchingProduct (fun i => if a i then s + k else s)
          (fun j => if b j then t + l else t) σ := by
  classical
  obtain ⟨V, hV, hPV⟩ := exists_projection_tags_diagonalization a P hP hPP ha
  obtain ⟨W, hW, hQW⟩ := exists_projection_tags_diagonalization b Q hQ hQQ hb
  have hshape (X E : Matrix ι ι ℂ) (hX : IsUnitary X) (c : ι → Bool)
      (hE : E = X * diagonal (fun i => if c i then (1 : ℂ) else 0) * Xᴴ) (s k : ℂ) :
      s • (1 : Matrix ι ι ℂ) + k • E = X * diagonal (fun i => if c i then s + k else s) * Xᴴ := by
    let d (i : ι) := if c i then (1 : ℂ) else 0
    have hvalues : (fun i => if c i then s + k else s) =
        fun i => s + (k • d) i := by
      funext i
      by_cases hi : c i = true <;> simp [d, hi, Pi.smul_apply]
    rw [hvalues, ← Matrix.diagonal_add (fun _ : ι => s) (k • d),
      Matrix.diagonal_smul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, show X * diagonal d * Xᴴ = E from hE.symm,
      ← Matrix.smul_one_eq_diagonal,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hX.1]
  let J := (univ : Finset ι).filter (fun i => b i = true)
  obtain ⟨w, hw, hs, hd⟩ := exists_two_values_matching_law J (Vᴴ * W) (relative_unitary V W hV hW)
  refine ⟨w, hw, hs, fun s k t l => ?_⟩
  rw [hshape V P hV a hPV s k, hshape W Q hW b hQW t l, determinantValue_relative _ _ V W hV]
  simpa only [J, Finset.mem_filter, Finset.mem_univ, true_and] using
    hd (fun i => if a i then s + k else s) (t + l) t


end PureProjections

variable {κ : Type*} [DecidableEq κ]

private def SupportedOff {ι : Type*} (g : ι → Option κ) (P : Matrix ι ι ℂ) : Prop :=
  ∀ i c, g i = some c → ∀ j, P i j = 0

private def leafEquiv {n : ℕ} (i : Fin (n + 1)) : (Fin 1 ⊕ Fin n) ≃ Fin (n + 1) :=
  (Equiv.sumCongr (Equiv.ofUnique (Fin 1) Unit) (Equiv.refl (Fin n))).trans
    ((Equiv.sumComm Unit (Fin n)).trans ((Equiv.optionEquivSumPUnit (Fin n)).symm.trans (finSuccEquiv' i).symm))

private theorem leafEquiv_inl {n : ℕ} (i : Fin (n + 1)) (j : Fin 1) :
    leafEquiv i (.inl j) = i := by
  simp [leafEquiv]

private theorem leafEquiv_inr {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    leafEquiv i (.inr j) = i.succAbove j := by
  simp [leafEquiv]

private def leafColumn {n : ℕ} (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (n + 1)) : Matrix (Fin n) (Fin 1) ℂ :=
  P.submatrix i.succAbove (fun _ => i)

private def leafRest {n : ℕ} (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (n + 1)) : Matrix (Fin n) (Fin n) ℂ :=
  P.submatrix i.succAbove i.succAbove

private theorem matrix_eq_leaf_border {n : ℕ}
    {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hP : P.IsHermitian) (i : Fin (n + 1)) :
    P.submatrix (leafEquiv i) (leafEquiv i) =
      fromBlocks (scalar (Fin 1) ((P i i).re : ℂ)) (leafColumn P i)ᴴ
        (leafColumn P i) (leafRest P i) := by
  have h (j k : Fin (n + 1)) : star (P k j) = P j k := by
    exact congrFun (congrFun hP.eq j) k
  ext (j | j) (k | k) : 1
  · have hjk : j = k := Subsingleton.elim _ _
    simpa [leafEquiv_inl, scalar_apply, hjk] using
      (hP.coe_re_apply_self i).symm
  · simpa [leafEquiv_inl, leafEquiv_inr, leafColumn] using (h i (i.succAbove k)).symm
  · simp [leafEquiv_inl, leafEquiv_inr, leafColumn]
  · simp [leafEquiv_inr, leafRest]

private theorem projection_leaf_square {n : ℕ}
    {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hP : P.IsHermitian) (hPP : P * P = P)
    (i : Fin (n + 1)) :
    let R := fromBlocks (scalar (Fin 1) ((P i i).re : ℂ)) (leafColumn P i)ᴴ
      (leafColumn P i) (leafRest P i)
    R * R = R := by
  dsimp only
  rw [← matrix_eq_leaf_border hP i, Matrix.submatrix_mul_equiv P P (leafEquiv i) (leafEquiv i) (leafEquiv i), hPP]

private theorem projection_leaf_bounds {n : ℕ}
    {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hP : P.IsHermitian) (hPP : P * P = P)
    (i : Fin (n + 1)) : 0 ≤ (P i i).re ∧ (P i i).re ≤ 1 :=
  projection_border_nonneg_le_one _ _ _ (projection_leaf_square hP hPP i)

private theorem leafRest_hermitian {n : ℕ} {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hP : P.IsHermitian) (i : Fin (n + 1)) : (leafRest P i).IsHermitian := by
  rw [IsHermitian, leafRest, conjTranspose_submatrix, hP.eq]

private def conditionedLeaf {n : ℕ} (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (n + 1)) (b : Bool) : Matrix (Fin n) (Fin n) ℂ :=
  if b then projectionConditionOne (P i i).re (leafColumn P i) (leafRest P i)
  else projectionConditionZero (P i i).re (leafColumn P i) (leafRest P i)

private def leafWeight {n : ℕ} (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (n + 1)) (b : Bool) : ℝ := if b then (P i i).re else 1 - (P i i).re

private theorem conditionedLeaf_spec {n : ℕ}
    {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hP : P.IsHermitian) (hPP : P * P = P)
    (i : Fin (n + 1)) (b : Bool) (hb : leafWeight P i b ≠ 0) :
    (conditionedLeaf P i b).IsHermitian ∧
      conditionedLeaf P i b * conditionedLeaf P i b = conditionedLeaf P i b ∧
      (conditionedLeaf P i b).trace.re = P.trace.re - (if b then 1 else 0) := by
  have htrace : (P.submatrix (leafEquiv i) (leafEquiv i)).trace = P.trace := by
    exact (leafEquiv i).sum_comp (fun j => P j j)
  rw [matrix_eq_leaf_border hP] at htrace
  have hsq := projection_leaf_square hP hPP i
  have hJ := leafRest_hermitian hP i
  cases b
  · have hb' : (P i i).re ≠ 1 := by
      intro hz
      exact hb (by simp [leafWeight, hz])
    obtain ⟨h, hh, ht⟩ := projectionConditionZero_spec _ _ _ hJ hsq hb'
    simp only [conditionedLeaf, Bool.false_eq_true, ↓reduceIte, h, hh, true_and, sub_zero]
    rw [ht, htrace]
  · obtain ⟨h, hh, ht⟩ := projectionConditionOne_spec _ _ _ hJ hsq
      (by simpa [leafWeight] using hb)
    simp only [conditionedLeaf, ↓reduceIte, h, hh, true_and]
    rw [ht, htrace, Complex.sub_re, Complex.one_re]

omit [DecidableEq κ] in
private theorem conditionedLeaf_supported {n : ℕ} {g : Fin (n + 1) → Option κ}
    {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (h : SupportedOff g P)
    (i : Fin (n + 1)) (b : Bool) : SupportedOff (g ∘ i.succAbove) (conditionedLeaf P i b) := by
  intro j c hj k
  have hq : leafColumn P i j 0 = 0 := h (i.succAbove j) c hj i
  have hJ : leafRest P i j k = 0 := h (i.succAbove j) c hj (i.succAbove k)
  have houter : (leafColumn P i * (leafColumn P i)ᴴ) j k = 0 := by
    simp [Matrix.mul_apply, hq]
  cases b <;> simp [conditionedLeaf, projectionConditionOne, projectionConditionZero, hJ, houter]

private theorem label_exists_of_positive_mass {n : ℕ} {g : Fin n → Option κ}
    {P : Matrix (Fin n) (Fin n) ℂ} {a : Fin n → κ ⊕ Bool}
    (h : ProjectionBlockLabels g P a) {x : κ ⊕ Bool}
    (hp : 0 < projectionBlockMass g P x) : ∃ j, a j = x := by
  by_contra! hn
  rw [← h x] at hp
  simp [hn] at hp

private theorem leaf_level_mass_positive {n : ℕ} {g : Fin (n + 1) → Option κ}
    {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hP : P.IsHermitian) (hPP : P * P = P)
    (hg : SupportedOff g P) (i : Fin (n + 1)) (hi : g i = none) (b : Bool)
    (hb : leafWeight P i b ≠ 0) : 0 < projectionBlockMass g P (.inr b) := by
  have htrace : P.trace.re = ∑ j, (P j j).re := by
    exact Complex.re_sum _ _
  cases b
  · simp only [projectionBlockMass, htrace, ← Finset.sum_sub_distrib]
    have hnonneg (j : Fin (n + 1)) :
        0 ≤ (if g j = none then (1 : ℝ) else 0) - (P j j).re := by
      cases hj : g j with
      | none => simpa only [hj, ↓reduceIte, sub_nonneg] using (projection_leaf_bounds hP hPP j).2
      | some c => simp [hj, hg j c hj j]
    have hpos : 0 < (if g i = none then (1 : ℝ) else 0) - (P i i).re := by
      rw [if_pos hi]
      exact lt_of_le_of_ne (sub_nonneg.mpr (projection_leaf_bounds hP hPP i).2)
        (Ne.symm (by simpa [leafWeight] using hb))
    exact hpos.trans_le (Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i))
  · rw [projectionBlockMass, htrace]
    have hpos : 0 < (P i i).re := lt_of_le_of_ne (projection_leaf_bounds hP hPP i).1
      (Ne.symm (by simpa [leafWeight] using hb))
    exact hpos.trans_le (Finset.single_le_sum
      (fun j _ => (projection_leaf_bounds hP hPP j).1) (Finset.mem_univ i))

private theorem private_mass_positive {n : ℕ} {g : Fin (n + 1) → Option κ}
    {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {i : Fin (n + 1)} {c : κ}
    (hi : g i = some c) : 0 < projectionBlockMass g P (.inl c) := by
  rw [projectionBlockMass]
  have hsingle := Finset.single_le_sum (f := fun j => if g j = some c then (1 : ℝ) else 0)
    (fun j _ => ite_nonneg zero_le_one le_rfl) (Finset.mem_univ i)
  exact zero_lt_one.trans_le (by simpa only [hi, ↓reduceIte] using hsingle)

private theorem labels_of_removed_level {n : ℕ} {g : Fin (n + 1) → Option κ}
    {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {C : Matrix (Fin n) (Fin n) ℂ}
    {a : Fin (n + 1) → κ ⊕ Bool} (h : ProjectionBlockLabels g P a)
    (i j : Fin (n + 1)) (hi : g i = none) (b : Bool) (hj : a j = .inr b)
    (ht : C.trace.re = P.trace.re - (if b then 1 else 0)) :
    ProjectionBlockLabels (g ∘ i.succAbove) C (a ∘ j.succAbove) := by
  intro x
  have hc := h x
  rw [Fin.sum_univ_succAbove _ j, hj] at hc
  cases x with
  | inl c =>
    simp only [projectionBlockMass, Sum.inr_ne_inl, if_false, zero_add] at hc
    rw [Fin.sum_univ_succAbove _ i, hi] at hc
    simpa [projectionBlockMass] using hc
  | inr c =>
    have hactive := Fin.sum_univ_succAbove (fun k => if g k = none then (1 : ℝ) else 0) i
    rw [if_pos hi] at hactive
    cases c <;> cases b <;>
      simp only [projectionBlockMass, Sum.inr.injEq, Bool.false_eq_true, Bool.true_eq_false,
        ↓reduceIte, zero_add, sub_zero, Function.comp_apply] at hc ht ⊢ <;> linarith

private theorem labels_of_removed_private {n : ℕ} {g : Fin (n + 1) → Option κ}
    {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {C : Matrix (Fin n) (Fin n) ℂ}
    {a : Fin (n + 1) → κ ⊕ Bool} (h : ProjectionBlockLabels g P a)
    (i j : Fin (n + 1)) (c : κ) (hi : g i = some c) (hj : a j = .inl c)
    (ht : C.trace.re = P.trace.re) :
    ProjectionBlockLabels (g ∘ i.succAbove) C (a ∘ j.succAbove) := by
  intro x
  have hc := h x
  rw [Fin.sum_univ_succAbove _ j, hj] at hc
  cases x with
  | inl d =>
    simp only [projectionBlockMass, Sum.inl.injEq] at hc
    rw [Fin.sum_univ_succAbove _ i, hi] at hc
    simpa only [Option.some.injEq, projectionBlockMass, Function.comp_apply] using
      add_left_cancel (by simpa only [Option.some.injEq] using hc :
        (if c = d then (1 : ℝ) else 0) + ∑ k, (if a (j.succAbove k) = .inl d then 1 else 0) =
        (if c = d then (1 : ℝ) else 0) + ∑ k, (if g (i.succAbove k) = some d then 1 else 0))
  | inr b =>
    have hactive := Fin.sum_univ_succAbove (fun k => if g k = none then (1 : ℝ) else 0) i
    simp only [hi, Option.some_ne_none, if_false, zero_add] at hactive
    cases b <;>
      simp only [projectionBlockMass, Sum.inl_ne_inr, if_false, zero_add,
        Function.comp_apply] at hc ⊢ <;> linarith

omit [DecidableEq κ] in
private theorem private_leaf_column_zero {n : ℕ} {g : Fin (n + 1) → Option κ}
    {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hP : P.IsHermitian) (h : SupportedOff g P)
    {i : Fin (n + 1)} {c : κ} (hi : g i = some c) : leafColumn P i = 0 := by
  ext j k
  have he := congrFun (congrFun hP.eq (i.succAbove j)) i
  change star (P i (i.succAbove j)) = P (i.succAbove j) i at he
  change P (i.succAbove j) i = 0
  rw [← he, h i c hi, star_zero]

omit [DecidableEq κ] in
private theorem private_leaf_rest_spec {n : ℕ} {g : Fin (n + 1) → Option κ}
    {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hP : P.IsHermitian) (hPP : P * P = P)
    (h : SupportedOff g P) {i : Fin (n + 1)} {c : κ} (hi : g i = some c) :
    (leafRest P i).IsHermitian ∧ leafRest P i * leafRest P i = leafRest P i ∧
      SupportedOff (g ∘ i.succAbove) (leafRest P i) ∧
      (leafRest P i).trace.re = P.trace.re := by
  have hz := h i c hi i
  refine ⟨leafRest_hermitian hP i, ?_, fun j d hd k => h (i.succAbove j) d hd (i.succAbove k), ?_⟩
  · refine (projection_border_endpoint _ _ _ (projection_leaf_square hP hPP i) ?_).2
    exact Or.inl (by rw [hz, Complex.zero_re])
  · have ht := Fin.sum_univ_succAbove (fun j => P j j) i
    rw [hz, zero_add] at ht
    exact congrArg Complex.re ht.symm

private theorem diagonal_leaf_border {n : ℕ} (f : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    (diagonal f).submatrix (leafEquiv i) (leafEquiv i) =
      fromBlocks (scalar (Fin 1) (f i)) 0 0 (diagonal (f ∘ i.succAbove)) := by
  rw [submatrix_diagonal_equiv, scalar_apply, fromBlocks_diagonal]
  apply congrArg Matrix.diagonal
  funext j
  rcases j with j | j
  · exact congrArg f (leafEquiv_inl i j)
  · exact congrArg f (leafEquiv_inr i j)

private def blockDeviation {ι : Type*} [DecidableEq ι] (g : ι → Option κ) (d : κ → ℂ)
    (s : ℂ) : Matrix ι ι ℂ :=
  diagonal (fun i => (g i).elim s d - s)

omit [DecidableEq κ] in
private theorem projectionBlockMatrix_eq {ι : Type*} [DecidableEq ι] (g : ι → Option κ)
    (P : Matrix ι ι ℂ) (d : κ → ℂ) (s k : ℂ) :
    projectionBlockMatrix g P d s k = s • (1 : Matrix ι ι ℂ) + k • P + blockDeviation g d s := by
  have hdiag : diagonal (fun i => (g i).elim s d) =
      s • (1 : Matrix ι ι ℂ) + blockDeviation g d s := by
    rw [smul_one_eq_diagonal, blockDeviation, diagonal_add]
    apply congrArg Matrix.diagonal
    funext i
    change (g i).elim s d = s + ((g i).elim s d - s)
    abel
  rw [projectionBlockMatrix, hdiag, add_right_comm]

omit [DecidableEq κ] in
private theorem private_block_leaf_border {n : ℕ} {g : Fin (n + 1) → Option κ}
    {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hP : P.IsHermitian) (h : SupportedOff g P)
    {i : Fin (n + 1)} {c : κ} (hi : g i = some c) (d : κ → ℂ) (s k : ℂ) :
    (projectionBlockMatrix g P d s k).submatrix (leafEquiv i) (leafEquiv i) =
      fromBlocks (scalar (Fin 1) (d c)) 0 0
        (projectionBlockMatrix (g ∘ i.succAbove) (leafRest P i) d s k) := by
  let E := leafEquiv i
  change (diagonal (fun j => (g j).elim s d)).submatrix E E + k • P.submatrix E E = _
  rw [diagonal_leaf_border, matrix_eq_leaf_border hP, private_leaf_column_zero hP h hi,
    h i c hi i, hi]
  simp only [projectionBlockMatrix, fromBlocks_add, fromBlocks_smul, Option.elim_some,
    Complex.zero_re, Complex.ofReal_zero, map_zero, conjTranspose_zero, smul_zero, add_zero]
  rfl

omit [DecidableEq κ] in
private theorem active_deviation_leaf_border {n : ℕ} {g : Fin (n + 1) → Option κ}
    {i : Fin (n + 1)} (hi : g i = none) (d : κ → ℂ) (s : ℂ) :
    (blockDeviation g d s).submatrix (leafEquiv i) (leafEquiv i) =
      fromBlocks 0 0 0 (blockDeviation (g ∘ i.succAbove) d s) := by
  rw [blockDeviation, diagonal_leaf_border, hi]
  simp only [Option.elim_none, sub_self, map_zero]
  rfl

omit [DecidableEq κ] in
private theorem det_projection_blocks_delete_leaf {n : ℕ}
    {g h : Fin (n + 1) → Option κ} {P Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (hQ : Q.IsHermitian) (hQs : SupportedOff h Q)
    {i : Fin (n + 1)} (hi : g i = none) {c : κ} (hc : h i = some c)
    (d e : κ → ℂ) (s k t l : ℂ) :
    (projectionBlockMatrix g P d s k + projectionBlockMatrix h Q e t l).det =
      ∑ b : Bool, (leafWeight P i b : ℂ) * ((projectionBlockValue d s k (.inr b) + e c) *
        (projectionBlockMatrix (g ∘ i.succAbove) (conditionedLeaf P i b) d s k +
          projectionBlockMatrix (h ∘ i.succAbove) (leafRest Q i) e t l).det) := by
  let A := blockDeviation (g ∘ i.succAbove) d s
  let B := projectionBlockMatrix (h ∘ i.succAbove) (leafRest Q i) e t l
  let E := leafEquiv i
  rw [← Matrix.det_submatrix_equiv_self E, projectionBlockMatrix_eq g]
  change (s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).submatrix E E +
    k • P.submatrix E E + (blockDeviation g d s).submatrix E E +
    (projectionBlockMatrix h Q e t l).submatrix E E).det = _
  rw [Matrix.submatrix_one_equiv, matrix_eq_leaf_border hP, active_deviation_leaf_border hi,
    private_block_leaf_border hQ hQs hc]
  change (_ + _ + fromBlocks 0 0 0 A + fromBlocks (scalar (Fin 1) (e c)) 0 0 B).det = _
  rw [add_assoc (_ + _), fromBlocks_add, zero_add, zero_add, zero_add]
  rw [det_sum_projection_leaf s k (e c) _ _ _ (A + B) (projection_leaf_square hP hPP i)]
  rw [Fintype.sum_bool]
  simp only [conditionedLeaf, leafWeight, projectionBlockValue, Bool.false_eq_true,
    ↓reduceIte, Complex.ofReal_sub, Complex.ofReal_one]
  simp only [projectionBlockMatrix_eq (g ∘ i.succAbove)]
  change _ = (_ * (_ * ((_ + _ + A + B).det))) + (_ * (_ * ((_ + _ + A + B).det)))
  simp only [add_assoc, mul_assoc]

/-- The private values, the lower level, and the increment to the upper level. -/
private structure ProjectionBlockParameters (κ : Type*) where
  privateValue : κ → ℂ
  lower : ℂ
  increment : ℂ

private def blockSpectrum {n : ℕ} (a : Fin n → κ ⊕ Bool)
    (x : ProjectionBlockParameters κ) : Fin n → ℂ :=
  projectionBlockValue x.privateValue x.lower x.increment ∘ a

private def blockAt {n : ℕ} (g : Fin n → Option κ) (P : Matrix (Fin n) (Fin n) ℂ)
    (x : ProjectionBlockParameters κ) : Matrix (Fin n) (Fin n) ℂ :=
  projectionBlockMatrix g P x.privateValue x.lower x.increment

private def ProjectionBlocksLaw {n : ℕ} (g h : Fin n → Option κ)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → κ ⊕ Bool) : Prop :=
  MatchingLaw (fun x : ProjectionBlockParameters κ × ProjectionBlockParameters κ =>
      blockSpectrum a x.1) (fun x => blockSpectrum b x.2)
    (fun x => (blockAt g P x.1 + blockAt h Q x.2).det)

omit [DecidableEq κ] in
private theorem ProjectionBlocksLaw.swap {n : ℕ} {g h : Fin n → Option κ}
    {P Q : Matrix (Fin n) (Fin n) ℂ} {a b : Fin n → κ ⊕ Bool}
    (hW : ProjectionBlocksLaw g h P Q a b) : ProjectionBlocksLaw h g Q P b a := by
  have h := MatchingLaw.pullback (MatchingLaw.swap hW) (Prod.swap :
    ProjectionBlockParameters κ × ProjectionBlockParameters κ → _)
  simpa only [ProjectionBlocksLaw, Function.comp_apply, Prod.swap,
    add_comm] using h

private theorem MatchingLaw.of_bool_mixture {n : ℕ} {θ : Type*} {a b : θ → Fin n → ℂ}
    {D : Bool → θ → ℂ} (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hD : ∀ u : Bool, (if u then p else 1 - p) ≠ 0 → MatchingLaw a b (D u)) :
    MatchingLaw a b (fun x => ∑ u : Bool, ((if u then p else 1 - p : ℝ) : ℂ) * D u x) := by
  by_cases hz : p = 0
  · simpa [Fintype.sum_bool, hz] using hD false (by simp [hz])
  by_cases ho : p = 1
  · simpa [Fintype.sum_bool, ho] using hD true (by simp [ho])
  simpa [Fintype.sum_bool, add_comm] using
    MatchingLaw.mixture p hp hp' (hD true (by simpa using hz))
      (hD false (sub_ne_zero.mpr (Ne.symm ho)))

private def ProjectionBlocksProblem (n : ℕ) : Prop :=
  ∀ (g h : Fin n → Option κ) (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → κ ⊕ Bool),
    P.IsHermitian → P * P = P → Q.IsHermitian → Q * Q = Q →
    SupportedOff g P → SupportedOff h Q → (∀ i, g i = none ∨ h i = none) →
    ProjectionBlockLabels g P a → ProjectionBlockLabels h Q b → ProjectionBlocksLaw g h P Q a b

private theorem laws_of_private_leaf {n : ℕ} (ih : ProjectionBlocksProblem (κ := κ) n)
    {g h : Fin (n + 1) → Option κ} {P Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {a b : Fin (n + 1) → κ ⊕ Bool}
    (hP : P.IsHermitian) (hPP : P * P = P) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (hPs : SupportedOff g P) (hQs : SupportedOff h Q) (hd : ∀ j, g j = none ∨ h j = none)
    (ha : ProjectionBlockLabels g P a) (hb : ProjectionBlockLabels h Q b)
    {i : Fin (n + 1)} {c : κ} (hc : h i = some c) :
    ProjectionBlocksLaw g h P Q a b := by
  have hi : g i = none := (hd i).resolve_right (by rw [hc]; exact Option.some_ne_none _)
  obtain ⟨v, hv⟩ := label_exists_of_positive_mass hb (private_mass_positive hc)
  obtain ⟨hR, hRR, hRs, hRt⟩ := private_leaf_rest_spec hQ hQQ hQs hc
  have hb' := labels_of_removed_private hb i v c hc hv hRt
  let D (u : Bool) (x : ProjectionBlockParameters κ × ProjectionBlockParameters κ) :=
    (projectionBlockValue x.1.privateValue x.1.lower x.1.increment (.inr u) + x.2.privateValue c) *
      (blockAt (g ∘ i.succAbove) (conditionedLeaf P i u) x.1 +
        blockAt (h ∘ i.succAbove) (leafRest Q i) x.2).det
  have hchild (u : Bool) (hu : leafWeight P i u ≠ 0) :
      MatchingLaw (fun x => blockSpectrum a x.1) (fun x => blockSpectrum b x.2) (D u) := by
    obtain ⟨j, hj⟩ := label_exists_of_positive_mass ha (leaf_level_mass_positive hP hPP hPs i hi u hu)
    obtain ⟨hC, hCC, hCt⟩ := conditionedLeaf_spec hP hPP i u hu
    have hsub := ih (g ∘ i.succAbove) (h ∘ i.succAbove) (conditionedLeaf P i u) (leafRest Q i)
      (a ∘ j.succAbove) (b ∘ v.succAbove) hC hCC hR hRR (conditionedLeaf_supported hPs i u) hRs
      (fun k => hd (i.succAbove k)) (labels_of_removed_level ha i j hi u hj hCt) hb'
    have hext := MatchingLaw.extend
      (a := fun x : ProjectionBlockParameters κ × ProjectionBlockParameters κ => blockSpectrum a x.1)
      (b := fun x => blockSpectrum b x.2)
      (det := fun x => (blockAt (g ∘ i.succAbove) (conditionedLeaf P i u) x.1 +
        blockAt (h ∘ i.succAbove) (leafRest Q i) x.2).det) j v hsub
    simpa only [D, blockSpectrum, Function.comp_apply, hj, hv, projectionBlockValue] using hext
  have hp := projection_leaf_bounds hP hPP i
  have hsum := MatchingLaw.of_bool_mixture (P i i).re hp.1 hp.2 hchild
  have heq :
      (fun x : ProjectionBlockParameters κ × ProjectionBlockParameters κ =>
        (blockAt g P x.1 + blockAt h Q x.2).det) =
        (fun x => ∑ u : Bool, ((leafWeight P i u : ℝ) : ℂ) * D u x) := by
    funext x
    exact det_projection_blocks_delete_leaf hP hPP hQ hQs hi hc
      x.1.privateValue x.2.privateValue x.1.lower x.1.increment x.2.lower x.2.increment
  unfold ProjectionBlocksLaw
  rw [heq]
  exact hsum

private theorem labels_of_no_private {n : ℕ} {g : Fin n → Option κ}
    {P : Matrix (Fin n) (Fin n) ℂ} {a : Fin n → κ ⊕ Bool}
    (ha : ProjectionBlockLabels g P a) (hg : ∀ i, g i = none) :
    ∃ A : Fin n → Bool, (∀ i, a i = .inr (A i)) ∧
      (∑ i, if A i = true then (1 : ℝ) else 0) = P.trace.re := by
  let A := Sum.elim (fun _ : κ => false) id ∘ a
  have hA (i : Fin n) : a i = .inr (A i) := by
    cases hi : a i with
    | inr p => simp [A, hi]
    | inl c =>
      exfalso
      have he : (∑ j, if a j = Sum.inl c then (1 : ℝ) else 0) = 0 := by
        simpa [projectionBlockMass, hg] using ha (.inl c)
      have hle : (if a i = Sum.inl c then (1 : ℝ) else 0) ≤
          ∑ j, if a j = Sum.inl c then (1 : ℝ) else 0 :=
        Finset.single_le_sum (f := fun j => if a j = Sum.inl c then (1 : ℝ) else 0)
          (fun j _ => ite_nonneg zero_le_one le_rfl) (Finset.mem_univ i)
      rw [hi, if_pos rfl, he] at hle
      exact (not_le_of_gt zero_lt_one) hle
  refine ⟨A, hA, ?_⟩
  simpa only [hA, Sum.inr.injEq, projectionBlockMass] using ha (.inr true)

private theorem laws_without_private {n : ℕ} {g h : Fin n → Option κ}
    {P Q : Matrix (Fin n) (Fin n) ℂ} {a b : Fin n → κ ⊕ Bool}
    (hP : P.IsHermitian) (hPP : P * P = P) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (hg : ∀ i, g i = none) (hh : ∀ i, h i = none)
    (ha : ProjectionBlockLabels g P a) (hb : ProjectionBlockLabels h Q b) :
    ProjectionBlocksLaw g h P Q a b := by
  obtain ⟨A, hA, hAc⟩ := labels_of_no_private ha hg
  obtain ⟨B, hB, hBc⟩ := labels_of_no_private hb hh
  obtain ⟨w, hw, hs, he⟩ := exists_projection_pair_matching_law A B P Q hP hPP hQ hQQ hAc hBc
  refine ⟨w, hw, hs, fun x => ?_⟩
  have ha' : blockSpectrum a x.1 = fun i => if A i then x.1.lower + x.1.increment else x.1.lower := by
    funext i
    simp only [blockSpectrum, Function.comp_apply, hA i, projectionBlockValue]
  have hb' : blockSpectrum b x.2 = fun i => if B i then x.2.lower + x.2.increment else x.2.lower := by
    funext i
    simp only [blockSpectrum, Function.comp_apply, hB i, projectionBlockValue]
  change (blockAt g P x.1 + blockAt h Q x.2).det =
    ∑ σ, (w σ : ℂ) * matchingProduct (blockSpectrum a x.1) (blockSpectrum b x.2) σ
  rw [ha', hb']
  simp only [blockAt, projectionBlockMatrix, hg, hh, Option.elim_none,
    ← Matrix.smul_one_eq_diagonal]
  exact he x.1.lower x.1.increment x.2.lower x.2.increment

private theorem projectionBlocksProblem (n : ℕ) : ProjectionBlocksProblem (κ := κ) n := by
  induction n with
  | zero =>
    intro g h P Q a b hP hPP hQ hQQ hPs hQs hd ha hb
    exact laws_without_private hP hPP hQ hQQ (fun i => Fin.elim0 i)
      (fun i => Fin.elim0 i) ha hb
  | succ n ih =>
    intro g h P Q a b hP hPP hQ hQQ hPs hQs hd ha hb
    by_cases hpriv : ∃ i c, h i = some c
    · obtain ⟨i, c, hc⟩ := hpriv
      exact laws_of_private_leaf ih hP hPP hQ hQQ hPs hQs hd ha hb hc
    by_cases gpriv : ∃ i c, g i = some c
    · obtain ⟨i, c, hc⟩ := gpriv
      exact (laws_of_private_leaf ih hQ hQQ hP hPP hQs hPs
        (fun j => (hd j).symm) hb ha hc).swap
    have hh (i : Fin (n + 1)) : h i = none := by
      cases he : h i with
      | none => rfl
      | some c => exact (hpriv ⟨i, c, he⟩).elim
    have hg (i : Fin (n + 1)) : g i = none := by
      cases he : g i with
      | none => rfl
      | some c => exact (gpriv ⟨i, c, he⟩).elim
    exact laws_without_private hP hPP hQ hQQ hg hh ha hb

/-- Two projection blocks with disjoint private coordinate sets admit one
probability law for every complex choice of the four level parameters and
every choice of the private diagonal values. -/
theorem overlapping_projection_blocks_matching_law {n : ℕ}
    (g h : Fin n → Option κ) (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → κ ⊕ Bool)
    (hP : P.IsHermitian) (hPP : P * P = P) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (hPs : ∀ i c, g i = some c → ∀ j, P i j = 0)
    (hQs : ∀ i c, h i = some c → ∀ j, Q i j = 0)
    (hd : ∀ i, g i = none ∨ h i = none)
    (ha : ProjectionBlockLabels g P a) (hb : ProjectionBlockLabels h Q b) :
    ∃ w : Equiv.Perm (Fin n) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
      ∀ (d e : κ → ℂ) (s k t l : ℂ),
        (projectionBlockMatrix g P d s k + projectionBlockMatrix h Q e t l).det =
          ∑ σ, (w σ : ℂ) * matchingProduct (projectionBlockValue d s k ∘ a)
            (projectionBlockValue e t l ∘ b) σ := by
  obtain ⟨w, hw, hs, hv⟩ := projectionBlocksProblem n g h P Q a b hP hPP hQ hQQ hPs hQs hd ha hb
  exact ⟨w, hw, hs, fun d e s k t l => hv (⟨d, s, k⟩, ⟨e, t, l⟩)⟩

/-- The determinant of the sum lies in the convex hull of eigenvalue
matching products for two overlapping two-level blocks. -/
theorem overlapping_projection_blocks_det_mem_convexHull {n : ℕ}
    (g h : Fin n → Option κ) (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → κ ⊕ Bool)
    (hP : P.IsHermitian) (hPP : P * P = P) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (hPs : ∀ i c, g i = some c → ∀ j, P i j = 0)
    (hQs : ∀ i c, h i = some c → ∀ j, Q i j = 0)
    (hd : ∀ i, g i = none ∨ h i = none)
    (ha : ProjectionBlockLabels g P a) (hb : ProjectionBlockLabels h Q b)
    (d e : κ → ℂ) (s k t l : ℂ) :
    (projectionBlockMatrix g P d s k + projectionBlockMatrix h Q e t l).det ∈ convexHull ℝ
      (Set.range (matchingProduct (projectionBlockValue d s k ∘ a)
        (projectionBlockValue e t l ∘ b))) := by
  obtain ⟨w, hw, hs, he⟩ :=
    overlapping_projection_blocks_matching_law g h P Q a b hP hPP hQ hQQ hPs hQs hd ha hb
  refine mem_convexHull_of_exists_fintype w _ hw hs (fun σ => ⟨σ, rfl⟩) ?_
  simpa only [Complex.real_smul] using (he d e s k t l).symm

/-- Determinant inclusion holds for two overlapping projection blocks and any
enumeration of the two spectra with algebraic multiplicity. -/
theorem overlapping_projection_blocks_inclusion {n : ℕ}
    (g h : Fin n → Option κ) (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (hPs : ∀ i c, g i = some c → ∀ j, P i j = 0)
    (hQs : ∀ i c, h i = some c → ∀ j, Q i j = 0)
    (hd : ∀ i, g i = none ∨ h i = none)
    (d e : κ → ℂ) (s k t l : ℂ) (a b : Fin n → ℂ)
    (ha : (projectionBlockMatrix g P d s k).charpoly.roots =
      (Finset.univ : Finset (Fin n)).val.map a)
    (hb : (projectionBlockMatrix h Q e t l).charpoly.roots =
      (Finset.univ : Finset (Fin n)).val.map b) :
    (projectionBlockMatrix g P d s k + projectionBlockMatrix h Q e t l).det ∈ convexHull ℝ
      (Set.range (matchingProduct a b)) := by
  obtain ⟨a', V, hA, hV, hAV⟩ := exists_projection_block_spectral_labels g P hP hPP hPs
  obtain ⟨b', W, hB, hW, hBW⟩ := exists_projection_block_spectral_labels h Q hQ hQQ hQs
  have har := ha
  have hbr := hb
  rw [hAV d s k, roots_unitary_diagonalization _ hV] at har
  rw [hBW e t l, roots_unitary_diagonalization _ hW] at hbr
  obtain ⟨σ, rfl⟩ := exists_perm_of_equal_multisets _ _ har.symm
  obtain ⟨τ, rfl⟩ := exists_perm_of_equal_multisets _ _ hbr.symm
  rw [matchingRange_relabel]
  exact overlapping_projection_blocks_det_mem_convexHull g h P Q a' b'
    hP hPP hQ hQQ hPs hQs hd hA hB d e s k t l

end

end MOC
