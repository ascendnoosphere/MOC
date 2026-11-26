import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The plane geometry and coordinate identities for the order-five
Grassmannian lift. -/

open BigOperators
open Matrix

namespace MOC

/-- Pairwise intersecting two-dimensional subspaces either contain one
common line or lie in a common space of dimension at most three. -/
theorem intersecting_planes_common_line_or_three_space
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (planes : Set (Submodule ℂ V)) (hdim : ∀ P ∈ planes, Module.finrank ℂ P = 2)
    (hmeet : ∀ P ∈ planes, ∀ Q ∈ planes, P ⊓ Q ≠ ⊥) :
    (∃ L : Submodule ℂ V, Module.finrank ℂ L = 1 ∧ ∀ P ∈ planes, L ≤ P) ∨
      (∃ H : Submodule ℂ V, Module.finrank ℂ H ≤ 3 ∧ ∀ P ∈ planes, P ≤ H) := by
  classical
  by_cases hpair : ∃ P ∈ planes, ∃ Q ∈ planes, P ≠ Q
  · obtain ⟨P, hP, Q, hQ, hpq⟩ := hpair
    let L := P ⊓ Q
    let H := P ⊔ Q
    have hp := hdim P hP
    have hq := hdim Q hQ
    have hLone : 1 ≤ Module.finrank ℂ L :=
      Submodule.one_le_finrank_iff.mpr (hmeet P hP Q hQ)
    have hLle : Module.finrank ℂ L ≤ 2 := by
      simpa only [hp] using Submodule.finrank_mono (inf_le_left : L ≤ P)
    have hLne : Module.finrank ℂ L ≠ 2 := by
      intro he
      have hLP : L = P := Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
      have hLQ : L = Q := Submodule.eq_of_le_of_finrank_le inf_le_right (by omega)
      exact hpq (hLP.symm.trans hLQ)
    have hL : Module.finrank ℂ L = 1 := by omega
    have hH : Module.finrank ℂ H = 3 := by
      have he : Module.finrank ℂ H + Module.finrank ℂ L =
          Module.finrank ℂ P + Module.finrank ℂ Q := Submodule.finrank_sup_add_finrank_inf_eq P Q
      omega
    by_cases hall : ∀ C ∈ planes, L ≤ C
    · exact Or.inl ⟨L, hL, hall⟩
    · push_neg at hall
      obtain ⟨D, hD, hLD⟩ := hall
      have missing_line_le_H (C : Submodule ℂ V) (hC : C ∈ planes) (hLC : ¬ L ≤ C) : C ≤ H := by
        let E := C ⊓ P
        let F := C ⊓ Q
        have hE : 1 ≤ Module.finrank ℂ E := Submodule.one_le_finrank_iff.mpr (hmeet C hC P hP)
        have hF : 1 ≤ Module.finrank ℂ F := Submodule.one_le_finrank_iff.mpr (hmeet C hC Q hQ)
        have hEF_L : E ⊓ F ≤ L := le_inf (inf_le_left.trans inf_le_right)
          (inf_le_right.trans inf_le_right)
        have hEF_C : E ⊓ F ≤ C := inf_le_left.trans inf_le_left
        have hEF : Module.finrank ℂ (E ⊓ F) = 0 := by
          by_contra hn
          have heq : E ⊓ F = L := Submodule.eq_of_le_of_finrank_le hEF_L (by omega)
          exact hLC (heq ▸ hEF_C)
        have hsup := Submodule.finrank_sup_add_finrank_inf_eq E F
        have heq : E ⊔ F = C := Submodule.eq_of_le_of_finrank_le
          (sup_le inf_le_left inf_le_left) (by have hc := hdim C hC; omega)
        rw [← heq]
        exact sup_le (inf_le_right.trans le_sup_left) (inf_le_right.trans le_sup_right)
      have hDH := missing_line_le_H D hD hLD
      refine Or.inr ⟨H, hH.le, ?_⟩
      intro C hC
      by_cases hLC : L ≤ C
      · by_contra hCH
        have hLI : L ≤ C ⊓ H := le_inf hLC (inf_le_left.trans le_sup_left)
        have hIC : C ⊓ H ≤ C := inf_le_left
        have hIle : Module.finrank ℂ (C ⊓ H) ≤ 2 := by
          simpa only [hdim C hC] using Submodule.finrank_mono hIC
        have hIne : Module.finrank ℂ (C ⊓ H) ≠ 2 := by
          intro he
          have heq : C ⊓ H = C := Submodule.eq_of_le_of_finrank_le hIC (by rw [he, hdim C hC])
          exact hCH (heq ▸ (inf_le_right : C ⊓ H ≤ H))
        have hI : L = C ⊓ H := Submodule.eq_of_le_of_finrank_le hLI (by omega)
        have hDL : C ⊓ D ≤ L := by
          rw [hI]
          exact le_inf inf_le_left (inf_le_right.trans hDH)
        have hCD : 1 ≤ Module.finrank ℂ (C ⊓ D) :=
          Submodule.one_le_finrank_iff.mpr (hmeet C hC D hD)
        have heq : C ⊓ D = L := Submodule.eq_of_le_of_finrank_le hDL (by omega)
        exact hLD (heq ▸ (inf_le_right : C ⊓ D ≤ D))
      · exact missing_line_le_H C hC hLC
  · by_cases hn : ∃ P ∈ planes
    · obtain ⟨P, hP⟩ := hn
      refine Or.inr ⟨P, by rw [hdim P hP]; decide, fun Q hQ => ?_⟩
      have he : P = Q := by
        by_contra hne
        exact hpair ⟨P, hP, Q, hQ, hne⟩
      rw [he]
    · exact Or.inr ⟨⊥, by simp, fun P hP => (hn ⟨P, hP⟩).elim⟩

/-- The skew coordinate matrix of the exterior product of two vectors. -/
def bivectorMatrix {ι R : Type*} [CommRing R] (x y : ι → R) : Matrix ι ι R :=
  fun i j => x i * y j - y i * x j

/-- The equations for the cone of decomposable bivectors. -/
def PluckerBivector {ι R : Type*} [CommRing R] (A : Matrix ι ι R) : Prop :=
  (∀ i j, A j i = -A i j) ∧
    ∀ p q i j, A p q * A i j - A p i * A q j + A p j * A q i = 0

/-- The Plücker equations express decomposability, including at zero. -/
theorem pluckerBivector_iff_decomposable {ι K : Type*} [Field K] (A : Matrix ι ι K) :
    PluckerBivector A ↔ ∃ x y : ι → K, A = bivectorMatrix x y := by
  classical
  constructor
  · rintro ⟨hskew, hplucker⟩
    by_cases hA : A = 0
    · refine ⟨0, 0, ?_⟩
      ext i j
      simp [hA, bivectorMatrix]
    · obtain ⟨p, q, hpq⟩ : ∃ p q, A p q ≠ 0 := by
        by_contra! h
        exact hA (Matrix.ext h)
      refine ⟨fun i => A i q, fun i => A p i / A p q, ?_⟩
      ext i j
      have he := hplucker p q i j
      rw [hskew j q, hskew i q] at he
      calc
        A i j = (A i q * A p j - A p i * A j q) / A p q :=
          (eq_div_iff hpq).2 (by linear_combination he)
        _ = _ := by simp only [bivectorMatrix]; ring
  · rintro ⟨x, y, rfl⟩
    constructor
    · intro i j
      simp only [bivectorMatrix]
      ring
    · intro p q i j
      simp only [bivectorMatrix]
      ring

section Carrier

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The carrier is the range of the skew matrix on coordinate vectors. -/
def bivectorCarrier (A : Matrix ι ι ℂ) : Submodule ℂ (ι → ℂ) :=
  LinearMap.range A.mulVecLin

private theorem bivectorMatrix_mulVec (x y v : ι → ℂ) :
    bivectorMatrix x y *ᵥ v = (y ⬝ᵥ v) • x - (x ⬝ᵥ v) • y := by
  ext i
  simp only [Matrix.mulVec, dotProduct, bivectorMatrix, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  ring

/-- A nonzero decomposable bivector determines the span of its factors. -/
theorem bivectorCarrier_matrix_eq_span (x y : ι → ℂ) (h : bivectorMatrix x y ≠ 0) :
    bivectorCarrier (bivectorMatrix x y) = Submodule.span ℂ ({x, y} : Set (ι → ℂ)) := by
  classical
  let A := bivectorMatrix x y
  obtain ⟨p, q, hpq⟩ : ∃ p q, A p q ≠ 0 := by
    by_contra! hn
    exact h (Matrix.ext hn)
  have hc (j : ι) : (fun i => A i j) ∈ bivectorCarrier A := by
    refine ⟨Pi.single j 1, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] <;> rfl
  have hx : x ∈ bivectorCarrier A := by
    have he : (x p / A p q) • (fun i => A i q) - (x q / A p q) • (fun i => A i p) = x := by
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [hpq]
      simp only [A, bivectorMatrix]
      ring
    rw [← he]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (hc q)) (Submodule.smul_mem _ _ (hc p))
  have hy : y ∈ bivectorCarrier A := by
    have he : (y p / A p q) • (fun i => A i q) - (y q / A p q) • (fun i => A i p) = y := by
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [hpq]
      simp only [A, bivectorMatrix]
      ring
    rw [← he]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (hc q)) (Submodule.smul_mem _ _ (hc p))
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [Matrix.mulVecLin_apply, bivectorMatrix_mulVec]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · have he : {x, y} ⊆ (bivectorCarrier A : Set (ι → ℂ)) := by
      intro z hz
      rcases (show z = x ∨ z = y by simpa using hz) with rfl | rfl
      · exact hx
      · exact hy
    exact Submodule.span_le.2 he

/-- Nonzero decomposable bivectors have two-dimensional carriers. -/
theorem bivectorCarrier_finrank {A : Matrix ι ι ℂ} (hA : PluckerBivector A) (hn : A ≠ 0) :
    Module.finrank ℂ (bivectorCarrier A) = 2 := by
  obtain ⟨x, y, rfl⟩ := (pluckerBivector_iff_decomposable A).mp hA
  have hi : LinearIndependent ℂ (![x, y] : Fin 2 → (ι → ℂ)) := by
    rw [linearIndependent_fin2]
    refine ⟨?_, ?_⟩
    · intro hy
      apply hn
      have hz : y = 0 := hy
      subst y
      ext i j
      simp [bivectorMatrix]
    · intro c hc
      have he : c • y = x := hc
      rw [← he] at hn
      apply hn
      ext i j
      simp only [bivectorMatrix, Matrix.zero_apply, Pi.smul_apply, smul_eq_mul]
      ring
  have hr : Set.range (![x, y] : Fin 2 → (ι → ℂ)) = {x, y} := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hz
      rcases (show z = x ∨ z = y by simpa using hz) with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [bivectorCarrier_matrix_eq_span x y hn, ← hr, finrank_span_eq_card hi, Fintype.card_fin]

/-- Any nonzero vector in the carrier of a nonzero decomposable bivector
can serve as its first factor. -/
theorem exists_bivector_factor_of_mem_carrier {A : Matrix ι ι ℂ}
    (hA : PluckerBivector A) (ha : A ≠ 0) (z : ι → ℂ)
    (hz : z ∈ bivectorCarrier A) (hzn : z ≠ 0) :
    ∃ w : ι → ℂ, A = bivectorMatrix z w := by
  obtain ⟨x, y, rfl⟩ := (pluckerBivector_iff_decomposable A).mp hA
  rw [bivectorCarrier_matrix_eq_span x y ha] at hz
  obtain ⟨c, d, he⟩ := Submodule.mem_span_pair.mp hz
  by_cases hc : c = 0
  · have hd : d ≠ 0 := by
      intro hd
      apply hzn
      simpa [hc, hd] using he.symm
    refine ⟨-(d⁻¹ • x), ?_⟩
    rw [← he, hc, zero_smul, zero_add]
    ext i j
    simp only [bivectorMatrix, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hd] <;> ring
  · refine ⟨c⁻¹ • y, ?_⟩
    rw [← he]
    ext i j
    simp only [bivectorMatrix, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hc] <;> ring

/-- The carriers of two nonzero decomposable bivectors meet if their sum
is decomposable. Disjoint carriers would make the sum have rank four. -/
theorem bivectorCarrier_inf_ne_bot {A B : Matrix ι ι ℂ}
    (hA : PluckerBivector A) (hB : PluckerBivector B) (hAB : PluckerBivector (A + B))
    (ha : A ≠ 0) (hb : B ≠ 0) : bivectorCarrier A ⊓ bivectorCarrier B ≠ ⊥ := by
  intro hdisj
  have htA : Aᵀ = -A := by ext i j; exact hA.1 i j
  have htB : Bᵀ = -B := by ext i j; exact hB.1 i j
  let S := Matrix.fromRows A B
  have hker : LinearMap.ker (A + B).mulVecLin = LinearMap.ker S.mulVecLin := by
    ext v
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.add_mulVec, S, Matrix.fromRows_mulVec]
    constructor
    · intro h
      have he : A *ᵥ v = -(B *ᵥ v) := eq_neg_iff_add_eq_zero.mpr h
      have hmem : A *ᵥ v ∈ bivectorCarrier A ⊓ bivectorCarrier B :=
        ⟨⟨v, rfl⟩, he.symm ▸ Submodule.neg_mem (bivectorCarrier B) ⟨v, rfl⟩⟩
      rw [hdisj, Submodule.mem_bot] at hmem
      have hz : B *ᵥ v = 0 := by simpa only [hmem, zero_add] using h
      funext i
      cases i <;> simp [hmem, hz]
    · intro h
      have h₁ : A *ᵥ v = 0 := funext (fun i => congrFun h (Sum.inl i))
      have h₂ : B *ᵥ v = 0 := funext (fun i => congrFun h (Sum.inr i))
      rw [h₁, h₂, add_zero]
  have hrange : LinearMap.range (Sᵀ).mulVecLin = bivectorCarrier A ⊔ bivectorCarrier B := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      let u (i : ι) := v (.inl i)
      let w (i : ι) := v (.inr i)
      have hv : v = Sum.elim u w := by funext i; cases i <;> rfl
      rw [Matrix.mulVecLin_apply, hv, S, Matrix.transpose_fromRows,
        Matrix.fromCols_mulVec_sumElim, htA, htB, Matrix.neg_mulVec, Matrix.neg_mulVec]
      exact Submodule.add_mem_sup
        (Submodule.neg_mem (bivectorCarrier A) ⟨u, rfl⟩)
        (Submodule.neg_mem (bivectorCarrier B) ⟨w, rfl⟩)
    · rw [sup_le_iff]
      constructor
      · rintro _ ⟨v, rfl⟩
        refine ⟨Sum.elim (-v) 0, ?_⟩
        simp [S, Matrix.transpose_fromRows, htA, htB, Matrix.mulVecLin_apply, Matrix.neg_mulVec_neg]
      · rintro _ ⟨v, rfl⟩
        refine ⟨Sum.elim 0 (-v), ?_⟩
        simp [S, Matrix.transpose_fromRows, htA, htB, Matrix.mulVecLin_apply, Matrix.neg_mulVec_neg]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (bivectorCarrier A) (bivectorCarrier B)
  rw [hdisj, finrank_bot, add_zero, bivectorCarrier_finrank hA ha,
    bivectorCarrier_finrank hB hb] at hdim
  have hS : S.rank = 4 := by
    rw [← Matrix.rank_transpose S]
    change Module.finrank ℂ (LinearMap.range (Sᵀ).mulVecLin) = 4
    rw [hrange]
    exact hdim
  have h₁ := LinearMap.finrank_range_add_finrank_ker (A + B).mulVecLin
  have h₂ := LinearMap.finrank_range_add_finrank_ker S.mulVecLin
  change (A + B).rank + Module.finrank ℂ (LinearMap.ker (A + B).mulVecLin) = _ at h₁
  change S.rank + Module.finrank ℂ (LinearMap.ker S.mulVecLin) = _ at h₂
  rw [hker] at h₁
  have h4 : (A + B).rank = 4 := by omega
  have hn : A + B ≠ 0 := by
    intro h
    rw [h, Matrix.rank_zero] at h4
    omega
  have h2 := bivectorCarrier_finrank hAB hn
  change (A + B).rank = 2 at h2
  omega

/-- A linear subspace of decomposable bivectors has a common carrier
line, or every carrier lies in a fixed subspace of dimension at most three. -/
theorem decomposable_submodule_carrier_dichotomy (S : Submodule ℂ (Matrix ι ι ℂ))
    (hS : ∀ A ∈ S, PluckerBivector A) :
    (∃ L : Submodule ℂ (ι → ℂ), Module.finrank ℂ L = 1 ∧
      ∀ A ∈ S, A ≠ 0 → L ≤ bivectorCarrier A) ∨
    (∃ H : Submodule ℂ (ι → ℂ), Module.finrank ℂ H ≤ 3 ∧
      ∀ A ∈ S, A ≠ 0 → bivectorCarrier A ≤ H) := by
  let planes := {P | ∃ A ∈ S, A ≠ 0 ∧ bivectorCarrier A = P}
  have hdim : ∀ P ∈ planes, Module.finrank ℂ P = 2 := by
    rintro _ ⟨A, hA, hn, rfl⟩
    exact bivectorCarrier_finrank (hS A hA) hn
  have hmeet : ∀ P ∈ planes, ∀ Q ∈ planes, P ⊓ Q ≠ ⊥ := by
    rintro _ ⟨A, hA, ha, rfl⟩ _ ⟨B, hB, hb, rfl⟩
    exact bivectorCarrier_inf_ne_bot (hS A hA) (hS B hB) (hS _ (S.add_mem hA hB)) ha hb
  rcases intersecting_planes_common_line_or_three_space planes hdim hmeet with
    ⟨L, hd, hL⟩ | ⟨H, hd, hH⟩
  · exact Or.inl ⟨L, hd, fun A hA hn => hL _ ⟨A, hA, hn, rfl⟩⟩
  · exact Or.inr ⟨H, hd, fun A hA hn => hH _ ⟨A, hA, hn, rfl⟩⟩

/-- A subspace of decomposable bivectors lies in a star, or its carriers
all lie in a common subspace of dimension at most three. -/
theorem decomposable_submodule_star_or_three_space (S : Submodule ℂ (Matrix ι ι ℂ))
    (hS : ∀ A ∈ S, PluckerBivector A) :
    (∃ z : ι → ℂ, z ≠ 0 ∧ ∀ A ∈ S, ∃ w : ι → ℂ, A = bivectorMatrix z w) ∨
    (∃ H : Submodule ℂ (ι → ℂ), Module.finrank ℂ H ≤ 3 ∧
      ∀ A ∈ S, A ≠ 0 → bivectorCarrier A ≤ H) := by
  rcases decomposable_submodule_carrier_dichotomy S hS with ⟨L, hdim, hL⟩ | hH
  · have hp : 0 < Module.finrank ℂ L := by rw [hdim]; decide
    obtain ⟨z, hzn⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hp
    have hz : (z : ι → ℂ) ≠ 0 := by
      intro he
      apply hzn
      exact Subtype.ext he
    refine Or.inl ⟨z, hz, fun A hA => ?_⟩
    by_cases ha : A = 0
    · refine ⟨0, ?_⟩
      ext i j
      simp [ha, bivectorMatrix]
    · exact exists_bivector_factor_of_mem_carrier (hS _ hA) ha z (hL A hA ha z.property) hz
  · exact Or.inr hH

end Carrier

end MOC
