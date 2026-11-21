import MOC.Core
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Relation
import Mathlib.Tactic.Choose

/-! Real matching products allow real diagonal similarity on a strongly
connected nonzero-entry graph, even when some kernel entries are zero. -/

open BigOperators

namespace MOC

variable {ι : Type*}

private noncomputable def walkWeight (K : Matrix ι ι ℂ) (v : ℕ → ι) (n : ℕ) : ℂ :=
  ∏ k ∈ Finset.range n, K (v k) (v (k + 1))

private theorem walkWeight_split (K : Matrix ι ι ℂ) (v : ℕ → ι) (n m : ℕ) :
    walkWeight K v (n + m) =
      walkWeight K v n * walkWeight K (fun k => v (n + k)) m := by
  simp only [walkWeight, Finset.prod_range_add, Nat.add_assoc]

private theorem exists_walk_join (K : Matrix ι ι ℂ) (v w : ℕ → ι) (n m : ℕ)
    (h : v n = w 0) :
    ∃ u : ℕ → ι, u 0 = v 0 ∧ u (n + m) = w m ∧
      walkWeight K u (n + m) = walkWeight K v n * walkWeight K w m := by
  let u (k : ℕ) := if k < n then v k else w (k - n)
  have hx (k) (hk : k ≤ n) : u k = v k := by
    by_cases hkn : k < n
    · simp [u, hkn]
    · have he : k = n := by omega
      subst k
      simp [u, h]
  have hy (k) : u (n + k) = w k := by
    have hkn : ¬ n + k < n := by omega
    simp [u, hkn]
  refine ⟨u, hx 0 (Nat.zero_le n), hy m, ?_⟩
  rw [walkWeight_split, show (fun k => u (n + k)) = w from funext hy]
  congr 1
  unfold walkWeight
  apply Finset.prod_congr rfl
  intro k hk
  have hkn := Finset.mem_range.mp hk
  rw [hx k (by omega), hx (k + 1) (by omega)]

private theorem exists_walk_extend (K : Matrix ι ι ℂ) (v : ℕ → ι) (n : ℕ) (j : ι) :
    ∃ w : ℕ → ι, w 0 = v 0 ∧ w (n + 1) = j ∧
      walkWeight K w (n + 1) = walkWeight K v n * K (v n) j := by
  let u (k : ℕ) := if k = 0 then v n else j
  obtain ⟨w, h₀, hlast, hweight⟩ := exists_walk_join K v u n 1 (by simp [u])
  refine ⟨w, h₀, by simpa [u] using hlast, ?_⟩
  simpa only [walkWeight, u, Finset.prod_range_one, if_pos rfl, zero_add,
    if_neg Nat.one_ne_zero] using hweight

private theorem exists_nonzero_walk (K : Matrix ι ι ℂ) {i j : ι}
    (h : Relation.ReflTransGen (fun a b => K a b ≠ 0) i j) :
    ∃ (n : ℕ) (v : ℕ → ι), v 0 = i ∧ v n = j ∧ walkWeight K v n ≠ 0 := by
  induction h with
  | refl => exact ⟨0, fun _ => i, rfl, rfl, by simp [walkWeight]⟩
  | @tail b c _ hbc ih =>
    obtain ⟨n, v, h₀, hn, hw⟩ := ih
    obtain ⟨u, hu₀, huend, hu⟩ := exists_walk_extend K v n c
    exact ⟨n + 1, u, hu₀.trans h₀, huend, by rw [hu, hn]; exact mul_ne_zero hw hbc⟩

variable [Fintype ι] [DecidableEq ι]

private theorem simple_closed_walk_weight_im_eq_zero (K : Matrix ι ι ℂ)
    (hdiag : ∀ i, K i i = 1) (hmatch : ∀ σ : Equiv.Perm ι, (∏ j, K j (σ j)).im = 0)
    (n : ℕ) (v : ℕ → ι) (hend : v n = v 0)
    (hv : Function.Injective (fun i : Fin n => v i.val)) :
    (walkWeight K v n).im = 0 := by
  cases n with
  | zero => simp [walkWeight]
  | succ n =>
    let e : Fin (n + 1) ↪ ι := ⟨fun i => v i.val, hv⟩
    let σ := (finRotate (n + 1)).viaFintypeEmbedding e
    let S : Finset ι := Finset.univ.map e
    let f (j : ι) := K j (σ j)
    have hf (j) (hj : j ∈ Sᶜ) : f j = 1 := by
      have hnr : j ∉ Set.range e := by
        rintro ⟨i, hi⟩
        exact (Finset.mem_compl.mp hj) (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, hi⟩)
      change K j (σ j) = 1
      rw [Equiv.Perm.viaFintypeEmbedding_apply_not_mem_range _ _ hnr, hdiag]
    have hstep (i : Fin (n + 1)) :
        v (finRotate (n + 1) i).val = v (i.val + 1) := by
      by_cases hlast : i = Fin.last n
      · subst i
        simpa only [finRotate_last, Fin.val_zero, Fin.val_last] using hend.symm
      · rw [coe_finRotate_of_ne_last hlast]
    have hprod : (∏ j, K j (σ j)) = walkWeight K v (n + 1) := by
      change (∏ j, f j) = _
      rw [← Finset.prod_compl_mul_prod S f, Finset.prod_eq_one hf, one_mul]
      change (∏ j ∈ Finset.univ.map e, K j (σ j)) = _
      rw [Finset.prod_map, walkWeight, ← Fin.prod_univ_eq_prod_range]
      apply Finset.prod_congr rfl
      intro i _
      simp only [σ, Equiv.Perm.viaFintypeEmbedding_apply_image]
      change K (v i.val) (v (finRotate (n + 1) i).val) =
        K (v i.val) (v (i.val + 1))
      rw [hstep]
    rw [← hprod]
    exact hmatch σ

private theorem closed_walk_weight_im_eq_zero (K : Matrix ι ι ℂ)
    (hdiag : ∀ i, K i i = 1) (hmatch : ∀ σ : Equiv.Perm ι, (∏ j, K j (σ j)).im = 0)
    (n : ℕ) (v : ℕ → ι) (hend : v n = v 0) :
    (walkWeight K v n).im = 0 := by
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hv : Function.Injective (fun i : Fin n => v i.val)
    · exact simple_closed_walk_weight_im_eq_zero K hdiag hmatch n v hend hv
    have hrep : ∃ i j : Fin n, i < j ∧ v i.val = v j.val := by
      by_contra hn
      apply hv
      intro i j he
      rcases lt_trichotomy i j with h | h | h
      · exact (hn ⟨i, j, h, he⟩).elim
      · exact h
      · exact (hn ⟨j, i, h, he.symm⟩).elim
    obtain ⟨i, j, hij, he⟩ := hrep
    have hlt : i.val < j.val := hij
    have hjn : j.val < n := j.isLt
    let v₁ (k : ℕ) := v (i.val + k)
    let v₂ (k : ℕ) := v (j.val + k)
    have h₁ : i.val + (j.val - i.val) = j.val := by omega
    have h₂ : j.val + (n - j.val) = n := by omega
    have hsmall₁ : j.val - i.val < n := by omega
    have hsmall₂ : i.val + (n - j.val) < n := by omega
    have hclosed₁ : v₁ (j.val - i.val) = v₁ 0 := by
      simpa only [v₁, h₁, Nat.add_zero] using he.symm
    obtain ⟨u, hu₀, huend, hu⟩ := exists_walk_join K v v₂ i.val (n - j.val)
      (by simpa only [v₂, Nat.add_zero] using he)
    have hclosed₂ : u (i.val + (n - j.val)) = u 0 := by
      rw [huend, hu₀]
      simpa only [v₂, h₂] using hend
    have hsplit₁ : walkWeight K v j.val =
        walkWeight K v i.val * walkWeight K v₁ (j.val - i.val) := by
      rw [← walkWeight_split K v i.val (j.val - i.val), h₁]
    have hsplit₂ : walkWeight K v n =
        walkWeight K v j.val * walkWeight K v₂ (n - j.val) := by
      rw [← walkWeight_split K v j.val (n - j.val), h₂]
    have hsplit : walkWeight K v n =
        walkWeight K v₁ (j.val - i.val) * walkWeight K u (i.val + (n - j.val)) := by
      rw [hsplit₂, hsplit₁, hu]
      ring
    rw [hsplit, Complex.mul_im, ih _ hsmall₁ _ hclosed₁, ih _ hsmall₂ _ hclosed₂,
      mul_zero, zero_mul, add_zero]

/-- A diagonal-one matching kernel with real matching products and a
strongly connected nonzero-entry graph is similar by a nonzero diagonal
to a real matrix. The similarity is written as entrywise ratios. -/
theorem exists_diagonal_dephase_of_real_matchings (K : Matrix ι ι ℂ) (p : ι)
    (hdiag : ∀ i, K i i = 1)
    (hmatch : ∀ σ : Equiv.Perm ι, (∏ j, K (σ j) j).im = 0)
    (hforward : ∀ i, Relation.ReflTransGen (fun a b => K a b ≠ 0) p i)
    (hreturn : ∀ i, Relation.ReflTransGen (fun a b => K a b ≠ 0) i p) :
    ∃ g : ι → ℂ, (∀ i, g i ≠ 0) ∧ ∀ i j, (g i * K i j / g j).im = 0 := by
  classical
  have hmatch' (σ : Equiv.Perm ι) : (∏ j, K j (σ j)).im = 0 := by
    have h := hmatch σ.symm
    rw [← Equiv.prod_comp σ (fun j => K (σ.symm j) j)] at h
    simpa only [Equiv.symm_apply_apply] using h
  choose n v hv₀ hvi hv using fun i => exists_nonzero_walk K (hforward i)
  choose m w hw₀ hwp hw using fun j => exists_nonzero_walk K (hreturn j)
  let g (i : ι) := walkWeight K (v i) (n i)
  let b (j : ι) := walkWeight K (w j) (m j)
  refine ⟨g, hv, fun i j => ?_⟩
  obtain ⟨u, hu₀, huend, hu⟩ := exists_walk_join K (v j) (w j) (n j) (m j)
    ((hvi j).trans (hw₀ j).symm)
  have hden : (g j * b j).im = 0 := by
    change (walkWeight K (v j) (n j) * walkWeight K (w j) (m j)).im = 0
    rw [← hu]
    exact closed_walk_weight_im_eq_zero K hdiag hmatch' _ _
      (huend.trans ((hwp j).trans ((hv₀ j).symm.trans hu₀.symm)))
  obtain ⟨v', hv'₀, hv'end, hv'⟩ := exists_walk_extend K (v i) (n i) j
  obtain ⟨u', hu'₀, hu'end, hu'⟩ := exists_walk_join K v' (w j) (n i + 1) (m j)
    (hv'end.trans (hw₀ j).symm)
  have hnum : (g i * K i j * b j).im = 0 := by
    have he : walkWeight K u' (n i + 1 + m j) = g i * K i j * b j := by
      rw [hu', hv', hvi i]
    rw [← he]
    exact closed_walk_weight_im_eq_zero K hdiag hmatch' _ _
      (hu'end.trans ((hwp j).trans ((hv₀ i).symm.trans (hv'₀.symm.trans hu'₀.symm))))
  rw [← mul_div_mul_right _ _ (show b j ≠ 0 from hw j)]
  simp only [Complex.div_im, hden, hnum, zero_mul, mul_zero, zero_div, sub_self]

end MOC
