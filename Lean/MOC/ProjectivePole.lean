import MOC.Core
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! A projective chart for the bipartite matching products with one right
label at infinity. The factor for the pole column is suppressed, and
all resulting matching products share the same nonzero scale. -/

open BigOperators

namespace MOC

/-- Put left labels `i₀`, `i₁` at zero and one and right label `j₀` at
infinity. The finite labels in the two spectra stay distinct. -/
theorem exists_projective_pole_chart {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) (i₀ i₁ j₀ : ι) (hi : i₀ ≠ i₁)
    (ha : Function.Injective a) (hb : Function.Injective b) (hab : ∀ i j, a i + b j ≠ 0) :
    ∃ (c : ℂ) (x y : ι → ℂ), c ≠ 0 ∧ x i₀ = 0 ∧ x i₁ = 1 ∧ Function.Injective x ∧
      (∀ {j k}, j ≠ j₀ → k ≠ j₀ → y j = y k → j = k) ∧
      (∀ i j, j ≠ j₀ → x i ≠ y j) ∧
      ∀ σ : Equiv.Perm ι, matchingProduct a b σ =
        c * ∏ j ∈ Finset.univ.erase j₀, (x (σ j) - y j) := by
  let L := (a i₁ + b j₀) / (a i₁ - a i₀)
  let K := L * (a i₀ + b j₀)
  let f (z : ℂ) := L * (z - a i₀) / (z + b j₀)
  let x (i : ι) := f (a i)
  let y (j : ι) := f (-b j)
  let A (i : ι) := a i + b j₀
  let B (j : ι) := -b j + b j₀
  let S : Finset ι := Finset.univ.erase j₀
  let c := (∏ i, A i) * (∏ j ∈ S, B j) / K ^ S.card
  have hleft : a i₁ - a i₀ ≠ 0 := sub_ne_zero.mpr (ha.ne hi.symm)
  have hL : L ≠ 0 := div_ne_zero (hab i₁ j₀) hleft
  have hK : K ≠ 0 := mul_ne_zero hL (hab i₀ j₀)
  have hB {j : ι} (hj : j ≠ j₀) : B j ≠ 0 := by
    change -b j + b j₀ ≠ 0
    rw [neg_add_eq_sub]
    exact sub_ne_zero.mpr (hb.ne hj.symm)
  have hf {z w : ℂ} (hz : z + b j₀ ≠ 0) (hw : w + b j₀ ≠ 0) :
      f z - f w = K * (z - w) / ((z + b j₀) * (w + b j₀)) := by
    dsimp only [f, K]
    field_simp [hz, hw]
    <;> ring
  have hfinj {z w : ℂ} (hz : z + b j₀ ≠ 0) (hw : w + b j₀ ≠ 0)
      (he : f z = f w) : z = w := by
    have h := sub_eq_zero.mpr he
    rw [hf hz hw] at h
    exact sub_eq_zero.mp ((mul_eq_zero.mp ((div_eq_zero_iff.mp h).resolve_right
      (mul_ne_zero hz hw))).resolve_left hK)
  have hterm (i j : ι) (hj : j ≠ j₀) :
      a i + b j = (x i - y j) * (A i * B j) / K := by
    change a i + b j = (f (a i) - f (-b j)) * ((a i + b j₀) * (-b j + b j₀)) / K
    rw [hf (hab i j₀) (hB hj)]
    rw [div_mul_cancel₀ _ (mul_ne_zero (hab i j₀) (hB hj)), mul_div_cancel_left₀ _ hK, sub_neg_eq_add]
  refine ⟨c, x, y, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hab i j₀)
      (Finset.prod_ne_zero_iff.mpr fun j hj => hB (Finset.mem_erase.mp hj).1)) (pow_ne_zero _ hK)
  · simp [x, f]
  · dsimp only [x, f, L]
    field_simp [hleft, hab i₁ j₀]
  · intro i k h
    exact ha (hfinj (hab i j₀) (hab k j₀) h)
  · intro j k hj hk h
    exact hb (neg_injective (hfinj (hB hj) (hB hk) h))
  · intro i j hj h
    have hz := hfinj (hab i j₀) (hB hj) h
    exact hab i j (by rw [hz, neg_add_cancel])
  · intro σ
    have hp : A (σ j₀) * (∏ j ∈ S, A (σ j)) = ∏ i, A i := by
      rw [show S = Finset.univ.erase j₀ from rfl,
        Finset.mul_prod_erase _ (fun j => A (σ j)) (Finset.mem_univ j₀),
        Equiv.prod_comp σ A]
    calc
      _ = A (σ j₀) * ∏ j ∈ S, (a (σ j) + b j) := by
        exact (Finset.mul_prod_erase _ (fun j => a (σ j) + b j) (Finset.mem_univ j₀)).symm
      _ = A (σ j₀) * ∏ j ∈ S, ((x (σ j) - y j) * (A (σ j) * B j) / K) := by
        congr 1
        exact Finset.prod_congr rfl (fun j hj => hterm (σ j) j (Finset.mem_erase.mp hj).1)
      _ = ((A (σ j₀) * ∏ j ∈ S, A (σ j)) * (∏ j ∈ S, B j) / K ^ S.card) *
            ∏ j ∈ S, (x (σ j) - y j) := by
        simp only [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const]
        ring
      _ = _ := by rw [hp]

end MOC
