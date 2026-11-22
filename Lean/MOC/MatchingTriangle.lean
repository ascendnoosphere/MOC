import MOC.Support
import Mathlib.Tactic.Linarith

/-! The local three-label alternating identity controls the odd part of
the support variation near a permutation in any order. -/

open BigOperators

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Fix all but three columns of a matching. The two three-cycles and the
original matching have the same total product as the three transpositions. -/
theorem matchingProduct_triangle_identity
    (a b : ι → ℂ) (σ : Equiv.Perm ι) (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    matchingProduct a b σ +
      matchingProduct a b (σ * Equiv.swap i j * Equiv.swap j k) +
      matchingProduct a b (σ * Equiv.swap j k * Equiv.swap i j) =
    matchingProduct a b (σ * Equiv.swap i j) +
      matchingProduct a b (σ * Equiv.swap i k) +
      matchingProduct a b (σ * Equiv.swap j k) := by
  let S : Finset ι := {i, j, k}
  let R := ∏ m ∈ Sᶜ, (a (σ m) + b m)
  have hfactor (τ : Equiv.Perm ι) (hτ : ∀ m ∈ Sᶜ, τ m = m) :
      matchingProduct a b (σ * τ) =
        R * ((a (σ (τ i)) + b i) * ((a (σ (τ j)) + b j) * (a (σ (τ k)) + b k))) := by
    let f (m : ι) := a (σ (τ m)) + b m
    have hfixed : (∏ m ∈ Sᶜ, f m) = R := by
      apply Finset.prod_congr rfl
      intro m hm
      simp only [f, hτ m hm]
    have hprod : (∏ m ∈ S, f m) = f i * (f j * f k) := by
      change (∏ m ∈ ({i, j, k} : Finset ι), f m) = _
      rw [Finset.prod_insert (show i ∉ ({j, k} : Finset ι) by simp [hij, hik]),
        Finset.prod_insert (show j ∉ ({k} : Finset ι) by simp [hjk]), Finset.prod_singleton]
    change (∏ m, f m) = R * (f i * (f j * f k))
    rw [← Finset.prod_compl_mul_prod S f, hfixed, hprod]
  have hout (m : ι) (hm : m ∈ Sᶜ) : m ≠ i ∧ m ≠ j ∧ m ≠ k := by
    simpa [S, not_or] using Finset.mem_compl.mp hm
  have h₀ := hfactor 1 (fun _ _ => rfl)
  have h₁ := hfactor (Equiv.swap i j)
    (fun m hm => Equiv.swap_apply_of_ne_of_ne (hout m hm).1 (hout m hm).2.1)
  have h₂ := hfactor (Equiv.swap i k)
    (fun m hm => Equiv.swap_apply_of_ne_of_ne (hout m hm).1 (hout m hm).2.2)
  have h₃ := hfactor (Equiv.swap j k)
    (fun m hm => Equiv.swap_apply_of_ne_of_ne (hout m hm).2.1 (hout m hm).2.2)
  have hp := hfactor (Equiv.swap i j * Equiv.swap j k)
    (fun m hm => by simp only [Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (hout m hm).2.1 (hout m hm).2.2,
      Equiv.swap_apply_of_ne_of_ne (hout m hm).1 (hout m hm).2.1])
  have hq := hfactor (Equiv.swap j k * Equiv.swap i j)
    (fun m hm => by simp only [Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (hout m hm).1 (hout m hm).2.1,
      Equiv.swap_apply_of_ne_of_ne (hout m hm).2.1 (hout m hm).2.2])
  simp only [mul_one, Equiv.Perm.one_apply] at h₀
  rw [mul_assoc σ (Equiv.swap i j) (Equiv.swap j k),
    mul_assoc σ (Equiv.swap j k) (Equiv.swap i j), h₀, hp, hq, h₁, h₂, h₃]
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne hij hik, Equiv.swap_apply_of_ne_of_ne hij.symm hjk,
    Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm]
  ring

theorem matching_cycle_gap_sum_eq_swaps
    (a b : ι → ℂ) (η : ℂ) (σ : Equiv.Perm ι) (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    matchingGap a b η σ (σ * Equiv.swap i j * Equiv.swap j k) +
      matchingGap a b η σ (σ * Equiv.swap j k * Equiv.swap i j) =
      matchingGap a b η σ (σ * Equiv.swap i j) +
      matchingGap a b η σ (σ * Equiv.swap i k) +
      matchingGap a b η σ (σ * Equiv.swap j k) := by
  have h := congrArg (fun z : ℂ => (η * z).re)
    (matchingProduct_triangle_identity a b σ i j k hij hik hjk)
  simp only [mul_add, Complex.add_re] at h
  unfold matchingGap
  linarith only [h]

/-- At a maximizing matching, the difference between oriented cycle scores
is bounded by the sum of the three transposition deficits. -/
theorem abs_matching_cycle_gap_le_swaps
    (a b : ι → ℂ) (η : ℂ) (σ : Equiv.Perm ι) (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hmax : ∀ τ, 0 ≤ matchingGap a b η σ τ) :
    |matchingGap a b η σ (σ * Equiv.swap i j * Equiv.swap j k) -
      matchingGap a b η σ (σ * Equiv.swap j k * Equiv.swap i j)| ≤
      matchingGap a b η σ (σ * Equiv.swap i j) +
      matchingGap a b η σ (σ * Equiv.swap i k) +
      matchingGap a b η σ (σ * Equiv.swap j k) := by
  have h := matching_cycle_gap_sum_eq_swaps a b η σ i j k hij hik hjk
  have hp := hmax (σ * Equiv.swap i j * Equiv.swap j k)
  have hq := hmax (σ * Equiv.swap j k * Equiv.swap i j)
  exact abs_le.mpr ⟨by linarith only [h, hp, hq], by linarith only [h, hp, hq]⟩

end MOC
