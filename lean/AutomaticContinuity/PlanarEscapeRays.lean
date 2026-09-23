import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false

/-! # Explicit unbounded connected escape sets in the complex plane

An exterior point of a convex set escapes along the ray pointing away from
any point of the convex set. In the gap between two parallel caps, a vertical
ray escapes. Neither construction uses polynomial approximation, separation
theorems, compactness, or a connected-complement assumption.
-/

noncomputable section

namespace AutomaticContinuity.PlanarEscapeRays

open Set Complex

def ray (z v : ℂ) : Set ℂ := (fun t : ℝ ↦ z + t • v) '' Ici 0

theorem mem_ray (z v : ℂ) : z ∈ ray z v := by
  exact ⟨(0:ℝ), by simp, by simp⟩

theorem isPreconnected_ray (z v : ℂ) : IsPreconnected (ray z v) :=
  isPreconnected_Ici.image _ (by fun_prop)

theorem not_isBounded_ray (z : ℂ) {v : ℂ} (hv : v ≠ 0) :
    ¬ Bornology.IsBounded (ray z v) := by
  intro h
  obtain ⟨B,hB,hbound⟩ := h.exists_pos_norm_le
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let t : ℝ := (B + ‖z‖ + 1) / ‖v‖
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpoint : z + t • v ∈ ray z v := ⟨t,ht,rfl⟩
  have htval : t * ‖v‖ = B + ‖z‖ + 1 := by
    dsimp [t]
    exact div_mul_cancel₀ _ (ne_of_gt hvpos)
  have hn : t * ‖v‖ ≤ ‖z + t • v‖ + ‖z‖ := by
    calc
      _ = ‖t • v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
      _ = ‖(z + t • v) - z‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have := hbound _ hpoint
  linarith

theorem ray_subset_compl_of_convex {C : Set ℂ} (hC : Convex ℝ C)
    {z w : ℂ} (hz : z ∉ C) (hw : w ∈ C) : ray z (z-w) ⊆ Cᶜ := by
  rintro x ⟨t,ht,rfl⟩ hx
  change 0 ≤ t at ht
  change z + t • (z-w) ∈ C at hx
  have htp : 0 < t + 1 := by linarith
  have hc := hC hw hx
    (show 0 ≤ t/(t+1) by positivity)
    (show 0 ≤ 1/(t+1) by positivity)
    (show t/(t+1) + 1/(t+1) = 1 by field_simp)
  have heq : (t/(t+1):ℝ) • w + (1/(t+1):ℝ) • (z+t•(z-w)) = z := by
    calc
      _ = ((1/(t+1))*(t+1):ℝ) • z := by simp only [div_eq_mul_inv]; module
      _ = z := by rw [one_div_mul_cancel (ne_of_gt htp), one_smul]
  exact hz (heq ▸ hc)

/-- Every point outside a convex set lies in an explicit unbounded connected
subset of its complement. The convex set may be empty or unbounded. -/
theorem exists_escape_convex {C : Set ℂ} (hC : Convex ℝ C) {z : ℂ} (hz : z ∉ C) :
    ∃ T : Set ℂ, IsPreconnected T ∧ z ∈ T ∧ T ⊆ Cᶜ ∧ ¬ Bornology.IsBounded T := by
  rcases C.eq_empty_or_nonempty with h | ⟨w,hw⟩
  · refine ⟨ray z 1,isPreconnected_ray z 1,mem_ray z 1,?_,not_isBounded_ray z one_ne_zero⟩
    simp [h]
  · refine ⟨ray z (z-w),isPreconnected_ray z (z-w),mem_ray z (z-w),
      ray_subset_compl_of_convex hC hz hw,not_isBounded_ray z ?_⟩
    exact sub_ne_zero.mpr (fun h ↦ hz (h ▸ hw))

def separatedCaps (C : Set ℂ) (c d : ℝ) : Set ℂ :=
  (C ∩ {z | z.re ≤ c}) ∪ (C ∩ {z | d ≤ z.re})

theorem vertical_ray_subset_caps_compl {C : Set ℂ} {c d : ℝ} {z : ℂ}
    (hcz : c < z.re) (hzd : z.re < d) : ray z I ⊆ (separatedCaps C c d)ᶜ := by
  rintro x ⟨t,_,rfl⟩ hx
  have hre : (z + t • I).re = z.re := by simp
  rcases hx with hx | hx
  · have : (z+t•I).re ≤ c := hx.2
    rw [hre] at this
    linarith
  · have : d ≤ (z+t•I).re := hx.2
    rw [hre] at this
    linarith

/-- Two real-coordinate caps cut from a convex set have no bounded
complement component. In the separating strip the escape ray is vertical. -/
theorem exists_escape_separatedCaps {C : Set ℂ} (hC : Convex ℝ C)
    {c d : ℝ} (_hcd : c < d) {z : ℂ} (hz : z ∉ separatedCaps C c d) :
    ∃ T : Set ℂ, IsPreconnected T ∧ z ∈ T ∧
      T ⊆ (separatedCaps C c d)ᶜ ∧ ¬ Bornology.IsBounded T := by
  by_cases hzC : z ∈ C
  · have hcz : c < z.re := lt_of_not_ge (fun h ↦ hz (Or.inl ⟨hzC,h⟩))
    have hzd : z.re < d := lt_of_not_ge (fun h ↦ hz (Or.inr ⟨hzC,h⟩))
    exact ⟨ray z I,isPreconnected_ray z I,mem_ray z I,
      vertical_ray_subset_caps_compl hcz hzd,not_isBounded_ray z I_ne_zero⟩
  · obtain ⟨T,hT,hzT,hTC,hTb⟩ := exists_escape_convex hC hzC
    refine ⟨T,hT,hzT,?_,hTb⟩
    intro x hx hxcap
    exact hTC hx (hxcap.elim And.left And.left)

end AutomaticContinuity.PlanarEscapeRays
