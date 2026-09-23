import AutomaticContinuity.PolynomialCutoff
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

/-!
# Uniform tubes preserving strict cutoff margins

A cutoff bounded by 1/16 on a compact set stays below 1/8 on one fixed
positive closed tube. The same radius works for both the zero and one regions.
This tube is chosen before the cutoff is iterated and is therefore independent
of the amplified polynomial's degree.
-/

noncomputable section

namespace AutomaticContinuity.CompactCutoffTubes

open Metric Set

variable {E : Type*} [PseudoMetricSpace E]

theorem exists_tube (q : E → ℂ) {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hq : ContinuousOn q U)
    (c : ℂ) (hsmall : ∀ x ∈ K, ‖q x - c‖ ≤ 1 / 16) :
    ∃ ρ : ℝ, 0 < ρ ∧ cthickening ρ K ⊆ U ∧
      ∀ x ∈ cthickening ρ K, ‖q x - c‖ < 1 / 8 := by
  let V : Set E := U ∩ (fun x => ‖q x - c‖) ⁻¹' Iio (1 / 8)
  have hV : IsOpen V := ((hq.sub continuousOn_const).norm).isOpen_inter_preimage hU isOpen_Iio
  have hKV : K ⊆ V := fun x hx => ⟨hKU hx, (hsmall x hx).trans_lt (by norm_num)⟩
  obtain ⟨ρ, hρ, hsub⟩ := hK.exists_cthickening_subset_open hV hKV
  exact ⟨ρ, hρ, fun x hx => (hsub hx).1, fun x hx => (hsub hx).2⟩

/-- The actual closed tubes are disjoint, as forced by their scalar cutoff
values. No independent separation theorem or positive-distance assumption is
required. -/
theorem exists_two_tubes (q : E → ℂ) {K₀ K₁ U : Set E}
    (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁)
    (hU : IsOpen U) (hK₀U : K₀ ⊆ U) (hK₁U : K₁ ⊆ U) (hq : ContinuousOn q U)
    (hzero : ∀ x ∈ K₀, ‖q x‖ ≤ 1 / 16)
    (hone : ∀ x ∈ K₁, ‖q x - 1‖ ≤ 1 / 16) :
    ∃ ρ : ℝ, 0 < ρ ∧ cthickening ρ K₀ ⊆ U ∧ cthickening ρ K₁ ⊆ U ∧
      (∀ x ∈ cthickening ρ K₀, ‖q x‖ < 1 / 8) ∧
      (∀ x ∈ cthickening ρ K₁, ‖q x - 1‖ < 1 / 8) ∧
      Disjoint (cthickening ρ K₀) (cthickening ρ K₁) := by
  obtain ⟨ρ₀, hρ₀, h₀U, h₀⟩ := exists_tube q hK₀ hU hK₀U hq 0
    (by simpa only [sub_zero] using hzero)
  obtain ⟨ρ₁, hρ₁, h₁U, h₁⟩ := exists_tube q hK₁ hU hK₁U hq 1 hone
  let ρ := min ρ₀ ρ₁
  have hsub₀ : cthickening ρ K₀ ⊆ cthickening ρ₀ K₀ := cthickening_mono (min_le_left _ _) _
  have hsub₁ : cthickening ρ K₁ ⊆ cthickening ρ₁ K₁ := cthickening_mono (min_le_right _ _) _
  have hz : ∀ x ∈ cthickening ρ K₀, ‖q x‖ < 1 / 8 := by
    intro x hx
    simpa only [sub_zero] using h₀ x (hsub₀ hx)
  have ho : ∀ x ∈ cthickening ρ K₁, ‖q x - 1‖ < 1 / 8 := fun x hx => h₁ x (hsub₁ hx)
  refine ⟨ρ, lt_min hρ₀ hρ₁, hsub₀.trans h₀U, hsub₁.trans h₁U, hz, ho, ?_⟩
  rw [Set.disjoint_left]
  intro x hx₀ hx₁
  have ht := norm_sub_le (q x) (q x - 1)
  have heq : q x - (q x - 1) = 1 := by ring
  rw [heq, norm_one] at ht
  linarith [hz x hx₀, ho x hx₁]

end AutomaticContinuity.CompactCutoffTubes
