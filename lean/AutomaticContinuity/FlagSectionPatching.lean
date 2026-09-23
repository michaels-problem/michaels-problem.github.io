import AutomaticContinuity.FlagApproximationStability

set_option autoImplicit false

/-!
# Patching an already-small replacement of an admissible section

A continuous real cutoff interpolates between the old and new maps inside the
proved admissibility tube. Holomorphicity is asserted only on a region where
the cutoff is identically one (or identically zero). This constructs no new
holomorphic approximation and imposes no holomorphicity on a general cutoff.
-/

noncomputable section

namespace AutomaticContinuity.FlagSectionPatching

open Set FlagTotalSpace

abbrev Pair := ℂ × ℂ

def patch {X : Type*} (h g : X → Pair) (ρ : X → ℝ) (z : X) : Pair :=
  h z + ρ z • (g z - h z)

@[simp] theorem patch_eq_old {X : Type*} (h g : X → Pair) (ρ : X → ℝ)
    {z : X} (hρ : ρ z = 0) : patch h g ρ z = h z := by simp [patch, hρ]

@[simp] theorem patch_eq_new {X : Type*} (h g : X → Pair) (ρ : X → ℝ)
    {z : X} (hρ : ρ z = 1) : patch h g ρ z = g z := by simp [patch, hρ]

theorem patch_sub_old {X : Type*} (h g : X → Pair) (ρ : X → ℝ) (z : X) :
    patch h g ρ z - h z = ρ z • (g z - h z) := by
  dsimp [patch]
  abel

theorem continuous_patch {X : Type*} [TopologicalSpace X]
    {h g : X → Pair} {ρ : X → ℝ}
    (hh : Continuous h) (hg : Continuous g) (hρ : Continuous ρ) :
    Continuous (patch h g ρ) := hh.add (hρ.smul (hg.sub hh))

/-- A cutoff between zero and one never increases the displacement from the
old section, measured in the actual Euclidean pair norm. -/
theorem norm_patch_sub_le {X : Type*} (h g : X → Pair) (ρ : X → ℝ) {z : X}
    (hρ0 : 0 ≤ ρ z) (hρ1 : ρ z ≤ 1) :
    euclideanPairNorm (patch h g ρ z - h z) ≤ euclideanPairNorm (g z - h z) := by
  rw [patch_sub_old, euclideanPairNorm_real_smul hρ0]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hρ1
    (euclideanPairNorm_nonneg (g z - h z))

/-- Global admissibility follows from the compact tube inside `K` and exact
agreement with the old globally admissible map outside `K`. -/
theorem admissible_patch_of_tube {n : ℕ} {K : Set (FinitePoint n)}
    {h g : FinitePoint n → Pair} {ρ : FinitePoint n → ℝ} {δ : ℝ}
    (hadm : ∀ z, (z, h z) ∈ totalSet n)
    (htube : ∀ z ∈ K, ∀ v : Pair,
      euclideanPairNorm (v - h z) ≤ δ → (z, v) ∈ totalSet n)
    (hρ0 : ∀ z, 0 ≤ ρ z) (hρ1 : ∀ z, ρ z ≤ 1)
    (houtside : ∀ z ∉ K, ρ z = 0)
    (hclose : ∀ z ∈ K, euclideanPairNorm (g z - h z) ≤ δ) :
    ∀ z, (z, patch h g ρ z) ∈ totalSet n := by
  intro z
  by_cases hz : z ∈ K
  · exact htube z hz _ ((norm_patch_sub_le h g ρ (hρ0 z) (hρ1 z)).trans (hclose z hz))
  · rw [patch_eq_old h g ρ (houtside z hz)]
    exact hadm z

/-- Compactness chooses a uniform tolerance that works for every continuous
replacement and every continuous cutoff supported in the specified compact. -/
theorem exists_patch_tolerance {n : ℕ} {K : Set (FinitePoint n)} (hK : IsCompact K)
    {h : FinitePoint n → Pair} (hh : Continuous h)
    (hadm : ∀ z, (z, h z) ∈ totalSet n) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (g : FinitePoint n → Pair) (ρ : FinitePoint n → ℝ),
        Continuous g → Continuous ρ → (∀ z, 0 ≤ ρ z) → (∀ z, ρ z ≤ 1) →
        (∀ z ∉ K, ρ z = 0) →
        (∀ z ∈ K, euclideanPairNorm (g z - h z) ≤ δ) →
        Continuous (patch h g ρ) ∧ ∀ z, (z, patch h g ρ z) ∈ totalSet n := by
  obtain ⟨δ, hδ, htube⟩ := exists_uniform_tube hK hh.continuousOn
    (fun z _hz => mem_totalSet_iff.mp (hadm z))
  refine ⟨δ, hδ, ?_⟩
  intro g ρ hg hρ hρ0 hρ1 houtside hclose
  exact ⟨continuous_patch hh hg hρ,
    admissible_patch_of_tube hadm htube hρ0 hρ1 houtside hclose⟩

/-- Where the cutoff is identically one, the patch is genuinely holomorphic
whenever the replacement is. No differentiability of the cutoff is required. -/
theorem differentiableOn_patch_of_one {n : ℕ} {U : Set (FinitePoint n)}
    (h g : FinitePoint n → Pair) (ρ : FinitePoint n → ℝ)
    (hg : DifferentiableOn ℂ g U) (hρ : ∀ z ∈ U, ρ z = 1) :
    DifferentiableOn ℂ (patch h g ρ) U :=
  hg.congr (fun z hz => patch_eq_new h g ρ (hρ z hz))

theorem differentiableOn_patch_of_zero {n : ℕ} {U : Set (FinitePoint n)}
    (h g : FinitePoint n → Pair) (ρ : FinitePoint n → ℝ)
    (hh : DifferentiableOn ℂ h U) (hρ : ∀ z ∈ U, ρ z = 0) :
    DifferentiableOn ℂ (patch h g ρ) U :=
  hh.congr (fun z hz => patch_eq_old h g ρ (hρ z hz))

/-- In particular, a replacement holomorphic near a compact remains so after
patching if the cutoff is one throughout that actual open neighborhood. -/
theorem holomorphicNear_patch_of_one {n : ℕ} {L U : Set (FinitePoint n)}
    (h g : FinitePoint n → Pair) (ρ : FinitePoint n → ℝ)
    (hU : IsOpen U) (hLU : L ⊆ U) (hg : DifferentiableOn ℂ g U)
    (hρ : ∀ z ∈ U, ρ z = 1) :
    ∃ V : Set (FinitePoint n), IsOpen V ∧ L ⊆ V ∧
      DifferentiableOn ℂ (patch h g ρ) V :=
  ⟨U, hU, hLU, differentiableOn_patch_of_one h g ρ hg hρ⟩

end AutomaticContinuity.FlagSectionPatching
