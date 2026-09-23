import AutomaticContinuity.FlagLocalExtension

set_option autoImplicit false

/-!
# Unit-radius enlargement is the same remaining approximation input

Only an enlargement from radius R to R+1 is required. Finite iteration gives
arbitrary compact enlargement, and the previously checked exhaustion gives
entire approximation. This proposition remains an explicit unproved input.
-/

namespace AutomaticContinuity

def FiniteFlagUnitExtensionStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (R : ℝ), 0 ≤ R →
    ∀ h : FinitePoint n → ℂ × ℂ,
      Continuous h →
      (∃ U : Set (FinitePoint n), IsOpen U ∧ polydisc n R ⊆ U ∧
        DifferentiableOn ℂ h U) →
      (∀ k : ℕ, 1 ≤ k → k ≤ n →
        ∀ z ∈ finiteFlag n k, (k : ℝ) < euclideanPairNorm (h z)) →
      ∀ ε : ℝ, 0 < ε →
        ∃ H : FinitePoint n → ℂ × ℂ,
          Continuous H ∧
          (∃ U : Set (FinitePoint n), IsOpen U ∧ polydisc n (R + 1) ⊆ U ∧
            DifferentiableOn ℂ H U) ∧
          (∀ k : ℕ, 1 ≤ k → k ≤ n →
            ∀ z ∈ finiteFlag n k, (k : ℝ) < euclideanPairNorm (H z)) ∧
          (∀ z ∈ polydisc n R, euclideanPairNorm (H z - h z) < ε)

theorem finiteFlagUnitExtension_iterate (hUnit : FiniteFlagUnitExtensionStatement)
    (n : ℕ) (hn : 1 ≤ n) (R : ℝ) (hR : 0 ≤ R) (m : ℕ)
    (h : FinitePoint n → ℂ × ℂ) (hc : Continuous h)
    (hh : ∃ U : Set (FinitePoint n), IsOpen U ∧ polydisc n R ⊆ U ∧
      DifferentiableOn ℂ h U)
    (hb : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      ∀ z ∈ finiteFlag n k, (k : ℝ) < euclideanPairNorm (h z))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ H : FinitePoint n → ℂ × ℂ,
      Continuous H ∧
      (∃ U : Set (FinitePoint n), IsOpen U ∧ polydisc n (R + m) ⊆ U ∧
        DifferentiableOn ℂ H U) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ n →
        ∀ z ∈ finiteFlag n k, (k : ℝ) < euclideanPairNorm (H z)) ∧
      (∀ z ∈ polydisc n R, euclideanPairNorm (H z - h z) < ε) := by
  induction m generalizing ε with
  | zero =>
    refine ⟨h, hc, ?_, hb, ?_⟩
    · simpa only [Nat.cast_zero, add_zero] using hh
    · intro z _
      simpa only [sub_self, euclideanPairNorm_zero] using hε
  | succ m ih =>
    obtain ⟨H, hHc, hHh, hHb, hHa⟩ := ih (ε / 2) (half_pos hε)
    obtain ⟨G, hGc, hGh, hGb, hGa⟩ := hUnit n hn (R + m)
      (add_nonneg hR (Nat.cast_nonneg m)) H hHc hHh hHb (ε / 2) (half_pos hε)
    refine ⟨G, hGc, ?_, hGb, ?_⟩
    · simpa only [Nat.cast_succ, add_assoc] using hGh
    · intro z hz
      have hz' : z ∈ polydisc n (R + m) :=
        FlagLocalExtension.polydisc_mono n (le_add_of_nonneg_right (Nat.cast_nonneg m)) hz
      have heq : G z - h z = (G z - H z) + (H z - h z) := by abel
      rw [heq]
      exact (euclideanPairNorm_add_le _ _).trans_lt (by linarith [hGa z hz', hHa z hz])

theorem finiteFlagLocalExtension_of_unitExtension
    (hUnit : FiniteFlagUnitExtensionStatement) : FiniteFlagLocalExtensionStatement := by
  intro n hn R S hR _hRS h hc hh hb ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt (S - R)
  obtain ⟨H, hHc, ⟨U, hU, hKU, hHd⟩, hHb, hHa⟩ :=
    finiteFlagUnitExtension_iterate hUnit n hn R hR m h hc hh hb ε hε
  refine ⟨H, hHc, ⟨U, hU, ?_, hHd⟩, hHb, hHa⟩
  exact (FlagLocalExtension.polydisc_mono n (by linarith : S ≤ R + m)).trans hKU

theorem finiteFlagUnitExtension_of_localExtension
    (hLocal : FiniteFlagLocalExtensionStatement) : FiniteFlagUnitExtensionStatement := by
  intro n hn R hR h hc hh hb ε hε
  exact hLocal n hn R (R + 1) hR (lt_add_one R) h hc hh hb ε hε

theorem finiteFlagUnitExtension_iff_approximation :
    FiniteFlagUnitExtensionStatement ↔ FiniteFlagApproximationStatement :=
  ⟨fun h => finiteFlagApproximation_of_localExtension
      (finiteFlagLocalExtension_of_unitExtension h),
    fun h => finiteFlagUnitExtension_of_localExtension
      (finiteFlagLocalExtension_of_approximation h)⟩

end AutomaticContinuity
