import AutomaticContinuity.FlagApproximationStability
import AutomaticContinuity.SeveralVariableUniformLimit
import AutomaticContinuity.AdaptiveUniformLimit

set_option autoImplicit false

/-!
# From compact local extension to global flag approximation

The local extension input enlarges the compact set on which a continuous
admissible section is holomorphic. It does not already assume an entire output.
The exhaustion argument uses adaptive summable errors and compact stability
tubes to retain the strict flag inequalities in the final holomorphic limit.
-/

noncomputable section

namespace AutomaticContinuity

/-- A local enlargement step sufficient for the global finite flag theorem.
This remains an explicit unproved proposition, not an axiom. -/
def FiniteFlagLocalExtensionStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (R S : ℝ), 0 ≤ R → R < S →
    ∀ h : FinitePoint n → ℂ × ℂ,
      Continuous h →
      (∃ U : Set (FinitePoint n), IsOpen U ∧ polydisc n R ⊆ U ∧
        DifferentiableOn ℂ h U) →
      (∀ k : ℕ, 1 ≤ k → k ≤ n →
        ∀ z ∈ finiteFlag n k, (k : ℝ) < euclideanPairNorm (h z)) →
      ∀ ε : ℝ, 0 < ε →
        ∃ H : FinitePoint n → ℂ × ℂ,
          Continuous H ∧
          (∃ U : Set (FinitePoint n), IsOpen U ∧ polydisc n S ⊆ U ∧
            DifferentiableOn ℂ H U) ∧
          (∀ k : ℕ, 1 ≤ k → k ≤ n →
            ∀ z ∈ finiteFlag n k, (k : ℝ) < euclideanPairNorm (H z)) ∧
          (∀ z ∈ polydisc n R, euclideanPairNorm (H z - h z) < ε)

namespace FlagLocalExtension

open Set Filter Metric
open scoped Topology

def radius (R : ℝ) (m : ℕ) : ℝ := R + m

theorem radius_nonneg {R : ℝ} (hR : 0 ≤ R) (m : ℕ) : 0 ≤ radius R m :=
  add_nonneg hR (Nat.cast_nonneg m)

theorem radius_lt_succ (R : ℝ) (m : ℕ) : radius R m < radius R (m + 1) := by
  simp [radius]

theorem polydisc_mono (n : ℕ) {r s : ℝ} (hrs : r ≤ s) :
    polydisc n r ⊆ polydisc n s := fun _ hz j => (hz j).trans hrs

theorem polydisc_radius_monotone (n : ℕ) (R : ℝ) : Monotone (fun m => polydisc n (radius R m)) := by
  intro i j hij
  exact polydisc_mono n (add_le_add le_rfl (Nat.cast_le.mpr hij))

theorem polydisc_radius_exhaustive (n : ℕ) (R : ℝ) (z : FinitePoint n) :
    ∃ m : ℕ, z ∈ polydisc n (radius R m) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (‖z‖ - R)
  refine ⟨m, fun j => (norm_le_pi_norm z j).trans ?_⟩
  dsimp [radius]
  linarith

/-- A stage carries a positive tolerance that preserves all bounds over its
current compact polydisc, in addition to genuine holomorphic-neighbourhood data. -/
structure Stage (n : ℕ) (R : ℝ) (m : ℕ) where
  map : FinitePoint n → ℂ × ℂ
  continuous : Continuous map
  holomorphicNear : ∃ U : Set (FinitePoint n), IsOpen U ∧
    polydisc n (radius R m) ⊆ U ∧ DifferentiableOn ℂ map U
  bounds : ∀ k : ℕ, 1 ≤ k → k ≤ n →
    ∀ z ∈ finiteFlag n k, (k : ℝ) < euclideanPairNorm (map z)
  budget : ℝ
  budget_pos : 0 < budget
  tube : ∀ z ∈ polydisc n (radius R m), ∀ v : ℂ × ℂ,
    euclideanPairNorm (v - map z) ≤ budget → (z, v) ∈ FlagTotalSpace.totalSet n

theorem exists_stage {n m : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (h : FinitePoint n → ℂ × ℂ) (hc : Continuous h)
    (hh : ∃ U : Set (FinitePoint n), IsOpen U ∧
      polydisc n (radius R m) ⊆ U ∧ DifferentiableOn ℂ h U)
    (hb : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      ∀ z ∈ finiteFlag n k, (k : ℝ) < euclideanPairNorm (h z))
    {cap : ℝ} (hcap : 0 < cap) :
    ∃ s : Stage n R m, s.map = h ∧ s.budget ≤ cap := by
  obtain ⟨δ, hδ, htube⟩ := FlagTotalSpace.exists_uniform_tube
    (isCompact_polydisc n (radius_nonneg hR m)) hc.continuousOn
    (fun z _ k hk hkn hz => hb k hk hkn z hz)
  refine ⟨⟨h, hc, hh, hb, min cap δ, lt_min hcap hδ, ?_⟩, rfl, min_le_left _ _⟩
  intro z hz v hv
  exact htube z hz v (hv.trans (min_le_right _ _))

/-- One application of local extension, with the next tolerance at most half
the preceding tolerance. -/
theorem exists_next_stage (hExtension : FiniteFlagLocalExtensionStatement)
    {n : ℕ} (hn : 1 ≤ n) {R : ℝ} (hR : 0 ≤ R)
    (m : ℕ) (s : Stage n R m) :
    ∃ t : Stage n R (m + 1), t.budget ≤ s.budget / 2 ∧
      ∀ z ∈ polydisc n (radius R m),
        euclideanPairNorm (t.map z - s.map z) < s.budget / 4 := by
  obtain ⟨H, hc, hh, hb, ha⟩ := hExtension n hn (radius R m) (radius R (m + 1))
    (radius_nonneg hR m) (radius_lt_succ R m) s.map s.continuous s.holomorphicNear
    s.bounds (s.budget / 4) (div_pos s.budget_pos (by norm_num))
  obtain ⟨t, ht, hbudget⟩ := exists_stage hR H hc hh hb (half_pos s.budget_pos)
  refine ⟨t, hbudget, ?_⟩
  simpa only [ht] using ha

/-- Dependent choice constructs all finite stages and their adaptive budgets. -/
theorem exists_stages (hExtension : FiniteFlagLocalExtensionStatement)
    {n : ℕ} (hn : 1 ≤ n) {R : ℝ} (hR : 0 ≤ R) (s₀ : Stage n R 0) :
    ∃ s : (m : ℕ) → Stage n R m, s 0 = s₀ ∧
      (∀ m, (s (m + 1)).budget ≤ (s m).budget / 2) ∧
      (∀ m, ∀ z ∈ polydisc n (radius R m),
        euclideanPairNorm ((s (m + 1)).map z - (s m).map z) < (s m).budget / 4) := by
  classical
  choose next hbudget happrox using exists_next_stage hExtension hn hR
  let s : (m : ℕ) → Stage n R m := fun m => Nat.rec s₀ (fun m t => next m t) m
  exact ⟨s, rfl, fun m => hbudget m (s m), fun m => happrox m (s m)⟩

end FlagLocalExtension

/-- The compact local enlargement step suffices for the full global
approximation theorem. Adaptive positive error budgets retain strict bounds
on every flag, rather than merely non-strict inequalities at the limit. -/
theorem finiteFlagApproximation_of_localExtension
    (hExtension : FiniteFlagLocalExtensionStatement) : FiniteFlagApproximationStatement := by
  classical
  intro n hn R hR h hc hh hb ε hε
  have hh₀ : ∃ U : Set (FinitePoint n), IsOpen U ∧
      polydisc n (FlagLocalExtension.radius R 0) ⊆ U ∧ DifferentiableOn ℂ h U := by
    simpa only [FlagLocalExtension.radius, Nat.cast_zero, add_zero] using hh
  obtain ⟨s₀, hs₀, hbudget₀⟩ := FlagLocalExtension.exists_stage hR h hc hh₀ hb (half_pos hε)
  obtain ⟨s, hs, hbudget, hstep⟩ := FlagLocalExtension.exists_stages hExtension hn hR s₀
  obtain ⟨G, hlim, hclose⟩ := AdaptiveUniformLimit.exists_limit
    (fun m => polydisc n (FlagLocalExtension.radius R m))
    (FlagLocalExtension.polydisc_radius_monotone n R)
    (FlagLocalExtension.polydisc_radius_exhaustive n R)
    (fun m => (s m).map) (fun m => (s m).budget)
    (fun m => (s m).budget_pos) hbudget
    (fun m z hz => (norm_le_euclideanPairNorm _).trans (hstep m z hz).le)
  have heclose : ∀ m, ∀ z ∈ polydisc n (FlagLocalExtension.radius R m),
      euclideanPairNorm (G z - (s m).map z) ≤ (s m).budget := by
    intro m z hz
    have h₁ := hclose m z hz
    have h₂ := euclideanPairNorm_le_two_mul_norm (G z - (s m).map z)
    linarith
  refine ⟨G, ?_, ?_, ?_⟩
  · intro z
    obtain ⟨m, hm⟩ := exists_nat_gt (‖z‖ - R)
    have hz : z ∈ Metric.ball 0 (FlagLocalExtension.radius R m) := by
      rw [Metric.mem_ball, dist_zero_right]
      dsimp [FlagLocalExtension.radius]
      linarith
    have hball : Metric.ball (0 : FinitePoint n) (FlagLocalExtension.radius R m) ⊆
        polydisc n (FlagLocalExtension.radius R m) := by
      rw [polydisc_eq_closedBall n (FlagLocalExtension.radius_nonneg hR m)]
      exact Metric.ball_subset_closedBall
    have hdiff : ∀ i : ℕ, DifferentiableOn ℂ ((s (i + m)).map)
        (Metric.ball 0 (FlagLocalExtension.radius R m)) := by
      intro i
      obtain ⟨U, _hU, hKU, hd⟩ := (s (i + m)).holomorphicNear
      exact hd.mono (hball.trans
        ((FlagLocalExtension.polydisc_radius_monotone n R (by omega)).trans hKU))
    have hshift : TendstoUniformlyOn (fun i => (s (i + m)).map) G Filter.atTop
        (polydisc n (FlagLocalExtension.radius R m)) := by
      intro u hu
      exact (Filter.tendsto_add_atTop_nat m).eventually (hlim m u hu)
    have hG := SeveralVariableUniformLimit.differentiableOn_of_tendstoUniformlyOn_ball
      hdiff (hshift.mono hball)
    exact hG.differentiableAt (Metric.isOpen_ball.mem_nhds hz)
  · intro z hz
    have hm := heclose 0 z (by simpa only [FlagLocalExtension.radius, Nat.cast_zero, add_zero] using hz)
    have hmap : (s 0).map = h := by rw [hs]; exact hs₀
    rw [hmap] at hm
    apply hm.trans_lt
    have hbud : (s 0).budget ≤ ε / 2 := by rw [hs]; exact hbudget₀
    exact hbud.trans_lt (half_lt_self hε)
  · intro k hk hkn z hz
    obtain ⟨m, hm⟩ := FlagLocalExtension.polydisc_radius_exhaustive n R z
    have hmem := (s m).tube z hm (G z) (heclose m z hm)
    exact FlagTotalSpace.mem_totalSet_iff.mp hmem k hk hkn hz

/-- The global theorem of course gives each compact enlargement. Together
with the preceding exhaustion proof this identifies the exact remaining task. -/
theorem finiteFlagLocalExtension_of_approximation
    (hApproximation : FiniteFlagApproximationStatement) : FiniteFlagLocalExtensionStatement := by
  intro n hn R S hR _hRS h hc hh hb ε hε
  obtain ⟨H, hH, ha, hbound⟩ := hApproximation n hn R hR h hc hh hb ε hε
  exact ⟨H, hH.continuous, ⟨Set.univ, isOpen_univ, Set.subset_univ _, hH.differentiableOn⟩,
    hbound, ha⟩

theorem finiteFlagLocalExtension_iff_approximation :
    FiniteFlagLocalExtensionStatement ↔ FiniteFlagApproximationStatement :=
  ⟨finiteFlagApproximation_of_localExtension, finiteFlagLocalExtension_of_approximation⟩

end AutomaticContinuity
