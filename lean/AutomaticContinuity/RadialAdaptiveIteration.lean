import AutomaticContinuity.RadialPushIteration
import AutomaticContinuity.AdaptiveInverseControl
import AutomaticContinuity.AdaptiveUniformLimit

set_option autoImplicit false

/-! # Actual adaptive inverse budgets for the coherent radial push

At every stage the compact uniform-continuity tolerance is extracted from
the already chosen cumulative inverse. The next real push uses the smaller
of this tolerance and the prescribed factor error. No modulus uniform over
all possible histories is assumed.
-/

noncomputable section

namespace AutomaticContinuity.RadialAdaptiveIteration

open Set Filter FlagTotalSpace RadialPushIteration
open scoped Topology

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
variable {L U : Set P}

abbrev Pair := ℂ × ℂ

def cylinder (A : Prefix L U) : Set (P × Pair) := L ×ˢ closedEuclideanBall A.state.radius

theorem exists_inverse_tolerance (hL : IsCompact L) (hU : IsOpen U) (hLU : L ⊆ U)
    (A : Prefix L U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ψ : P → Pair ≃ₜ Pair,
      (∀ z ∈ cylinder A, euclideanPairNorm ((ψ z.1).symm z.2 - z.2) ≤ δ) →
      ∀ z ∈ cylinder A,
        euclideanPairNorm (((A.cumulative z.1).trans (ψ z.1)).symm z.2 -
          (A.cumulative z.1).symm z.2) < ε :=
  AdaptiveInverseControl.exists_composed_inverse_increment A.cumulative
    (hL.prod (isCompact_closedEuclideanBall A.state.radius)) hU
    (fun _ hz => ⟨hLU hz.1, mem_univ _⟩) A.inverse_holomorphic.continuousOn hε

def inverseTolerance (hL : IsCompact L) (hU : IsOpen U) (hLU : L ⊆ U)
    (A : Prefix L U) {ε : ℝ} (hε : 0 < ε) : ℝ :=
  Classical.choose (exists_inverse_tolerance hL hU hLU A hε)

theorem inverseTolerance_spec (hL : IsCompact L) (hU : IsOpen U) (hLU : L ⊆ U)
    (A : Prefix L U) {ε : ℝ} (hε : 0 < ε) :
    0 < inverseTolerance hL hU hLU A hε ∧ ∀ ψ : P → Pair ≃ₜ Pair,
      (∀ z ∈ cylinder A, euclideanPairNorm ((ψ z.1).symm z.2 - z.2) ≤
        inverseTolerance hL hU hLU A hε) →
      ∀ z ∈ cylinder A,
        euclideanPairNorm (((A.cumulative z.1).trans (ψ z.1)).symm z.2 -
          (A.cumulative z.1).symm z.2) < ε :=
  Classical.choose_spec (exists_inverse_tolerance hL hU hLU A hε)

def budget (hL : IsCompact L) (hU : IsOpen U) (hLU : L ⊆ U)
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n) (n : ℕ) (A : Prefix L U) : ℝ :=
  min (b n / 4) (inverseTolerance hL hU hLU A (ε := b n / 4)
    (div_pos (hb n) (by norm_num)))

theorem budget_pos (hL : IsCompact L) (hU : IsOpen U) (hLU : L ⊆ U)
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n) (n : ℕ) (A : Prefix L U) :
    0 < budget hL hU hLU b hb n A := by
  unfold budget
  exact lt_min (div_pos (hb n) (by norm_num))
    (inverseTolerance_spec hL hU hLU A (ε := b n / 4) _).1

theorem factor_errors (hL : IsCompact L) (hU : IsOpen U) (hLU : L ⊆ U)
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n) {S₀ : State L U}
    (I : ControlledIteration S₀ (budget hL hU hLU b hb)) (n : ℕ)
    {z : P × Pair} (hz : z ∈ cylinder (I.history n)) :
    euclideanPairNorm ((I.step n).map z.1 z.2 - z.2) < b n / 4 ∧
    euclideanPairNorm (((I.step n).map z.1).symm z.2 - z.2) < b n / 4 := by
  obtain ⟨hf, hi⟩ := (I.step n).protected_error z hz
  have hbudget : budget hL hU hLU b hb n (I.history n) ≤ b n / 4 := by
    unfold budget
    exact min_le_left _ _
  exact ⟨hf.trans_le hbudget, hi.trans_le hbudget⟩

theorem inverse_increment (hL : IsCompact L) (hU : IsOpen U) (hLU : L ⊆ U)
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n) {S₀ : State L U}
    (I : ControlledIteration S₀ (budget hL hU hLU b hb)) (n : ℕ)
    {z : P × Pair} (hz : z ∈ cylinder (I.history n)) :
    euclideanPairNorm (((I.history (n + 1)).cumulative z.1).symm z.2 -
      ((I.history n).cumulative z.1).symm z.2) < b n / 4 := by
  have hε : 0 < b n / 4 := div_pos (hb n) (by norm_num)
  have hbudget : budget hL hU hLU b hb n (I.history n) ≤
      inverseTolerance hL hU hLU (I.history n) hε := by
    unfold budget
    exact min_le_right _ _
  have hh := (inverseTolerance_spec hL hU hLU (I.history n) hε).2 (I.step n).map
    (fun w hw => ((I.step n).protected_error w hw).2.le.trans hbudget) z hz
  rw [I.successor n]
  exact hh

/-- The same bound with the explicit geometric cylinder radius, convenient
for convergence theorems stated independently of the iteration data. -/
theorem inverse_increment_on_geometric_cylinder
    (hL : IsCompact L) (hU : IsOpen U) (hLU : L ⊆ U)
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n) {S₀ : State L U}
    (I : ControlledIteration S₀ (budget hL hU hLU b hb)) (n : ℕ)
    {z : P × Pair} (hz : z ∈ L ×ˢ closedEuclideanBall ((2 : ℝ) ^ n * S₀.radius)) :
    euclideanPairNorm (((I.history (n + 1)).cumulative z.1).symm z.2 -
      ((I.history n).cumulative z.1).symm z.2) < b n / 4 := by
  apply inverse_increment hL hU hLU b hb I n
  have hr : (I.history n).state.radius = (2 : ℝ) ^ n * S₀.radius :=
    I.toIteration.radius n
  simpa only [cylinder, hr] using hz

/-- The inverse-control controller is actually instantiated by a coherent
sequence, rather than left as an unspecified positive function. -/
theorem exists_adaptive_iteration [ProperSpace P]
    (hL : IsCompact L) (hU : IsOpen U) (hLU : L ⊆ U)
    (S₀ : State L U) (b : ℕ → ℝ) (hb : ∀ n, 0 < b n) :
    Nonempty (ControlledIteration S₀ (budget hL hU hLU b hb)) :=
  exists_controlled_iteration hL hU hLU S₀ (budget hL hU hLU b hb)
    (budget_pos hL hU hLU b hb)

end AutomaticContinuity.RadialAdaptiveIteration
