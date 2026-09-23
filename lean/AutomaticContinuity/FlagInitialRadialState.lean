import AutomaticContinuity.FlagGraphCutoff
import AutomaticContinuity.FlagCenteredSeparator
import AutomaticContinuity.RadialPushIteration

set_option autoImplicit false

/-!
# A genuine initial iteration state for the forbidden flag graph

Every premise of the radial iteration state is discharged from the original
admissible section and compact forbidden graph. The separator is selected by
the proved polynomial-function-algebra cutoff theorem, then translated into
the actual fibre polynomial family. The retained obstacle is exactly the
original forbidden graph centered along the section.
-/

noncomputable section

namespace AutomaticContinuity.FlagInitialRadialState

open Set FlagPolynomialSeparation FlagTotalSpace FlagCenteredSeparator
open CenteredPolynomialFamily

theorem exists_initial_state {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (h : FinitePoint n → ℂ × ℂ) {U : Set (FinitePoint n)} (hU : IsOpen U)
    (hKU : polydisc n R ⊆ U) (hh : DifferentiableOn ℂ h U)
    (hadm : ∀ z ∈ polydisc n R, (z, h z) ∈ totalSet n) :
    ∃ S : RadialPushIteration.State (polydisc n R) U,
      S.obstacle = centeredObstacle h (compactForbiddenGraph n R) := by
  obtain ⟨q, hqgraph, hqobstacle⟩ := FlagGraphCutoff.exists_forbidden_graph_separator
    hR h hU hKU hh hadm (by norm_num : (0 : ℝ) < 1 / 32)
  have hbase : compactForbiddenGraph n R ⊆ polydisc n R ×ˢ univ :=
    fun z hz => ⟨(mem_compactForbiddenGraph_iff.mp hz).1, mem_univ _⟩
  obtain ⟨a, ha, hKc, hKbase, hzero, hone, _⟩ := exists_separator_data q h
    (isCompact_polydisc n hR) (isCompact_compactForbiddenGraph n hR) hU hKU hbase
    hh.continuousOn (fun p hp => (hqgraph p hp).le) (fun z hz => (hqobstacle z hz).le)
  refine ⟨{
    radius := a
    radius_pos := ha
    degree := q.totalDegree
    obstacle := centeredObstacle h (compactForbiddenGraph n R)
    compact_obstacle := hKc
    obstacle_base := hKbase
    polynomial := polynomial q h
    holomorphic_coefficients := holomorphicCoefficientsOn_polynomial q h hh
    degree_bound := fun p _ => totalDegree_polynomial_le q h p
    small_on_cylinder := hzero
    near_one_on_obstacle := fun z hz => (hone z hz).trans (by norm_num)
  }, rfl⟩

end AutomaticContinuity.FlagInitialRadialState
