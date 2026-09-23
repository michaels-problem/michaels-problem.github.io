import AutomaticContinuity.CoefficientConvergence
import AutomaticContinuity.ContinuousCharacters
import AutomaticContinuity.FiniteStages
import AutomaticContinuity.ProofObligations

/-!
# The finite-dimensional analytic bridge and escape limit

The representation statement below asks for actual coefficient series
representing the entire stage maps, with the precise Cauchy-derived coefficient
estimates. `TaylorStageRepresentation.lean` proves it. The limit argument here
retains that interface explicitly; the construction of finite stages remains
unproved.
-/

namespace AutomaticContinuity

open CoefficientSeries Filter
open scoped Topology

/-- Taylor expansion and finite-polydisc Cauchy estimates in exactly the form
needed by the manuscript. The zero-dimensional terms are unrestricted.
This is a proposition definition, not an imported or assumed theorem. -/
def CoefficientStageRepresentationStatement : Prop :=
  ∀ F : (n : ℕ) → FinitePoint n → ℂ × ℂ,
    (∀ n : ℕ, 1 ≤ n → Differentiable ℂ (F n)) →
    (∀ n : ℕ, 1 ≤ n →
      ∀ z ∈ polydisc (n + 1) (2 * ((n + 1 : ℕ) : ℝ)),
        euclideanPairNorm (F (n + 1) z - F n (prefixProjection n z)) <
          ((2 : ℝ) ^ (3 * (n + 1)))⁻¹) →
    ∃ f g : ℕ → CoefficientSeries,
      (∀ n : ℕ, 1 ≤ n → ∀ w : BoundedSequence,
        (evaluate w (f n), evaluate w (g n)) = F n (restrictSequence n w)) ∧
      (∀ n : ℕ, 1 ≤ n →
        q (n + 1) (f (n + 1) - f n) ≤ (1 / 4 : ℝ) ^ (n + 1)) ∧
      (∀ n : ℕ, 1 ≤ n →
        q (n + 1) (g (n + 1) - g n) ≤ (1 / 4 : ℝ) ^ (n + 1))

/-- The formal convergence part of the escape construction. The stage and
representation interfaces remain visible in the type. -/
theorem escapePair_of_finiteStages_and_representation
    (hStages : FiniteStageConstructionStatement)
    (hRepresentation : CoefficientStageRepresentationStatement) : EscapePairStatement := by
  obtain ⟨F, hEntire, _, hBounds, hApprox⟩ := hStages
  obtain ⟨f, g, hEval, hf, hg⟩ := hRepresentation F hEntire hApprox
  obtain ⟨flim, hflim⟩ := exists_limit_of_successive_q_bound f hf
  obtain ⟨glim, hglim⟩ := exists_limit_of_successive_q_bound g hg
  refine ⟨flim, glim, ?_⟩
  apply isEscapeMap_of_finiteStage_tendsto (Fstage := F) (hbound := hBounds)
  intro w
  have hfeval : Tendsto (fun n => evaluate w (f n)) atTop (𝓝 (evaluate w flim)) :=
    (continuous_evaluationHom w).continuousAt.tendsto.comp hflim
  have hgeval : Tendsto (fun n => evaluate w (g n)) atTop (𝓝 (evaluate w glim)) :=
    (continuous_evaluationHom w).continuousAt.tendsto.comp hglim
  apply (hfeval.prodMk_nhds hgeval).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact hEval n hn w

end AutomaticContinuity
