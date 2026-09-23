import AutomaticContinuity.FlagGraphCutoff
import AutomaticContinuity.FlagPolynomialExpulsion

set_option autoImplicit false

/-!
# Expelling the actual forbidden flag graph near an admissible section

This endpoint supplies its own polynomial separator. Its hypotheses are the
actual compact forbidden graph, a section holomorphic on an open neighbourhood
of the source polydisc, and admissibility on that polydisc. It produces an
actual fibre automorphism fixing the section, with both directions locally
jointly holomorphic and uniformly near the identity on a positive section
tube, while expelling the entire compact forbidden graph beyond a prescribed
Euclidean radius.

This is a compact push theorem. It does not assert the full noncompact flag
approximation theorem or complete Theorem A.
-/

noncomputable section

namespace AutomaticContinuity.FlagObstaclePush

open Set FlagPolynomialSeparation FlagTotalSpace

abbrev Pair := ℂ × ℂ

theorem exists_forbidden_graph_push {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (h : FinitePoint n → Pair) {U : Set (FinitePoint n)} (hU : IsOpen U)
    (hKU : polydisc n R ⊆ U) (hh : DifferentiableOn ℂ h U)
    (hadm : ∀ z ∈ polydisc n R, (z, h z) ∈ totalSet n)
    (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∃ Ψ : FinitePoint n → Pair ≃ₜ Pair,
      (∀ p, Ψ p (h p) = h p) ∧
      DifferentiableOn ℂ (fun z : Point n => Ψ z.1 z.2) (U ×ˢ univ) ∧
      DifferentiableOn ℂ (fun z : Point n => (Ψ z.1).symm z.2) (U ×ˢ univ) ∧
      (∀ p ∈ polydisc n R, ∀ w : Pair, euclideanPairNorm (w - h p) ≤ a →
        euclideanPairNorm (Ψ p w - w) < ε ∧ euclideanPairNorm ((Ψ p).symm w - w) < ε) ∧
      (∀ z ∈ compactForbiddenGraph n R, r < euclideanPairNorm (Ψ z.1 z.2)) := by
  obtain ⟨q, hqgraph, hqobstacle⟩ := FlagGraphCutoff.exists_forbidden_graph_separator
    hR h hU hKU hh hadm (by norm_num : (0 : ℝ) < 1 / 32)
  exact FlagPolynomialPush.exists_section_expelling_push q h r
    (isCompact_polydisc n hR) (isCompact_compactForbiddenGraph n hR) hU hKU
    (fun z hz => ⟨(mem_compactForbiddenGraph_iff.mp hz).1, mem_univ _⟩) hh
    (fun p hp => (hqgraph p hp).le) (fun z hz => (hqobstacle z hz).le) hε

end AutomaticContinuity.FlagObstaclePush
