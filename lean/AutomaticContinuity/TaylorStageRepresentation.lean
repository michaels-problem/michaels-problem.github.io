import AutomaticContinuity.TaylorRepresentation
import AutomaticContinuity.AnalyticBridge

set_option autoImplicit false

/-!
# Taylor representatives and sharp coefficient bounds for the finite stages

This discharges the representation statement for the actual entire finite-stage
maps. The old stage is embedded by an exact zero-extension identity before the
Cauchy estimate is applied to their difference.
-/

noncomputable section

namespace AutomaticContinuity

open CoefficientSeries FiniteTaylor

/-- Entire finite stages have actual coefficient-series representatives with
the precise geometric bounds required for their limits in `CoefficientSeries`. -/
theorem coefficientStageRepresentation : CoefficientStageRepresentationStatement := by
  intro F hEntire hApprox
  let f : ℕ → CoefficientSeries := fun n =>
    if hn : 1 ≤ n then ofEntire (fun z => (F n z).1) (hEntire n hn).fst else 0
  let g : ℕ → CoefficientSeries := fun n =>
    if hn : 1 ≤ n then ofEntire (fun z => (F n z).2) (hEntire n hn).snd else 0
  refine ⟨f, g, ?_, ?_, ?_⟩
  · intro n hn w
    simp only [f, g, dite_eq_left hn]
    rw [evaluate_ofEntire, evaluate_ofEntire]
  · intro n hn
    have hn' : 1 ≤ n + 1 := by omega
    simp only [f, dite_eq_left hn, dite_eq_left hn']
    apply q_sub_ofEntire_le
    intro z hz
    exact (norm_fst_le_euclideanPairNorm (F (n + 1) z - F n (prefixProjection n z))).trans
      (hApprox n hn z hz).le
  · intro n hn
    have hn' : 1 ≤ n + 1 := by omega
    simp only [g, dite_eq_left hn, dite_eq_left hn']
    apply q_sub_ofEntire_le
    intro z hz
    exact (norm_snd_le_euclideanPairNorm (F (n + 1) z - F n (prefixProjection n z))).trans
      (hApprox n hn z hz).le

end AutomaticContinuity
