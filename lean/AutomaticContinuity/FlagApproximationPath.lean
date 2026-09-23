import AutomaticContinuity.FlagSectionApproximation
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

/-!
# Propagation of section approximability along a continuous compact path

Joint continuity on `[0,1] × K` supplies continuity in the uniform Euclidean
topology. Approximable times are therefore closed. Their openness remains
an explicitly named premise; connectedness then propagates an approximable
endpoint along the path. This file proves no analytic openness theorem.
-/

noncomputable section

namespace AutomaticContinuity.FlagSectionApproximation

open Set

abbrev Time := Icc (0 : ℝ) 1

theorem uniformFamily_of_continuous_path {n : ℕ} {K : Set (FinitePoint n)}
    (hK : IsCompact K) (H : ℝ × FinitePoint n → Pair)
    (hH : ContinuousOn H (Icc 0 1 ×ˢ K)) :
    UniformFamily K (fun t : Time => fun z => H (t.val, z)) := by
  have huc := (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hH
  intro t ε hε
  obtain ⟨δ, hδ, hcontrol⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro s hst z hz
  have hd : dist (s.val, z) (t.val, z) < δ := by
    simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Subtype.dist_eq] using hst
  have herr := hcontrol (s.val, z) ⟨s.property, hz⟩ (t.val, z) ⟨t.property, hz⟩ hd
  rw [dist_eq_norm] at herr
  exact (euclideanPairNorm_le_two_mul_norm _).trans_lt (by linarith)

/-- The analytic open-condition is kept separate from the proved compact-path
continuity and closedness facts. -/
def OpenAlongPath {n : ℕ} (K L : Set (FinitePoint n))
    (H : ℝ × FinitePoint n → Pair) : Prop :=
  OpenParameters K L (fun t : Time => fun z => H (t.val, z))

theorem isClosed_approximable_times {n : ℕ} {K : Set (FinitePoint n)}
    (hK : IsCompact K) (L : Set (FinitePoint n)) (H : ℝ × FinitePoint n → Pair)
    (hH : ContinuousOn H (Icc 0 1 ×ˢ K)) :
    IsClosed {t : Time | Approximable K L (fun z => H (t.val, z))} :=
  isClosed_approximable_parameters K L _ (uniformFamily_of_continuous_path hK H hH)

/-- A path ending at an approximable section starts at an approximable
section, provided the separately stated analytic openness has been proved. -/
theorem approximable_zero_of_open_path {n : ℕ} {K : Set (FinitePoint n)}
    (hK : IsCompact K) (L : Set (FinitePoint n)) (H : ℝ × FinitePoint n → Pair)
    (hH : ContinuousOn H (Icc 0 1 ×ˢ K)) (hopen : OpenAlongPath K L H)
    (h1 : Approximable K L (fun z => H (1, z))) :
    Approximable K L (fun z => H (0, z)) := by
  let : PreconnectedSpace Time := Subtype.preconnectedSpace isPreconnected_Icc
  exact all_approximable_of_open K L (fun t : Time => fun z => H (t.val, z))
    (uniformFamily_of_continuous_path hK H hH) hopen ⟨1, by norm_num⟩ h1 ⟨0, by norm_num⟩

/-- The terminal section may instead be supplied directly as a holomorphic
admissible extension near the larger target set. -/
theorem approximable_zero_of_open_path_extension {n : ℕ} {K L U : Set (FinitePoint n)}
    (hK : IsCompact K) (H : ℝ × FinitePoint n → Pair)
    (hH : ContinuousOn H (Icc 0 1 ×ˢ K)) (hopen : OpenAlongPath K L H)
    (hU : IsOpen U) (hLU : L ⊆ U)
    (hhol : DifferentiableOn ℂ (fun z => H (1, z)) U)
    (hadm : ∀ z ∈ U, (z, H (1, z)) ∈ FlagTotalSpace.totalSet n) :
    Approximable K L (fun z => H (0, z)) :=
  approximable_zero_of_open_path hK L H hH hopen
    (approximable_of_extension _ hU hLU hhol hadm)

end AutomaticContinuity.FlagSectionApproximation
