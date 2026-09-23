import AutomaticContinuity.FlagAdditiveGluing
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option autoImplicit false

/-!
# Approximability by admissible sections near a specified larger compact set

The predicate retains the actual flag constraints and a genuine open
neighbourhood of the target set. Closure under uniform convergence is proved
by the triangle inequality. Openness is a separate analytic obligation and
is never inferred from the existence of a local fibre family alone.
-/

noncomputable section

namespace AutomaticContinuity.FlagSectionApproximation

open Set Filter FlagTotalSpace
open scoped Topology

abbrev Pair := ℂ × ℂ

/-- Uniform Euclidean approximation on `K` by actual holomorphic admissible
sections on an open neighbourhood of `L`. -/
def Approximable {n : ℕ} (K L : Set (FinitePoint n)) (h : FinitePoint n → Pair) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (f : FinitePoint n → Pair) (U : Set (FinitePoint n)),
    IsOpen U ∧ L ⊆ U ∧ DifferentiableOn ℂ f U ∧
    (∀ z ∈ U, (z, f z) ∈ totalSet n) ∧
    ∀ z ∈ K, euclideanPairNorm (f z - h z) < ε

theorem approximable_of_extension {n : ℕ} {K L U : Set (FinitePoint n)}
    (h : FinitePoint n → Pair) (hU : IsOpen U) (hLU : L ⊆ U)
    (hh : DifferentiableOn ℂ h U) (hadm : ∀ z ∈ U, (z, h z) ∈ totalSet n) :
    Approximable K L h := by
  intro ε hε
  exact ⟨h, U, hU, hLU, hh, hadm, fun z _ => by
    simpa only [sub_self, euclideanPairNorm_zero] using hε⟩

theorem Approximable.congr {n : ℕ} {K L : Set (FinitePoint n)}
    {f g : FinitePoint n → Pair} (hf : Approximable K L f) (heq : EqOn f g K) :
    Approximable K L g := by
  intro ε hε
  obtain ⟨a, U, hU, hLU, ha, hadm, hclose⟩ := hf ε hε
  exact ⟨a, U, hU, hLU, ha, hadm, fun z hz => by rw [← heq hz]; exact hclose z hz⟩

/-- The approximating sections may vary with the tolerance; no compatibility
or uniform neighbourhood for them is assumed in this closure lemma. -/
theorem approximable_of_arbitrarily_close {n : ℕ} {K L : Set (FinitePoint n)}
    (h : FinitePoint n → Pair)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ g : FinitePoint n → Pair,
      Approximable K L g ∧ ∀ z ∈ K, euclideanPairNorm (g z - h z) < ε) :
    Approximable K L h := by
  intro ε hε
  obtain ⟨g, hg, hgh⟩ := hclose (ε / 2) (half_pos hε)
  obtain ⟨f, U, hU, hLU, hf, hadm, hfg⟩ := hg (ε / 2) (half_pos hε)
  refine ⟨f, U, hU, hLU, hf, hadm, ?_⟩
  intro z hz
  have htri := euclideanPairNorm_add_le (f z - g z) (g z - h z)
  rw [sub_add_sub_cancel] at htri
  exact htri.trans_lt (by linarith [hfg z hz, hgh z hz])

/-- Uniform limits of approximable sections are approximable. The incoming
limit uses the ordinary product metric; the conclusion retains Euclidean
error, with the explicit factor-two comparison in the proof. -/
theorem approximable_of_tendstoUniformlyOn {n : ℕ} {K L : Set (FinitePoint n)}
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (f : ι → FinitePoint n → Pair) (h : FinitePoint n → Pair)
    (hf : ∀ i, Approximable K L (f i)) (hlim : TendstoUniformlyOn f h l K) :
    Approximable K L h := by
  apply approximable_of_arbitrarily_close h
  intro ε hε
  obtain ⟨i, hi⟩ := (Metric.tendstoUniformlyOn_iff.mp hlim (ε / 2) (half_pos hε)).exists
  refine ⟨f i, hf i, ?_⟩
  intro z hz
  have herr := hi z hz
  rw [dist_comm, dist_eq_norm] at herr
  exact (euclideanPairNorm_le_two_mul_norm _).trans_lt (by linarith)

/-- Continuity of a family in the uniform Euclidean topology on `K`. -/
def UniformFamily {n : ℕ} {T : Type*} [PseudoMetricSpace T]
    (K : Set (FinitePoint n)) (H : T → FinitePoint n → Pair) : Prop :=
  ∀ t : T, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ s : T, dist s t < δ → ∀ z ∈ K, euclideanPairNorm (H s z - H t z) < ε

/-- Closedness of the set of approximable family members is unconditional
once continuity in the uniform topology has been supplied. -/
theorem isClosed_approximable_parameters {n : ℕ} {T : Type*} [PseudoMetricSpace T]
    (K L : Set (FinitePoint n)) (H : T → FinitePoint n → Pair)
    (hH : UniformFamily K H) : IsClosed {t : T | Approximable K L (H t)} := by
  apply isClosed_of_closure_subset
  intro t ht
  apply approximable_of_arbitrarily_close (H t)
  intro ε hε
  obtain ⟨δ, hδ, hcontrol⟩ := hH t ε hε
  obtain ⟨s, hs, hdist⟩ := Metric.mem_closure_iff.mp ht δ hδ
  exact ⟨H s, hs, hcontrol s (by simpa only [dist_comm] using hdist)⟩

/-- This is the remaining analytic openness assertion, stated separately
from closedness and the connectedness argument. -/
def OpenParameters {n : ℕ} {T : Type*} [TopologicalSpace T]
    (K L : Set (FinitePoint n)) (H : T → FinitePoint n → Pair) : Prop :=
  IsOpen {t : T | Approximable K L (H t)}

theorem all_approximable_of_open {n : ℕ} {T : Type*}
    [PseudoMetricSpace T] [PreconnectedSpace T]
    (K L : Set (FinitePoint n)) (H : T → FinitePoint n → Pair)
    (hH : UniformFamily K H) (hopen : OpenParameters K L H)
    (t₀ : T) (hstart : Approximable K L (H t₀)) :
    ∀ t : T, Approximable K L (H t) := by
  have hc : IsClopen {t : T | Approximable K L (H t)} :=
    ⟨isClosed_approximable_parameters K L H hH, hopen⟩
  have hall := hc.eq_univ ⟨t₀, hstart⟩
  intro t
  have ht : t ∈ ({s : T | Approximable K L (H s)} : Set T) := by
    rw [hall]
    exact mem_univ t
  exact ht

end AutomaticContinuity.FlagSectionApproximation
