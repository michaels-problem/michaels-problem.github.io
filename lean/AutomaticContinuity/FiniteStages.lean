import AutomaticContinuity.Flags
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Finite-dimensional stages of the escape construction

This module gives inspectable definitions for the finite-dimensional construction
in Section 3.2 of `automatic_continuity_characters.tex`, equations `finite-escape`
and `approximation`. `FiniteStageConstructionStatement` is an unproved proposition
definition. In particular it is not an axiom and supplies no stage maps.

Coordinates remain zero based, while the dimension and the number of fixed
coordinates are the paper's positive integers. An unused zero-dimensional stage
is permitted to make the family easy to index.

The ambient products carry Mathlib's usual norm for the differentiability and
topology definitions. Every quantitative target norm is nevertheless explicitly
`euclideanPairNorm`, the Euclidean norm required by the manuscript. No quantitative
bound uses the default product maximum norm.
-/

namespace AutomaticContinuity

open Filter
open scoped Topology

/-- The finite-dimensional coordinate model of `ℂⁿ`. -/
abbrev FinitePoint (n : ℕ) := Fin n → ℂ

/-- The affine flag fixes the first `k` coordinates. The construction uses this
with `1 ≤ k ≤ n`; the definition is also harmless outside that range. -/
def finiteFlag (n k : ℕ) : Set (FinitePoint n) :=
  {z | ∀ j : Fin n, j.val < k → z j = prescribedCoordinate j.val}

/-- The closed polydisc of coordinate radius `r`. -/
def polydisc (n : ℕ) (r : ℝ) : Set (FinitePoint n) :=
  {z | ∀ j : Fin n, ‖z j‖ ≤ r}

/-- The new constrained point `(4, 8, ..., 4n)`. -/
def prescribedPoint (n : ℕ) : FinitePoint n :=
  fun j => prescribedCoordinate j.val

/-- Restrict a bounded sequence to its first `n` coordinates. -/
def restrictSequence (n : ℕ) (w : BoundedSequence) : FinitePoint n :=
  fun j => w.val j.val

/-- Forget the last coordinate when comparing successive finite stages. -/
def prefixProjection (n : ℕ) (z : FinitePoint (n + 1)) : FinitePoint n :=
  fun j => z j.castSucc

theorem prescribedPoint_mem_finiteFlag (n k : ℕ) :
    prescribedPoint n ∈ finiteFlag n k := by
  intro j _
  rfl

theorem finiteFlag_nonempty (n k : ℕ) : (finiteFlag n k).Nonempty :=
  ⟨prescribedPoint n, prescribedPoint_mem_finiteFlag n k⟩

theorem finiteFlag_antitone (n : ℕ) : Antitone (finiteFlag n) := by
  intro k l hkl z hz j hj
  exact hz j (hj.trans_le hkl)

@[simp] theorem finiteFlag_zero (n : ℕ) : finiteFlag n 0 = Set.univ := by
  ext z
  simp [finiteFlag]

theorem finiteFlag_self (n : ℕ) : finiteFlag n n = {prescribedPoint n} := by
  ext z
  constructor
  · intro hz
    apply Set.mem_singleton_iff.mpr
    funext j
    exact hz j j.isLt
  · rintro rfl
    exact prescribedPoint_mem_finiteFlag n n

theorem restrictSequence_mem_finiteFlag {n k : ℕ} {w : BoundedSequence}
    (hw : w ∈ tailSet k) : restrictSequence n w ∈ finiteFlag n k := by
  intro j hj
  exact hw j.val hj

@[simp] theorem prefixProjection_restrictSequence (n : ℕ) (w : BoundedSequence) :
    prefixProjection n (restrictSequence (n + 1) w) = restrictSequence n w := rfl

/-- The constrained point is outside the approximation polydisc. This is the
separation used to choose a bump function in the manuscript. -/
theorem prescribedPoint_not_mem_polydisc {n : ℕ} (hn : 0 < n) :
    prescribedPoint n ∉ polydisc n (2 * (n : ℝ)) := by
  intro hmem
  let j : Fin n := ⟨n - 1, Nat.sub_lt hn (by decide)⟩
  have hj : j.val + 1 = n := by
    dsimp [j]
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
  have hbound := hmem j
  change ‖prescribedCoordinate j.val‖ ≤ 2 * (n : ℝ) at hbound
  rw [norm_prescribedCoordinate] at hbound
  have hjR : (j.val : ℝ) + 1 = n := by exact_mod_cast hj
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [hjR] at hbound
  linarith

/-- A restricted holomorphic approximation claim sufficient for the construction:
only the coordinate flags of this project, integer lower bounds, and a closed
polydisc are used. The open set `U` is an actual neighbourhood of that polydisc;
`DifferentiableOn ℂ h U` expresses holomorphicity there. Approximation uses the
same tolerance at every point of the polydisc.

This is a proposition definition, not a proved result or an axiom. It is a
specialisation of the paper's general flag approximation lemma, and does not
attempt to define a general Oka manifold or invoke an informal external theorem. -/
def FiniteFlagApproximationStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (R : ℝ), 0 ≤ R →
    ∀ h : FinitePoint n → ℂ × ℂ,
      Continuous h →
      (∃ U : Set (FinitePoint n), IsOpen U ∧ polydisc n R ⊆ U ∧
        DifferentiableOn ℂ h U) →
      (∀ k : ℕ, 1 ≤ k → k ≤ n →
        ∀ z ∈ finiteFlag n k, (k : ℝ) < euclideanPairNorm (h z)) →
      ∀ ε : ℝ, 0 < ε →
        ∃ H : FinitePoint n → ℂ × ℂ,
          Differentiable ℂ H ∧
          (∀ z ∈ polydisc n R, euclideanPairNorm (H z - h z) < ε) ∧
          (∀ k : ℕ, 1 ≤ k → k ≤ n →
            ∀ z ∈ finiteFlag n k, (k : ℝ) < euclideanPairNorm (H z))

/-- The exact unresolved finite-stage construction. Entire means everywhere
complex Fréchet differentiable. The error is the reciprocal of `2^(3*(n+1))`,
i.e. precisely the paper's `2^(-3N)` at stage `N = n + 1`.

This definition asserts no existence theorem. Obtaining a term of this proposition
requires the approximation construction, including the unformalised Oka input. -/
def FiniteStageConstructionStatement : Prop :=
  ∃ F : (n : ℕ) → FinitePoint n → ℂ × ℂ,
    (∀ n : ℕ, 1 ≤ n → Differentiable ℂ (F n)) ∧
    (∀ z : FinitePoint 1, F 1 z = (2, 0)) ∧
    (∀ (n k : ℕ), 1 ≤ k → k ≤ n →
      ∀ z ∈ finiteFlag n k, (k : ℝ) < euclideanPairNorm (F n z)) ∧
    (∀ n : ℕ, 1 ≤ n →
      ∀ z ∈ polydisc (n + 1) (2 * ((n + 1 : ℕ) : ℝ)),
        euclideanPairNorm (F (n + 1) z - F n (prefixProjection n z)) <
          ((2 : ℝ) ^ (3 * (n + 1)))⁻¹)

theorem continuous_euclideanPairNorm : Continuous euclideanPairNorm := by
  exact ((continuous_fst.norm.pow 2).add (continuous_snd.norm.pow 2)).sqrt

/-- A convergent sequence of pairs preserves an eventual non-strict lower bound
on its Euclidean norm. The assertion does not assume norm convergence in the
coefficient algebra. -/
theorem euclideanPairNorm_ge_of_tendsto {u : ℕ → ℂ × ℂ} {v : ℂ × ℂ} {r : ℝ}
    (hu : Tendsto u atTop (𝓝 v))
    (hbound : ∀ᶠ n in atTop, r ≤ euclideanPairNorm (u n)) :
    r ≤ euclideanPairNorm v := by
  exact ge_of_tendsto (continuous_euclideanPairNorm.continuousAt.tendsto.comp hu) hbound

/-- Elementary passage to the limit in the escape estimate. Both pointwise
convergence and the eventual finite-stage bound are explicit hypotheses. -/
theorem isEscapeMap_of_tendsto
    {F : BoundedSequence → ℂ × ℂ} {Fseq : ℕ → BoundedSequence → ℂ × ℂ}
    (hlim : ∀ w, Tendsto (fun n => Fseq n w) atTop (𝓝 (F w)))
    (hbound : ∀ (k : ℕ) (w : BoundedSequence), w ∈ tailSet k →
      ∀ᶠ n in atTop, (k : ℝ) < euclideanPairNorm (Fseq n w)) :
    IsEscapeMap F := by
  intro k w hw
  apply euclideanPairNorm_ge_of_tendsto (hlim w)
  filter_upwards [hbound k w hw] with n hn
  exact hn.le

/-- Specialisation to restrictions of finite-dimensional stage maps. This proves
the final lower-bound passage of Section 3.3 once pointwise convergence is known;
it does not establish that convergence or construct any of the maps. -/
theorem isEscapeMap_of_finiteStage_tendsto
    {F : BoundedSequence → ℂ × ℂ}
    {Fstage : (n : ℕ) → FinitePoint n → ℂ × ℂ}
    (hlim : ∀ w, Tendsto (fun n => Fstage n (restrictSequence n w)) atTop (𝓝 (F w)))
    (hbound : ∀ (n k : ℕ), 1 ≤ k → k ≤ n →
      ∀ z ∈ finiteFlag n k, (k : ℝ) < euclideanPairNorm (Fstage n z)) :
    IsEscapeMap F := by
  intro k w hw
  by_cases hk : k = 0
  · subst k
    simpa using euclideanPairNorm_nonneg (F w)
  · apply euclideanPairNorm_ge_of_tendsto (hlim w)
    filter_upwards [eventually_ge_atTop k] with n hkn
    exact (hbound n k (Nat.one_le_iff_ne_zero.mpr hk) hkn
      (restrictSequence n w) (restrictSequence_mem_finiteFlag hw)).le

end AutomaticContinuity
