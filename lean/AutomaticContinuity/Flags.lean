import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/-!
# Tail sets and the elementary escape contradiction

This file records the elementary geometry used in Sections 3 and 4 of
`automatic_continuity_characters.tex`. Indices start at zero in Lean: coordinate
`j` represents the paper's coordinate `j + 1`. Consequently `tailSet k` fixes
exactly the first `k` coordinates to `4, 8, ..., 4 * k`.

The norm on pairs is explicitly the Euclidean norm. In particular it is not the
default maximum norm on Lean's product of normed spaces.

The final results are conditional elementary implications. They do not construct
an escape map in the coefficient algebra and do not prove Theorem A.
-/

namespace AutomaticContinuity

/-- The set underlying the space of bounded complex sequences. No topology or
normed-space identification is needed for the elementary results in this file. -/
abbrev BoundedSequence :=
  {w : ℕ → ℂ // ∃ C : ℝ, ∀ j : ℕ, ‖w j‖ ≤ C}

/-- The paper's values `a₁ = 4, a₂ = 8, ...`, using zero-based indices. -/
def prescribedCoordinate (j : ℕ) : ℂ := ((4 * (j + 1) : ℕ) : ℂ)

@[simp] theorem norm_prescribedCoordinate (j : ℕ) :
    ‖prescribedCoordinate j‖ = 4 * ((j : ℝ) + 1) := by
  rw [prescribedCoordinate, Complex.norm_natCast]
  push_cast
  rfl

/-- `S_k` in the manuscript; `tailSet 0` is the whole space. -/
def tailSet (k : ℕ) : Set BoundedSequence :=
  {w | ∀ j : ℕ, j < k → w.val j = prescribedCoordinate j}

@[simp] theorem tailSet_zero : tailSet 0 = Set.univ := by
  ext w
  simp [tailSet]

/-- Truncate the prescribed unbounded sequence after the first `k` coordinates. -/
def truncatedPrescribed (k : ℕ) : BoundedSequence :=
  ⟨fun j => if j < k then prescribedCoordinate j else 0,
    ⟨4 * (k : ℝ), by
      intro j
      dsimp only
      split_ifs with hj
      · rw [norm_prescribedCoordinate]
        have hjk : (j : ℝ) + 1 ≤ (k : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt hj
        linarith
      · simp⟩⟩

theorem truncatedPrescribed_mem (k : ℕ) : truncatedPrescribed k ∈ tailSet k := by
  intro j hj
  simp [truncatedPrescribed, hj]

theorem tailSet_nonempty (k : ℕ) : (tailSet k).Nonempty :=
  ⟨truncatedPrescribed k, truncatedPrescribed_mem k⟩

/-- Fixing more coordinates makes the tail set smaller. -/
theorem tailSet_antitone : Antitone tailSet := by
  intro k l hkl w hw j hj
  exact hw j (hj.trans_le hkl)

theorem tailSet_succ_subset (k : ℕ) : tailSet (k + 1) ⊆ tailSet k :=
  tailSet_antitone (Nat.le_succ k)

/-- No bounded sequence can have all prescribed coordinate values. -/
theorem not_all_prescribed (w : BoundedSequence) :
    ¬ ∀ j : ℕ, w.val j = prescribedCoordinate j := by
  intro hw
  obtain ⟨C, hC⟩ := w.property
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hbound := hC n
  rw [hw n, norm_prescribedCoordinate] at hbound
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem iInter_tailSet_eq_empty : (⋂ k : ℕ, tailSet k) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro w hw
  apply not_all_prescribed w
  intro j
  exact (Set.mem_iInter.mp hw (j + 1)) j (Nat.lt_succ_self j)

/-- The actual Euclidean norm on a complex pair, written explicitly to avoid
using the maximum norm provided by the default product normed-space instance. -/
noncomputable def euclideanPairNorm (v : ℂ × ℂ) : ℝ :=
  Real.sqrt (‖v.1‖ ^ 2 + ‖v.2‖ ^ 2)

theorem euclideanPairNorm_nonneg (v : ℂ × ℂ) : 0 ≤ euclideanPairNorm v :=
  Real.sqrt_nonneg _

theorem euclideanPairNorm_sq (v : ℂ × ℂ) :
    euclideanPairNorm v ^ 2 = ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2 := by
  exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem norm_fst_le_euclideanPairNorm (v : ℂ × ℂ) :
    ‖v.1‖ ≤ euclideanPairNorm v := by
  apply Real.le_sqrt_of_sq_le
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem norm_snd_le_euclideanPairNorm (v : ℂ × ℂ) :
    ‖v.2‖ ≤ euclideanPairNorm v := by
  apply Real.le_sqrt_of_sq_le
  exact le_add_of_nonneg_left (sq_nonneg _)

theorem euclideanPairNorm_le_sum (v : ℂ × ℂ) :
    euclideanPairNorm v ≤ ‖v.1‖ + ‖v.2‖ := by
  apply (Real.sqrt_le_left (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  nlinarith [norm_nonneg v.1, norm_nonneg v.2]

/-- The quantitative escape bound of Proposition 3.1. Existence of such a map
whose two components belong to the coefficient algebra is a separate obligation. -/
def IsEscapeMap (F : BoundedSequence → ℂ × ℂ) : Prop :=
  ∀ (k : ℕ) (w : BoundedSequence), w ∈ tailSet k →
    (k : ℝ) ≤ euclideanPairNorm (F w)

/-- The elementary final contradiction, conditional on the escape estimate. -/
theorem escape_no_common_value {F : BoundedSequence → ℂ × ℂ}
    (hF : IsEscapeMap F) (v : ℂ × ℂ) :
    ¬ ∀ k : ℕ, v ∈ F '' tailSet k := by
  intro hv
  obtain ⟨k, hk⟩ := exists_nat_gt (euclideanPairNorm v)
  obtain ⟨w, hw, hFw⟩ := hv k
  have hbound := hF k w hw
  rw [hFw] at hbound
  exact (not_le_of_gt hk) hbound

theorem escape_image_intersection_eq_empty {F : BoundedSequence → ℂ × ℂ}
    (hF : IsEscapeMap F) : (⋂ k : ℕ, F '' tailSet k) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro v hv
  exact escape_no_common_value hF v (Set.mem_iInter.mp hv)

/-- Finite interpolation and an escape estimate cannot hold for the same pair.
The interpolation assertion is an explicit hypothesis, not a formalisation of
Arens's finite joint-spectrum theorem. -/
theorem escape_incompatible_with_interpolation
    {F : BoundedSequence → ℂ × ℂ} (hF : IsEscapeMap F)
    (v : ℂ × ℂ)
    (hInterpolation : ∀ k : ℕ, ∃ w ∈ tailSet k, F w = v) : False := by
  apply escape_no_common_value hF v
  exact hInterpolation

end AutomaticContinuity
