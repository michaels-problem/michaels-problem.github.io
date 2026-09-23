import AutomaticContinuity.FlagBumpChart
import AutomaticContinuity.AdaptiveInverseControl

set_option autoImplicit false

/-!
# An admissible bump homotopy in the actual entire chart

The chart and its fixed perturbation margin have already been constructed.
Any holomorphic parameter map gives a holomorphic endpoint, even when its
values are arbitrarily large away from the overlap. Compactness supplies one
overlap approximation tolerance before that parameter map is chosen.
-/

noncomputable section

namespace AutomaticContinuity.FlagBumpChart.Data

open Set FlagTotalSpace

variable {n : ℕ} {h : FinitePoint n → Pair} (D : Data n h)

def parameterHomotopy (p : FinitePoint n → Pair) (tz : ℝ × FinitePoint n) : Pair :=
  (1 - tz.1) • D.coordinates tz.2 + tz.1 • p tz.2

def homotopy (p : FinitePoint n → Pair) (tz : ℝ × FinitePoint n) : Pair :=
  D.chart (D.parameterHomotopy p tz)

def correctedHomotopy (p b : FinitePoint n → Pair) (tz : ℝ × FinitePoint n) : Pair :=
  D.homotopy p tz + tz.1 • b tz.2

@[simp] theorem parameterHomotopy_zero (p : FinitePoint n → Pair) (z : FinitePoint n) :
    D.parameterHomotopy p (0, z) = D.coordinates z := by simp [parameterHomotopy]

@[simp] theorem parameterHomotopy_one (p : FinitePoint n → Pair) (z : FinitePoint n) :
    D.parameterHomotopy p (1, z) = p z := by simp [parameterHomotopy]

theorem homotopy_zero (p : FinitePoint n → Pair) {z : FinitePoint n}
    (hz : z ∈ D.window) : D.homotopy p (0, z) = h z := by
  rw [homotopy, parameterHomotopy_zero, D.chart_coordinates hz]

@[simp] theorem homotopy_one (p : FinitePoint n → Pair) (z : FinitePoint n) :
    D.homotopy p (1, z) = D.chart (p z) := by
  rw [homotopy, parameterHomotopy_one]

theorem correctedHomotopy_zero (p b : FinitePoint n → Pair) {z : FinitePoint n}
    (hz : z ∈ D.window) : D.correctedHomotopy p b (0, z) = h z := by
  simp only [correctedHomotopy, zero_smul, add_zero, D.homotopy_zero p hz]

@[simp] theorem correctedHomotopy_one (p b : FinitePoint n → Pair) (z : FinitePoint n) :
    D.correctedHomotopy p b (1, z) = D.chart (p z) + b z := by
  simp only [correctedHomotopy, homotopy_one, one_smul]

theorem continuousOn_parameterHomotopy {p : FinitePoint n → Pair}
    (hh : ContinuousOn h D.window) (hp : ContinuousOn p D.window) :
    ContinuousOn (D.parameterHomotopy p) (Icc 0 1 ×ˢ D.window) := by
  have hu : ContinuousOn (fun tz : ℝ × FinitePoint n => D.coordinates tz.2)
      (Icc 0 1 ×ˢ D.window) := (D.continuousOn_coordinates hh).comp continuousOn_snd
    (fun _ hz => hz.2)
  have hp' : ContinuousOn (fun tz : ℝ × FinitePoint n => p tz.2)
      (Icc 0 1 ×ˢ D.window) := hp.comp continuousOn_snd (fun _ hz => hz.2)
  exact (continuousOn_const.sub continuousOn_fst).smul hu |>.add
    (continuousOn_fst.smul hp')

theorem continuousOn_homotopy {p : FinitePoint n → Pair}
    (hh : ContinuousOn h D.window) (hp : ContinuousOn p D.window) :
    ContinuousOn (D.homotopy p) (Icc 0 1 ×ˢ D.window) :=
  D.differentiable_chart.continuous.comp_continuousOn
    (D.continuousOn_parameterHomotopy hh hp)

theorem continuousOn_correctedHomotopy {p b : FinitePoint n → Pair}
    (hh : ContinuousOn h D.window) (hp : ContinuousOn p D.window)
    (hb : ContinuousOn b D.window) :
    ContinuousOn (D.correctedHomotopy p b) (Icc 0 1 ×ˢ D.window) :=
  (D.continuousOn_homotopy hh hp).add
    (continuousOn_fst.smul (hb.comp continuousOn_snd (fun _ hz => hz.2)))

theorem differentiableOn_endpoint {V : Set (FinitePoint n)}
    {p b : FinitePoint n → Pair} (hp : DifferentiableOn ℂ p V)
    (hb : DifferentiableOn ℂ b V) :
    DifferentiableOn ℂ (fun z => D.chart (p z) + b z) V :=
  (D.differentiable_chart.comp_differentiableOn hp).add hb

theorem admissible_homotopy (p : FinitePoint n → Pair) {t : ℝ}
    {z : FinitePoint n} (hz : z ∈ D.window) :
    (z, D.homotopy p (t, z)) ∈ totalSet n :=
  D.admissible hz (D.parameterHomotopy p (t, z))

theorem admissible_correctedHomotopy (p b : FinitePoint n → Pair) {t : ℝ}
    (ht : t ∈ Icc 0 1) {z : FinitePoint n} (hz : z ∈ D.window)
    (hb : euclideanPairNorm (b z) ≤ D.margin) :
    (z, D.correctedHomotopy p b (t, z)) ∈ totalSet n := by
  apply D.admissible_add z hz (D.parameterHomotopy p (t, z)) (t • b z)
  rw [euclideanPairNorm_real_smul ht.1]
  exact (mul_le_mul_of_nonneg_right ht.2 (euclideanPairNorm_nonneg (b z))).trans
    (by simpa only [one_mul] using hb)

theorem parameterHomotopy_sub_coordinates (p : FinitePoint n → Pair)
    (t : ℝ) (z : FinitePoint n) :
    D.parameterHomotopy p (t, z) - D.coordinates z = t • (p z - D.coordinates z) := by
  simp only [parameterHomotopy, sub_smul, one_smul, smul_sub]
  abel

theorem norm_parameterHomotopy_sub_le (p : FinitePoint n → Pair)
    {t : ℝ} (ht : t ∈ Icc 0 1) (z : FinitePoint n) :
    euclideanPairNorm (D.parameterHomotopy p (t, z) - D.coordinates z) ≤
      euclideanPairNorm (p z - D.coordinates z) := by
  rw [D.parameterHomotopy_sub_coordinates, euclideanPairNorm_real_smul ht.1]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2
    (euclideanPairNorm_nonneg (p z - D.coordinates z))

/-- A single positive tolerance controls every intermediate time on the compact
overlap. It is chosen independently of the approximating parameter map. -/
theorem exists_overlap_tolerance {C : Set (FinitePoint n)} (hC : IsCompact C)
    (hCW : C ⊆ D.window) (hh : ContinuousOn h D.window) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : FinitePoint n → Pair,
      (∀ z ∈ C, euclideanPairNorm (p z - D.coordinates z) ≤ δ) →
      ∀ t ∈ Icc 0 1, ∀ z ∈ C, euclideanPairNorm (D.homotopy p (t, z) - h z) < ε := by
  have hK : IsCompact (D.coordinates '' C) :=
    hC.image_of_continuousOn ((D.continuousOn_coordinates hh).mono hCW)
  obtain ⟨δ, hδ, hcontrol⟩ := AdaptiveInverseControl.exists_control_on_compact
    (D.chart : Pair → Pair) hK isOpen_univ (subset_univ _)
    D.differentiable_chart.continuous.continuousOn (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro p hp t ht z hz
  have hd : dist (D.parameterHomotopy p (t, z)) (D.coordinates z) ≤ δ := by
    rw [dist_eq_norm]
    exact (norm_le_euclideanPairNorm _).trans
      ((D.norm_parameterHomotopy_sub_le p ht z).trans (hp z hz))
  have hout := (hcontrol (D.coordinates z) ⟨z, hz, rfl⟩ _ hd).2
  rw [dist_eq_norm, D.chart_coordinates (hCW hz)] at hout
  exact (euclideanPairNorm_le_two_mul_norm _).trans_lt (by
    change 2 * ‖D.chart (D.parameterHomotopy p (t, z)) - h z‖ < ε
    linarith)

end AutomaticContinuity.FlagBumpChart.Data
