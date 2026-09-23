import AutomaticContinuity.FlagLocalSprays

set_option autoImplicit false

/-!
# A fixed entire chart with a uniform margin for a small flag bump

At an admissible point the source is restricted to exclude deeper flags.
For a positive active index, an actual normalized entire embedding avoids a
strictly larger ball. Its margin permits the same small additive perturbation
at every parameter, regardless of how large that parameter becomes. With no
active flags, translation gives the construction without a nonzero target
assumption. The inverse chart is chosen before the source window is shrunk.
-/

noncomputable section

namespace AutomaticContinuity.FlagBumpChart

open Set FlagTotalSpace

abbrev Pair := ℂ × ℂ

/-- An entire chart with a source window and a uniform additive tolerance.
The forward chart is defined on all of `C²`; only its inverse is local. -/
structure Data (n : ℕ) (h : FinitePoint n → Pair) where
  window : Set (FinitePoint n)
  isOpen_window : IsOpen window
  chart : OpenPartialHomeomorph Pair Pair
  differentiable_chart : Differentiable ℂ chart
  injective_chart : Function.Injective chart
  zero_mem_source : (0 : Pair) ∈ chart.source
  normalized : HasFDerivAt chart (ContinuousLinearMap.id ℂ Pair) 0
  differentiable_inverse : DifferentiableOn ℂ chart.symm chart.target
  section_mem_target : ∀ z ∈ window, h z ∈ chart.target
  margin : ℝ
  margin_pos : 0 < margin
  admissible_add : ∀ z ∈ window, ∀ t e : Pair,
    euclideanPairNorm e ≤ margin → (z, chart t + e) ∈ totalSet n

/-- The larger-ball estimate is stable under a closed, uniformly bounded
additive correction. Both norms are the actual Euclidean pair norm. -/
theorem norm_add_gt_of_margin {y e : Pair} {r R : ℝ}
    (hy : R < euclideanPairNorm y) (he : euclideanPairNorm e ≤ R - r) :
    r < euclideanPairNorm (y + e) := by
  have ht := euclideanPairNorm_add_le (y + e) (-e)
  rw [add_neg_cancel_right, LocalEntireSpray.euclideanPairNorm_neg] at ht
  linarith

/-- A normalized entire embedding and an additive tolerance are constructed
from the actual flag constraints, including the unconstrained stratum. -/
theorem exists_window_embedding {n : ℕ} (z : FinitePoint n) (v : Pair)
    (hadm : (z, v) ∈ totalSet n) :
    ∃ (W : Set (FinitePoint n)) (f : Pair → Pair) (δ : ℝ),
      IsOpen W ∧ z ∈ W ∧ Differentiable ℂ f ∧ Function.Injective f ∧
      f 0 = v ∧ HasFDerivAt f (ContinuousLinearMap.id ℂ Pair) 0 ∧ 0 < δ ∧
      ∀ p ∈ W, ∀ t e : Pair,
        euclideanPairNorm e ≤ δ → (p, f t + e) ∈ totalSet n := by
  obtain ⟨k, hkn, hzk, W, hW, hzW, hWk⟩ :=
    FlagLocalSprays.exists_source_neighborhood n z
  by_cases hk : k = 0
  · refine ⟨W, (fun t => v + t), 1, hW, hzW, ?_, ?_, by simp, ?_, by norm_num, ?_⟩
    · fun_prop
    · intro t u heq
      exact add_left_cancel heq
    · exact (hasFDerivAt_id (0 : Pair)).const_add v
    · intro p hp t e _he
      apply mem_totalSet_iff.mpr
      intro j hj hjn hpj
      have := hWk p hp j hjn hpj
      omega
  · have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
    have hkv : (k : ℝ) < euclideanPairNorm v :=
      (mem_totalSet_iff.mp hadm) k (by omega) hkn hzk
    let R : ℝ := ((k : ℝ) + euclideanPairNorm v) / 2
    have hkR : (k : ℝ) < R := by dsimp [R]; linarith
    have hRv : R < euclideanPairNorm v := by dsimp [R]; linarith
    obtain ⟨f, hf, hinj, hf0, hfd, hfr⟩ :=
      BallComplementEmbeddings.exists_normalized_entire_embedding (hkpos.trans hkR) v hRv
    refine ⟨W, f, R - k, hW, hzW, hf, hinj, hf0, hfd, sub_pos.mpr hkR, ?_⟩
    intro p hp t e he
    apply mem_totalSet_iff.mpr
    intro j _hj hjn hpj
    exact (Nat.cast_le.mpr (hWk p hp j hjn hpj)).trans_lt
      (norm_add_gt_of_margin (hfr t) he)

/-- The actual local inverse chart is fixed first. Continuity of the current
section then supplies an open source window whose image is inside that chart. -/
theorem exists_data {n : ℕ} (h : FinitePoint n → Pair) (hh : Continuous h)
    (z : FinitePoint n) (hadm : (z, h z) ∈ totalSet n) :
    ∃ D : Data n h, z ∈ D.window ∧ D.chart 0 = h z := by
  obtain ⟨W, f, δ, hW, hzW, hf, hinj, hf0, hfd, hδ, hadmW⟩ :=
    exists_window_embedding z (h z) hadm
  obtain ⟨e, he, he0, het, heinv⟩ := LocalEntireSpray.exists_biholomorphic_chart
    f hf (ContinuousLinearEquiv.refl ℂ Pair)
    (by simpa only [ContinuousLinearEquiv.coe_refl] using hfd)
  let D : Data n h :=
    { window := W ∩ h ⁻¹' e.target
      isOpen_window := hW.inter (e.open_target.preimage hh)
      chart := e
      differentiable_chart := he.symm ▸ hf
      injective_chart := he.symm ▸ hinj
      zero_mem_source := he0
      normalized := he.symm ▸ hfd
      differentiable_inverse := heinv
      section_mem_target := fun _ hp => hp.2
      margin := δ
      margin_pos := hδ
      admissible_add := by
        intro p hp t a ha
        rw [he]
        exact hadmW p hp.1 t a ha }
  refine ⟨D, ⟨hzW, ?_⟩, ?_⟩
  · change h z ∈ e.target
    simpa only [hf0] using het
  · change e 0 = h z
    rw [he, hf0]

namespace Data

variable {n : ℕ} {h : FinitePoint n → Pair} (D : Data n h)

/-- Inverse coordinates of the existing section. -/
def coordinates (z : FinitePoint n) : Pair := D.chart.symm (h z)

theorem chart_coordinates {z : FinitePoint n} (hz : z ∈ D.window) :
    D.chart (D.coordinates z) = h z :=
  D.chart.right_inv (D.section_mem_target z hz)

theorem continuousOn_coordinates (hh : ContinuousOn h D.window) :
    ContinuousOn D.coordinates D.window :=
  D.chart.continuousOn_symm.comp hh D.section_mem_target

theorem differentiableOn_coordinates {V : Set (FinitePoint n)}
    (hh : DifferentiableOn ℂ h V) (hV : V ⊆ D.window) :
    DifferentiableOn ℂ D.coordinates V :=
  D.differentiable_inverse.comp hh (fun z hz => D.section_mem_target z (hV hz))

theorem admissible {z : FinitePoint n} (hz : z ∈ D.window) (t : Pair) :
    (z, D.chart t) ∈ totalSet n := by
  simpa only [add_zero] using D.admissible_add z hz t 0
    (by simpa only [euclideanPairNorm_zero] using D.margin_pos.le)

end Data

end AutomaticContinuity.FlagBumpChart
