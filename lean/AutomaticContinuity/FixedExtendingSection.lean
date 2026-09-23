import AutomaticContinuity.FlagApproximationOpenness
import AutomaticContinuity.FlagScalingBuffer

set_option autoImplicit false

/-! # A fixed extending section with margin and actual inverse coordinates

Approximability is used once to choose a whole-target section sufficiently
close to the original compact graph. All output domains and positive margins
are then fixed before the subsequent parameter polynomial is selected.
-/

noncomputable section

namespace AutomaticContinuity.FlagSectionApproximation

open Set FlagTotalSpace CompactFamilyInverseCoordinates

theorem exists_fixed_extending_section {n : ℕ}
    {K L B : Set (FinitePoint n)} (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ L)
    (h : FinitePoint n → Pair) (hh : ContinuousOn h K) (happrox : Approximable K L h)
    {Ω : Set (FinitePoint n × Pair)} (hΩ : IsOpen Ω) (hΩB : Ω ⊆ B ×ˢ univ)
    (hgraph : ∀ z ∈ K, (z, h z) ∈ Ω)
    (F G : FinitePoint n × Pair → Pair)
    (hF : DifferentiableOn ℂ F Ω) (hzero : ∀ z ∈ K, F (z, h z) = 0)
    (hGF : ∀ z ∈ Ω, G (z.1, F z) = z.2) :
    ∃ (g θ : FinitePoint n → Pair) (U V : Set (FinitePoint n)) (δ : ℝ),
      IsOpen U ∧ L ⊆ U ∧ DifferentiableOn ℂ g U ∧ 0 < δ ∧
      (∀ z ∈ U, ∀ e : Pair, euclideanPairNorm e ≤ δ → (z, g z + e) ∈ totalSet n) ∧
      IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ V ⊆ B ∧
      DifferentiableOn ℂ θ V ∧ (∀ z ∈ V, G (z, θ z) = g z) := by
  obtain ⟨d, hd, hcontrol⟩ := exists_uniform_inverse_tolerance hK h hh hΩ hgraph
    F hF.continuousOn hzero (by norm_num : (0 : ℝ) < 1)
  obtain ⟨g, Z, hZ, hLZ, hg, hadm, hclose⟩ := happrox d hd
  have hggraph : ∀ z ∈ K, (z, g z) ∈ Ω := fun z hz =>
    (hcontrol z hz (g z) (hclose z hz).le).1
  obtain ⟨l, U, hl, hU, hLU, hUZ, hscaled⟩ :=
    FlagScalingBuffer.exists_scaling_neighbourhood hL hZ hLZ g hg.continuousOn
      (fun z hz => hadm z (hLZ hz))
  have hgU : DifferentiableOn ℂ g U := hg.mono hUZ
  obtain ⟨V, hV, hKV, hVU, hVgraph, hθ⟩ := exists_coordinate_neighbourhood
    hU (hKL.trans hLU) hΩ F g hF hgU hggraph
  refine ⟨g, coordinates F g, U, V, l-1, hU, hLU, hgU, sub_pos.mpr hl,
    ?_, hV, hKV, hVU, ?_, hθ, ?_⟩
  · intro z hz e he
    have hm := FlagScalingBuffer.admissible_smul_add hl (hscaled z hz) he
    have hlne : l ≠ 0 := ne_of_gt (lt_trans zero_lt_one hl)
    simpa only [smul_smul, mul_inv_cancel₀ hlne, one_smul] using hm
  · intro z hz
    exact (hΩB (hVgraph z hz)).1
  · exact reconstructed F G g hGF hVgraph

end AutomaticContinuity.FlagSectionApproximation
