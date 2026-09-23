import AutomaticContinuity.CompactCutoffTubes
import AutomaticContinuity.RadialCutoffField

set_option autoImplicit false

/-!
# One fixed tube around the entire radial isotopy

An initial scalar cutoff on a protectedSet cylinder and a compact obstacle gives
a cutoff on the stationary cylinder and the whole moving obstacle. The tube
radius is chosen once, uniformly over real time in `[0,1]`, before cubic
amplification. All fibre norms in these assumptions are genuinely Euclidean.
-/

noncomputable section

namespace AutomaticContinuity.RadialCutoffTubes

open Set Metric FlagTotalSpace

abbrev UnitTime := Icc (0 : ℝ) 1

def scale (c : ℝ) (t : UnitTime) : ℝ := 1 + (t : ℝ) * c

theorem one_le_scale {c : ℝ} (hc : 0 ≤ c) (t : UnitTime) : 1 ≤ scale c t :=
  le_add_of_nonneg_right (mul_nonneg t.property.1 hc)

theorem scale_pos {c : ℝ} (hc : 0 ≤ c) (t : UnitTime) : 0 < scale c t :=
  zero_lt_one.trans_le (one_le_scale hc t)

theorem continuous_scale (c : ℝ) : Continuous (scale c) := by unfold scale; fun_prop

variable {P : Type*}

def move (c : ℝ) (z : UnitTime × (P × (ℂ × ℂ))) : UnitTime × (P × (ℂ × ℂ)) :=
  (z.1, z.2.1, scale c z.1 • z.2.2)

def unscale (c : ℝ) (z : UnitTime × (P × (ℂ × ℂ))) : P × (ℂ × ℂ) :=
  (z.2.1, (scale c z.1)⁻¹ • z.2.2)

def pulledCutoff (q : P × (ℂ × ℂ) → ℂ) (c : ℝ)
    (z : UnitTime × (P × (ℂ × ℂ))) : ℂ := q (unscale c z)

def protectedSet (L : Set P) (a : ℝ) : Set (UnitTime × (P × (ℂ × ℂ))) :=
  univ ×ˢ (L ×ˢ closedEuclideanBall a)

def moving (K : Set (P × (ℂ × ℂ))) (c : ℝ) : Set (UnitTime × (P × (ℂ × ℂ))) :=
  move c '' (univ ×ˢ K)

theorem unscale_move {c : ℝ} (hc : 0 ≤ c) (z : UnitTime × (P × (ℂ × ℂ))) :
    unscale c (move c z) = z.2 := by
  simp [unscale, move, smul_smul, inv_mul_cancel₀ (scale_pos hc z.1).ne']

section Topology

variable [PseudoMetricSpace P]

theorem continuous_move (c : ℝ) : Continuous (move (P := P) c) := by
  unfold move
  exact continuous_fst.prodMk (continuous_snd.fst.prodMk
    (((continuous_scale c).comp continuous_fst).smul continuous_snd.snd))

theorem continuous_unscale {c : ℝ} (hc : 0 ≤ c) : Continuous (unscale (P := P) c) := by
  unfold unscale
  exact continuous_snd.fst.prodMk
    ((((continuous_scale c).comp continuous_fst).inv₀ (fun z => (scale_pos hc z.1).ne')).smul
      continuous_snd.snd)

theorem isCompact_protected {L : Set P} (hL : IsCompact L) (a : ℝ) :
    IsCompact (protectedSet L a) :=
  isCompact_univ.prod (hL.prod (isCompact_closedEuclideanBall a))

theorem isCompact_moving {K : Set (P × (ℂ × ℂ))} (hK : IsCompact K) (c : ℝ) :
    IsCompact (moving K c) := (isCompact_univ.prod hK).image (continuous_move c)

/-- Both full trajectory sets have one common positive closed tube on which
the scalar cutoff margins remain valid. The open base domain is retained. -/
theorem exists_uniform_tubes (q : P × (ℂ × ℂ) → ℂ)
    {L U : Set P} {K : Set (P × (ℂ × ℂ))} {a c : ℝ}
    (hL : IsCompact L) (hK : IsCompact K) (hU : IsOpen U) (hLU : L ⊆ U)
    (hKL : K ⊆ L ×ˢ univ) (hc : 0 ≤ c)
    (hq : ContinuousOn q (U ×ˢ univ))
    (hzero : ∀ z ∈ L ×ˢ closedEuclideanBall a, ‖q z‖ ≤ 1 / 16)
    (hone : ∀ z ∈ K, ‖q z - 1‖ ≤ 1 / 16) :
    ∃ ρ : ℝ, 0 < ρ ∧
      cthickening ρ (protectedSet L a) ⊆ univ ×ˢ (U ×ˢ univ) ∧
      cthickening ρ (moving K c) ⊆ univ ×ˢ (U ×ˢ univ) ∧
      (∀ z ∈ cthickening ρ (protectedSet L a), ‖pulledCutoff q c z‖ < 1 / 8) ∧
      (∀ z ∈ cthickening ρ (moving K c), ‖pulledCutoff q c z - 1‖ < 1 / 8) ∧
      Disjoint (cthickening ρ (protectedSet L a)) (cthickening ρ (moving K c)) := by
  apply CompactCutoffTubes.exists_two_tubes (pulledCutoff q c)
    (isCompact_protected hL a) (isCompact_moving hK c)
    (isOpen_univ.prod (hU.prod isOpen_univ))
  · intro z hz
    exact ⟨mem_univ _, hLU hz.2.1, mem_univ _⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨mem_univ _, hLU (hKL hz.2).1, mem_univ _⟩
  · exact hq.comp (continuous_unscale hc).continuousOn (fun z hz => ⟨hz.2.1, mem_univ _⟩)
  · intro z hz
    apply hzero
    refine ⟨hz.2.1, ?_⟩
    change euclideanPairNorm ((scale c z.1)⁻¹ • z.2.2) ≤ a
    rw [euclideanPairNorm_real_smul (inv_nonneg.mpr (scale_pos hc z.1).le)]
    have hi : (scale c z.1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_scale hc z.1)
    exact (mul_le_of_le_one_left (euclideanPairNorm_nonneg _) hi).trans hz.2.2
  · rintro _ ⟨z, hz, rfl⟩
    simpa only [pulledCutoff, unscale_move hc] using hone z.2 hz.2

end Topology

end AutomaticContinuity.RadialCutoffTubes
