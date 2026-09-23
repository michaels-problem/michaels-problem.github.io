import AutomaticContinuity.RadialCutoffTubes
import AutomaticContinuity.RadialMeshApproximation
import AutomaticContinuity.FiniteFlowHolomorphy
import AutomaticContinuity.ParameterFibreComposition

set_option autoImplicit false

/-!
# A compact radial push from actual local flow realizations

The realization datum consists of actual fibre homeomorphisms and their local
first-order expansions. The final mesh product is constructed here. The cutoff
degree is chosen before the mesh, and stability uses the radial comparison
field rather than any degree-dependent Lipschitz constant.
-/

noncomputable section

namespace AutomaticContinuity.RadialCompactPush

open Set Metric RadialCutoffTubes RadialCutoffField EuclideanTrajectoryStability

abbrev Pair := ℂ × ℂ

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

def localizedField (q : P × Pair → ℂ) (c : ℝ) (m : ℕ)
    (s : UnitTime) (p : P) (w : Pair) : Pair :=
  field (fun z : P × Pair => q (z.1, (scale c s)⁻¹ • z.2))
    m (c / scale c s) p w

/-- Uniform first-order realizations on compact subsets of the open base
domain. Forward and inverse maps are actual mutually inverse homeomorphisms. -/
structure Realization (q : P × Pair → ℂ) (c : ℝ) (U : Set P) (m : ℕ) where
  map : UnitTime → ℂ → P → Pair ≃ₜ Pair
  fixes_zero : ∀ s t p, map s t p 0 = 0
  holomorphic : ∀ s t, DifferentiableOn ℂ
    (fun z : P × Pair => map s t z.1 z.2) (U ×ˢ univ)
  inverse_holomorphic : ∀ s t, DifferentiableOn ℂ
    (fun z : P × Pair => (map s t z.1).symm z.2) (U ×ˢ univ)
  uniform_step : ∀ (C : Set (UnitTime × (P × Pair))), IsCompact C →
    C ⊆ univ ×ˢ (U ×ˢ univ) → ∀ η : ℝ, 0 < η →
    ∃ τ : ℝ, 0 < τ ∧ ∀ z ∈ C, ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < τ →
      euclideanPairNorm
        (map z.1 t z.2.1 z.2.2 - z.2.2 - t • localizedField q c m z.1 z.2.1 z.2.2)
        < η * ‖t‖ ∧
      euclideanPairNorm
        ((map z.1 t z.2.1).symm z.2.2 - z.2.2 + t • localizedField q c m z.1 z.2.1 z.2.2)
        < η * ‖t‖

def meshTime (h : ℝ) (j : ℕ) : UnitTime :=
  ⟨min 1 (max 0 ((j : ℝ) * h)), le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

theorem meshTime_val {N j : ℕ} {h : ℝ} (hh : 0 ≤ h)
    (hmesh : (N : ℝ) * h = 1) (hj : j ≤ N) :
    (meshTime h j : ℝ) = (j : ℝ) * h := by
  have hlo : 0 ≤ (j : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh
  have hhi : (j : ℝ) * h ≤ 1 := by
    rw [← hmesh]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) hh
  simp [meshTime, max_eq_right hlo, min_eq_right hhi]

theorem rate_bounds {c : ℝ} (hc : 0 ≤ c) (s : UnitTime) :
    0 ≤ c / scale c s ∧ c / scale c s ≤ c := by
  refine ⟨div_nonneg hc (scale_pos hc s).le, ?_⟩
  exact div_le_self hc (one_le_scale hc s)

omit [NormedSpace ℂ P] in
theorem same_fibre_mem_tube {S : Set (UnitTime × (P × Pair))}
    {s : UnitTime} {p : P} {w z : Pair} {ρ : ℝ}
    (hw : (s, p, w) ∈ S) (hz : euclideanPairNorm (z - w) ≤ ρ) :
    (s, p, z) ∈ cthickening ρ S := by
  apply mem_cthickening_of_dist_le (s, p, z) (s, p, w) ρ S hw
  calc
    dist (s, p, z) (s, p, w) = dist z w := by simp [Prod.dist_eq]
    _ = ‖z - w‖ := dist_eq_norm _ _
    _ ≤ ρ := (norm_le_euclideanPairNorm (z - w)).trans hz

omit [NormedAddCommGroup P] [NormedSpace ℂ P] in
theorem localizedField_small (q : P × Pair → ℂ) (m : ℕ) {c B : ℝ}
    (hc : 0 ≤ c) (hB : 0 ≤ B) (s : UnitTime) (p : P) (w : Pair)
    (hq : ‖pulledCutoff q c (s, p, w)‖ ≤ 1 / 8)
    (hw : euclideanPairNorm w ≤ B) :
    euclideanPairNorm (localizedField q c m s p w) ≤ c * ((1 / 2 : ℝ) ^ m / 8) * B := by
  apply (field_small_on_protected _ m (rate_bounds hc s).1 p w hq hw).trans
  gcongr
  exact (rate_bounds hc s).2

omit [NormedAddCommGroup P] [NormedSpace ℂ P] in
theorem localizedField_radial (q : P × Pair → ℂ) (m : ℕ) {c B : ℝ}
    (hc : 0 ≤ c) (hB : 0 ≤ B) (s : UnitTime) (p : P) (w : Pair)
    (hq : ‖pulledCutoff q c (s, p, w) - 1‖ ≤ 1 / 8)
    (hw : euclideanPairNorm w ≤ B) :
    euclideanPairNorm (localizedField q c m s p w - (c / scale c s) • w) ≤
      c * ((1 / 2 : ℝ) ^ m / 8) * B := by
  apply (field_close_to_radial _ m (rate_bounds hc s).1 p w hq hw).trans
  gcongr
  exact (rate_bounds hc s).2

theorem compose_toEquiv (e : ℕ → Pair ≃ₜ Pair) (n : ℕ) :
    (FiniteFlowHolomorphy.compose e n).toEquiv =
      FiniteFlowLocal.compose (fun i => (e i).toEquiv) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (FiniteFlowHolomorphy.compose e n).toEquiv.trans (e n).toEquiv = _
    rw [ih]
    rfl

set_option maxHeartbeats 400000 in
/-- Quantitative compact push. Both protected estimates concern the actual
forward and inverse products; the moving compact is dilated by `1+c`.
Regularity of the resulting family is supplied by the companion theorem. -/
theorem exists_compact_push_data [ProperSpace P] (q : P × Pair → ℂ)
    {L U : Set P} {K : Set (P × Pair)} {a c ε : ℝ}
    (hL : IsCompact L) (hK : IsCompact K) (hU : IsOpen U) (hLU : L ⊆ U)
    (hKL : K ⊆ L ×ˢ univ) (hc : 0 ≤ c) (hε : 0 < ε)
    (hq : ContinuousOn q (U ×ˢ univ))
    (hzero : ∀ z ∈ L ×ˢ FlagTotalSpace.closedEuclideanBall a, ‖q z‖ ≤ 1 / 16)
    (hone : ∀ z ∈ K, ‖q z - 1‖ ≤ 1 / 16)
    (hreal : ∀ m, Nonempty (Realization q c U m)) :
    ∃ (m : ℕ) (R : Realization q c U m) (N : ℕ) (h : ℝ), 0 < N ∧ 0 < h ∧
      (let Φ := fun p => FiniteFlowHolomorphy.compose (fun j => R.map (meshTime h j) (h : ℂ) p) N
       (∀ z ∈ L ×ˢ FlagTotalSpace.closedEuclideanBall a,
         euclideanPairNorm (Φ z.1 z.2 - z.2) < ε ∧
         euclideanPairNorm ((Φ z.1).symm z.2 - z.2) < ε) ∧
       (∀ z ∈ K, euclideanPairNorm (Φ z.1 z.2 - (1 + c) • z.2) < ε)) := by
  obtain ⟨ρ, hρ, hC₀U, hC₁U, hC₀q, hC₁q, _⟩ :=
    exists_uniform_tubes q hL hK hU hLU hKL hc hq hzero hone
  let C₀ := cthickening ρ (protectedSet L a)
  let C₁ := cthickening ρ (moving K c)
  let C := C₀ ∪ C₁
  have hC : IsCompact C := (isCompact_protected hL a).cthickening.union
    (isCompact_moving hK c).cthickening
  have hCU : C ⊆ univ ×ˢ (U ×ˢ univ) := union_subset hC₀U hC₁U
  obtain ⟨B₀, hB₀⟩ := hC.exists_bound_of_continuousOn
    (continuous_snd.snd : Continuous (fun z : UnitTime × (P × Pair) => z.2.2)).continuousOn
  let B := 2 * max B₀ 0
  have hB : 0 ≤ B := by positivity
  have hbound : ∀ z ∈ C, euclideanPairNorm z.2.2 ≤ B := by
    intro z hz
    exact (euclideanPairNorm_le_two_mul_norm z.2.2).trans
      (mul_le_mul_of_nonneg_left ((hB₀ z hz).trans (le_max_left _ _)) (by norm_num))
  obtain ⟨d, hd, hdm⟩ := exists_pos_mul_lt (lt_min hε hρ) (2 * Real.exp c)
  have hexp : 1 ≤ Real.exp c := Real.one_le_exp_iff.mpr hc
  have hde : (d + d) * Real.exp c < ε := by
    calc
      (d + d) * Real.exp c = (2 * Real.exp c) * d := by ring
      _ < min ε ρ := hdm
      _ ≤ ε := min_le_left _ _
  have hdr : (d + d) * Real.exp c < ρ := by
    calc
      (d + d) * Real.exp c = (2 * Real.exp c) * d := by ring
      _ < min ε ρ := hdm
      _ ≤ ρ := min_le_right _ _
  have hdd : d + d ≤ (d + d) * Real.exp c := le_mul_of_one_le_right (by positivity) hexp
  obtain ⟨m, hm⟩ := exists_degree hc hB hd
  obtain ⟨R⟩ := hreal m
  have hsmall : ∀ z ∈ C₀, euclideanPairNorm (localizedField q c m z.1 z.2.1 z.2.2) ≤ d := by
    intro z hz
    exact (localizedField_small q m hc hB z.1 z.2.1 z.2.2
      (hC₀q z hz).le (hbound z (Or.inl hz))).trans hm.le
  have hradial : ∀ z ∈ C₁,
      euclideanPairNorm (localizedField q c m z.1 z.2.1 z.2.2 -
        (c / scale c z.1) • z.2.2) ≤ d := by
    intro z hz
    exact (localizedField_radial q m hc hB z.1 z.2.1 z.2.2
      (hC₁q z hz).le (hbound z (Or.inr hz))).trans hm.le
  obtain ⟨τ, hτ, hstep⟩ := R.uniform_step C hC hCU d hd
  obtain ⟨N, h, hN, hh, hhτ, hmesh⟩ := RadialMeshApproximation.exists_unit_mesh hτ
  have hnorm : ‖(h : ℂ)‖ = h := by simp [abs_of_pos hh]
  let e (p : P) (j : ℕ) : Pair ≃ₜ Pair := R.map (meshTime h j) (h : ℂ) p
  let V (p : P) (j : ℕ) (w : Pair) := localizedField q c m (meshTime h j) p w
  have hEuler : ∀ j p w, (meshTime h j, p, w) ∈ C →
      euclideanPairNorm (e p j w - w - h • V p j w) ≤ h * d ∧
      euclideanPairNorm ((e p j).symm w - w + h • V p j w) ≤ h * d := by
    intro j p w hw
    obtain ⟨hf, hi⟩ := hstep (meshTime h j, p, w) hw (h : ℂ)
      (by rwa [hnorm]) (by rwa [hnorm])
    rw [hnorm, mul_comm d h] at hf hi
    exact ⟨hf.le, hi.le⟩
  refine ⟨m, R, N, h, hN, hh, ?_⟩
  change (∀ z ∈ L ×ˢ FlagTotalSpace.closedEuclideanBall a,
    euclideanPairNorm (FiniteFlowHolomorphy.compose (e z.1) N z.2 - z.2) < ε ∧
    euclideanPairNorm ((FiniteFlowHolomorphy.compose (e z.1) N).symm z.2 - z.2) < ε) ∧ _
  constructor
  · intro z hz
    have hmem : ∀ j w, euclideanPairNorm (w - z.2) < ρ → (meshTime h j, z.1, w) ∈ C₀ := by
      intro j w hw
      exact same_fibre_mem_tube (show (meshTime h j, z.1, z.2) ∈ protectedSet L a from
        ⟨mem_univ _, hz⟩) hw.le
    have hEf : ∀ j < N, ∀ w, euclideanPairNorm (w - z.2) < ρ →
        euclideanPairNorm ((e z.1 j).toEquiv w - w - h • V z.1 j w) ≤ h * d :=
      fun j _ w hw => (hEuler j z.1 w (Or.inl (hmem j w hw))).1
    have hEi : ∀ j < N, ∀ w, euclideanPairNorm (w - z.2) < ρ →
        euclideanPairNorm ((e z.1 j).toEquiv.symm w - w + h • V z.1 j w) ≤ h * d :=
      fun j _ w hw => (hEuler j z.1 w (Or.inl (hmem j w hw))).2
    have hV : ∀ j < N, ∀ w, euclideanPairNorm (w - z.2) < ρ →
        euclideanPairNorm (V z.1 j w) ≤ d :=
      fun j _ w hw => hsmall (meshTime h j, z.1, w) (hmem j w hw)
    have hf := RadialMeshApproximation.protected_compose_error
      (fun j => (e z.1 j).toEquiv) (V z.1) N z.2 hh.le hd.le hd.le hmesh
      (hdd.trans_lt hdr) hEf hV
    have hi := RadialMeshApproximation.inverse_protected_compose_error
      (fun j => (e z.1 j).toEquiv) (V z.1) N z.2 hh.le hd.le hd.le hmesh
      (hdd.trans_lt hdr) hEi hV
    rw [← compose_toEquiv] at hf hi
    exact ⟨hf.trans_lt (hdd.trans_lt hde), hi.trans_lt (hdd.trans_lt hde)⟩
  · intro z hz
    have htime : ∀ j < N, (meshTime h j : ℝ) = (j : ℝ) * h :=
      fun j hj => meshTime_val hh.le hmesh hj.le
    have hscale : ∀ j < N, scale c (meshTime h j) = 1 + (j : ℝ) * h * c :=
      fun j hj => by simp only [scale, htime j hj]
    have hmem : ∀ j < N, ∀ w,
        euclideanPairNorm (w - radialPoint c h j z.2) < ρ →
        (meshTime h j, z.1, w) ∈ C₁ := by
      intro j hj w hw
      apply same_fibre_mem_tube (ρ := ρ) (w := radialPoint c h j z.2) _ hw.le
      refine ⟨(meshTime h j, z), ⟨mem_univ _, hz⟩, ?_⟩
      simp only [move, radialPoint, hscale j hj]
    have hEf : ∀ j < N, ∀ w, euclideanPairNorm (w - radialPoint c h j z.2) < ρ →
        euclideanPairNorm ((e z.1 j).toEquiv w - w - h • V z.1 j w) ≤ h * d :=
      fun j hj w hw => (hEuler j z.1 w (Or.inr (hmem j hj w hw))).1
    have hV : ∀ j < N, ∀ w, euclideanPairNorm (w - radialPoint c h j z.2) < ρ →
        euclideanPairNorm (V z.1 j w - radialField c h j w) ≤ d := by
      intro j hj w hw
      have hh' := hradial (meshTime h j, z.1, w) (hmem j hj w hw)
      simpa only [hscale j hj, radialField] using hh'
    have hf := RadialMeshApproximation.radial_compose_error
      (fun j => (e z.1 j).toEquiv) (V z.1) N z.2 hc hh.le hd.le hd.le hmesh hdr hEf hV
    rw [← compose_toEquiv] at hf
    exact hf.trans_lt hde

/-- An actual parameter family of origin-fixing holomorphic fibre
automorphisms, approximating the identity in both directions on the protected
cylinder and the prescribed radial dilation on the moving compact. -/
theorem exists_compact_push [ProperSpace P] (q : P × Pair → ℂ)
    {L U : Set P} {K : Set (P × Pair)} {a c ε : ℝ}
    (hL : IsCompact L) (hK : IsCompact K) (hU : IsOpen U) (hLU : L ⊆ U)
    (hKL : K ⊆ L ×ˢ univ) (hc : 0 ≤ c) (hε : 0 < ε)
    (hq : ContinuousOn q (U ×ˢ univ))
    (hzero : ∀ z ∈ L ×ˢ FlagTotalSpace.closedEuclideanBall a, ‖q z‖ ≤ 1 / 16)
    (hone : ∀ z ∈ K, ‖q z - 1‖ ≤ 1 / 16)
    (hreal : ∀ m, Nonempty (Realization q c U m)) :
    ∃ Φ : P → Pair ≃ₜ Pair,
      (∀ p, Φ p 0 = 0) ∧
      DifferentiableOn ℂ (fun z : P × Pair => Φ z.1 z.2) (U ×ˢ univ) ∧
      DifferentiableOn ℂ (fun z : P × Pair => (Φ z.1).symm z.2) (U ×ˢ univ) ∧
      (∀ z ∈ L ×ˢ FlagTotalSpace.closedEuclideanBall a,
        euclideanPairNorm (Φ z.1 z.2 - z.2) < ε ∧
        euclideanPairNorm ((Φ z.1).symm z.2 - z.2) < ε) ∧
      (∀ z ∈ K, euclideanPairNorm (Φ z.1 z.2 - (1 + c) • z.2) < ε) := by
  obtain ⟨m, R, N, h, _, _, hprotected, hmoving⟩ :=
    exists_compact_push_data q hL hK hU hLU hKL hc hε hq hzero hone hreal
  let e := fun j p => R.map (meshTime h j) (h : ℂ) p
  refine ⟨ParameterFibreComposition.product e N, ?_, ?_, ?_, hprotected, hmoving⟩
  · intro p
    exact ParameterFibreComposition.product_origin e N p (fun j _ => R.fixes_zero _ _ p)
  · exact ParameterFibreComposition.differentiableOn_product e N U
      (fun j _ => R.holomorphic _ _)
  · exact ParameterFibreComposition.differentiableOn_product_symm e N U
      (fun j _ => R.inverse_holomorphic _ _)

end AutomaticContinuity.RadialCompactPush
