import AutomaticContinuity.FlagAffineContraction
import AutomaticContinuity.EuclideanExteriorPaths
import AutomaticContinuity.FlagApproximationOpenness

set_option autoImplicit false

/-! # A holomorphic admissible path from a section to a large constant

Contraction toward a point in the deepest flag met by the convex base
preserves every applicable flag constraint. It is followed by a constant
section path outside that flag's Euclidean ball. Every time slice remains
holomorphic on an actual neighbourhood of the original base.
-/

noncomputable section
namespace AutomaticContinuity.HolomorphicFlagContraction
open Set FlagTotalSpace FlagAffineContraction
open scoped unitInterval

abbrev Pair := ℂ × ℂ

def largeValue (n : ℕ) : Pair := (((n+1 : ℕ) : ℂ), 0)

theorem largeValue_norm (n : ℕ) : (n : ℝ) < euclideanPairNorm (largeValue n) := by
  have hh := norm_fst_le_euclideanPairNorm (largeValue n)
  have hnorm : ‖(largeValue n).1‖ = (n : ℝ) + 1 := by
    change ‖((n+1 : ℕ) : ℂ)‖ = _
    rw [Complex.norm_natCast, Nat.cast_add, Nat.cast_one]
  rw [hnorm] at hh
  linarith

theorem largeValue_admissible (n : ℕ) (z : FinitePoint n) :
    (z, largeValue n) ∈ totalSet n := by
  apply mem_totalSet_iff.mpr
  intro k _ hkn _
  exact (Nat.cast_le.mpr hkn).trans_lt (largeValue_norm n)

def contractionTime (t : ℝ) : ℝ := max (1-2*t) 0
def constantTime (t : ℝ) : ℝ := max (2*t-1) 0

theorem contractionTime_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    contractionTime t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_right _ _, max_le (by linarith [ht.1]) zero_le_one⟩

theorem constantTime_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    constantTime t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_right _ _, max_le (by linarith [ht.2]) zero_le_one⟩

def deformation {n : ℕ} (h : FinitePoint n → Pair) (c : FinitePoint n)
    {v : Pair} (p : Path (h c) v) (q : ℝ × FinitePoint n) : Pair :=
  h (contraction c (contractionTime q.1) q.2) + p.extend (constantTime q.1) - h c

@[simp] theorem deformation_zero {n : ℕ} (h : FinitePoint n → Pair) (c z : FinitePoint n)
    {v : Pair} (p : Path (h c) v) : deformation h c p (0,z) = h z := by
  norm_num [deformation, contractionTime, constantTime]

@[simp] theorem deformation_one {n : ℕ} (h : FinitePoint n → Pair) (c z : FinitePoint n)
    {v : Pair} (p : Path (h c) v) : deformation h c p (1,z) = v := by
  norm_num [deformation, contractionTime, constantTime]

theorem deformation_of_le_half {n : ℕ} (h : FinitePoint n → Pair) (c z : FinitePoint n)
    {v : Pair} (p : Path (h c) v) {t : ℝ} (ht : t ≤ 1/2) :
    deformation h c p (t,z) = h (contraction c (contractionTime t) z) := by
  have hc : constantTime t = 0 := max_eq_right (by linarith)
  simp [deformation, hc]

theorem deformation_of_half_le {n : ℕ} (h : FinitePoint n → Pair) (c z : FinitePoint n)
    {v : Pair} (p : Path (h c) v) {t : ℝ} (ht : 1/2 ≤ t) :
    deformation h c p (t,z) = p.extend (constantTime t) := by
  have hc : contractionTime t = 0 := max_eq_right (by linarith)
  simp [deformation, hc]

set_option backward.isDefEq.respectTransparency false in
theorem continuousOn_deformation {n : ℕ} {K : Set (FinitePoint n)}
    (hK : Convex ℝ K) {c : FinitePoint n} (hcK : c ∈ K)
    (h : FinitePoint n → Pair) (hh : ContinuousOn h K)
    {v : Pair} (p : Path (h c) v) :
    ContinuousOn (deformation h c p) (Icc 0 1 ×ˢ K) := by
  have harg : Continuous (fun q : ℝ × FinitePoint n => (contractionTime q.1, q.2)) := by
    unfold contractionTime
    fun_prop
  have hct : Continuous (fun q : ℝ × FinitePoint n =>
      contraction c (contractionTime q.1) q.2) := (continuous_contraction c).comp harg
  have hfirst : ContinuousOn (fun q : ℝ × FinitePoint n =>
      h (contraction c (contractionTime q.1) q.2)) (Icc 0 1 ×ˢ K) :=
    hh.comp hct.continuousOn
      (fun q hq => contraction_mem hK hcK hq.2 (contractionTime_mem hq.1))
  have hsecond : Continuous (fun q : ℝ × FinitePoint n => p.extend (constantTime q.1)) := by
    exact p.continuous_extend.comp (by unfold constantTime; fun_prop)
  exact (hfirst.add hsecond.continuousOn).sub continuousOn_const

theorem holomorphicNear_deformation {n : ℕ} {K U : Set (FinitePoint n)}
    (hK : Convex ℝ K) {c : FinitePoint n} (hcK : c ∈ K)
    (hU : IsOpen U) (hKU : K ⊆ U) (h : FinitePoint n → Pair)
    (hh : DifferentiableOn ℂ h U) {v : Pair} (p : Path (h c) v)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    FlagSectionApproximation.HolomorphicNear K (fun z => deformation h c p (t,z)) := by
  obtain ⟨V,hV,hKV,hhol⟩ := holomorphic_section_contraction hK hcK hU hKU hh
    (contractionTime_mem ht)
  refine ⟨V,hV,hKV,?_⟩
  simpa only [deformation] using (hhol.add_const (p.extend (constantTime t))).sub_const (h c)

/-- The whole path is actual and admissible on the original convex set.
Its endpoint is a globally admissible constant, independent of the input.
Holomorphic neighbourhoods may depend on the path time. -/
theorem exists_holomorphic_admissible_path {n : ℕ} {K U : Set (FinitePoint n)}
    (hK : Convex ℝ K) (hKne : K.Nonempty) (hU : IsOpen U) (hKU : K ⊆ U)
    (h : FinitePoint n → Pair) (hh : DifferentiableOn ℂ h U)
    (hadm : ∀ z ∈ K, (z,h z) ∈ totalSet n) :
    ∃ H : ℝ × FinitePoint n → Pair,
      ContinuousOn H (Icc 0 1 ×ˢ K) ∧
      (∀ z, H (0,z) = h z) ∧ (∀ z, H (1,z) = largeValue n) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        FlagSectionApproximation.HolomorphicNear K (fun z => H (t,z))) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ K, (z,H (t,z)) ∈ totalSet n) := by
  obtain ⟨j,hjn,c,hcK,hcj,hmax⟩ := exists_deepest_center hKne
  have hpath : ∃ p : Path (h c) (largeValue n),
      ∀ t : unitInterval, ∀ z ∈ K, (z,p t) ∈ totalSet n := by
    by_cases hj : j = 0
    · refine ⟨Path.segment (h c) (largeValue n), ?_⟩
      intro t z hz
      apply mem_totalSet_iff.mpr
      intro k hk hkn hzk
      have := hmax k hkn ⟨z,hz,hzk⟩
      omega
    · have hhc := mem_totalSet_iff.mp (hadm c hcK) j (Nat.one_le_iff_ne_zero.mpr hj) hjn hcj
      have hlarge : (j : ℝ) < euclideanPairNorm (largeValue n) :=
        (Nat.cast_le.mpr hjn).trans_lt (largeValue_norm n)
      have pp := EuclideanExteriorPaths.joinedIn_exterior (Nat.cast_nonneg j) hhc hlarge
      refine ⟨pp.somePath, ?_⟩
      intro t z hz
      apply mem_totalSet_iff.mpr
      intro k hk hkn hzk
      exact (Nat.cast_le.mpr (hmax k hkn ⟨z,hz,hzk⟩)).trans_lt (pp.somePath_mem t)
  obtain ⟨p,hp⟩ := hpath
  refine ⟨deformation h c p, continuousOn_deformation hK hcK h (hh.continuousOn.mono hKU) p,
    (fun z => deformation_zero h c z p), (fun z => deformation_one h c z p),
    fun t ht => holomorphicNear_deformation hK hcK hU hKU h hh p ht, ?_⟩
  intro t ht z hz
  by_cases hhalf : t ≤ 1/2
  · rw [deformation_of_le_half h c z p hhalf]
    exact contraction_admissible hK hcK hcj hmax hadm (contractionTime_mem ht) z hz
  · rw [deformation_of_half_le h c z p (le_of_not_ge hhalf), p.extend_apply (constantTime_mem ht)]
    exact hp _ z hz

end AutomaticContinuity.HolomorphicFlagContraction
