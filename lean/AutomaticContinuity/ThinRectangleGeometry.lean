import AutomaticContinuity.RectangleSeparatedSplitting
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false

/-!
# Thin buffered rectangles around a convex planar slice

The rectangle width is chosen after the holomorphic buffer is fixed. Its
horizontal edges avoid the entire compact convex set, even when that set is
not a rectangle. This geometry does not assert a complex approximation theorem.
-/

noncomputable section

namespace AutomaticContinuity.ThinRectangleGeometry

open Set Metric Complex RectangleCauchy

def zeroSlice (C : Set ℂ) : Set ℂ := C ∩ {z | z.re = 0}

theorem isCompact_zeroSlice {C : Set ℂ} (hC : IsCompact C) : IsCompact (zeroSlice C) :=
  hC.inter_right (isClosed_eq continuous_re continuous_const)

theorem convex_zeroSlice {C : Set ℂ} (hC : Convex ℝ C) : Convex ℝ (zeroSlice C) := by
  exact hC.inter ((convex_singleton (0 : ℝ)).linear_preimage reLm)

/-- Compactness controls every nearby slice, not just points on the cutting line. -/
theorem exists_narrow_band {C W : Set ℂ} (hC : IsCompact C) (hW : IsOpen W)
    (hSW : zeroSlice C ⊆ W) :
    ∃ η : ℝ, 0 < η ∧ ∀ z ∈ C, |z.re| ≤ η → z ∈ W := by
  classical
  by_cases hne : (C \ W).Nonempty
  · obtain ⟨z, hz, hmin⟩ := (hC.diff hW).exists_isMinOn hne continuous_re.abs.continuousOn
    have hzpos : 0 < |z.re| := abs_pos.mpr (by
      intro hzero
      exact hz.2 (hSW ⟨hz.1, hzero⟩))
    refine ⟨|z.re| / 2, by positivity, ?_⟩
    intro w hw hwr
    by_contra hwW
    have hmw : |z.re| ≤ |w.re| := hmin ⟨hw, hwW⟩
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz _
    by_contra hzW
    exact hne ⟨z, hz, hzW⟩

theorem exists_slice_extrema {C : Set ℂ} (hC : IsCompact C) (hCv : Convex ℝ C)
    (hne : (zeroSlice C).Nonempty) :
    ∃ a b : ℝ, a ≤ b ∧
      (∀ z ∈ zeroSlice C, a ≤ z.im ∧ z.im ≤ b) ∧
      ∀ t ∈ Icc a b, (t : ℂ) * I ∈ zeroSlice C := by
  obtain ⟨v, hv, hvmin⟩ := (isCompact_zeroSlice hC).exists_isMinOn hne continuous_im.continuousOn
  obtain ⟨w, hw, hwmax⟩ := (isCompact_zeroSlice hC).exists_isMaxOn hne continuous_im.continuousOn
  refine ⟨v.im, w.im, hvmin hw, fun z hz => ⟨hvmin hz, hwmax hz⟩, ?_⟩
  intro t ht
  have hconv := (convex_zeroSlice hCv).linear_image imLm
  have htmem : t ∈ imLm '' zeroSlice C :=
    hconv.ordConnected.out ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩ ht
  obtain ⟨z, hz, hzt⟩ := htmem
  have heq : z = (t : ℂ) * I := by
    apply Complex.ext
    · simpa using hz.2
    · simpa using hzt
  rwa [← heq]

private theorem clamp_mem {a b y : ℝ} (hab : a ≤ b) : max a (min b y) ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

private theorem abs_sub_clamp_le {a b y d : ℝ} (hab : a ≤ b) (hd : 0 ≤ d)
    (hy : y ∈ Icc (a-d) (b+d)) : |y-max a (min b y)| ≤ d := by
  by_cases hya : y < a
  · rw [min_eq_right (hya.le.trans hab), max_eq_left hya.le, abs_of_nonpos (by linarith)]
    linarith [hy.1]
  · by_cases hyb : b < y
    · rw [min_eq_left hyb.le, max_eq_right hab, abs_of_nonneg (by linarith)]
      linarith [hy.2]
    · rw [min_eq_right (le_of_not_gt hyb), max_eq_right (le_of_not_gt hya), sub_self, abs_zero]
      exact hd

/-- A narrow rectangle lies in the prescribed buffer, while every point of
the compact set in the same real-coordinate band lies strictly between its
horizontal edges. In particular those horizontal edges miss the compact. -/
theorem exists_thin_rectangle {C U : Set ℂ} (hC : IsCompact C) (hCv : Convex ℝ C)
    (hne : (zeroSlice C).Nonempty) (hU : IsOpen U) (hSU : zeroSlice C ⊆ U) :
    ∃ η b t : ℝ, 0 < η ∧ b < t ∧
      closedRectangle (-η) (3*η) b t ⊆ U ∧
      ∀ z ∈ C, |z.re| ≤ 3*η → b < z.im ∧ z.im < t := by
  obtain ⟨a, b, hab, hbounds, hsegment⟩ := exists_slice_extrema hC hCv hne
  obtain ⟨δ, hδ, htube⟩ := (isCompact_zeroSlice hC).exists_thickening_subset_open hU hSU
  let lo := a-δ/4
  let hi := b+δ/4
  have hlohi : lo < hi := by dsimp [lo, hi]; linarith
  have hstrip : IsOpen {z : ℂ | lo < z.im ∧ z.im < hi} :=
    (isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const)
  have hsstrip : zeroSlice C ⊆ {z : ℂ | lo < z.im ∧ z.im < hi} := by
    intro z hz
    obtain ⟨hl, hu⟩ := hbounds z hz
    dsimp [lo, hi]
    constructor <;> linarith
  obtain ⟨γ, hγ, hband⟩ := exists_narrow_band hC hstrip hsstrip
  let η := min (δ/12) (γ/3)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηδ : 3*η ≤ δ/4 := by have := min_le_left (δ/12) (γ/3); dsimp [η]; linarith
  have hηγ : 3*η ≤ γ := by have := min_le_right (δ/12) (γ/3); dsimp [η]; linarith
  refine ⟨η, lo, hi, hη, hlohi, ?_, ?_⟩
  · intro z hz
    have hzre : -η ≤ z.re ∧ z.re ≤ 3*η := hz.1
    have hzim : z.im ∈ Icc (a-δ/4) (b+δ/4) := hz.2
    let w : ℂ := (max a (min b z.im) : ℝ) * I
    have hw : w ∈ zeroSlice C := hsegment _ (clamp_mem hab)
    apply htube
    apply mem_thickening_iff.mpr
    refine ⟨w, hw, ?_⟩
    rw [dist_eq_norm]
    have hr : |z.re| ≤ 3*η := abs_le.mpr ⟨by linarith, hzre.2⟩
    have hd := abs_sub_clamp_le hab (show 0 ≤ δ/4 by positivity) hzim
    calc
      ‖z-w‖ ≤ |(z-w).re| + |(z-w).im| := norm_le_abs_re_add_abs_im _
      _ = |z.re| + |z.im-max a (min b z.im)| := by simp [w]
      _ ≤ 3*η + δ/4 := add_le_add hr hd
      _ < δ := by linarith
  · intro z hz hzr
    exact hband z hz (hzr.trans hηγ)

end AutomaticContinuity.ThinRectangleGeometry
