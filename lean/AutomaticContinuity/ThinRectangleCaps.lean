import AutomaticContinuity.ThinRectangleGeometry

set_option autoImplicit false

/-!
# Separated caps and their actual Cauchy contour

The final contour is strictly to the right of the original cutting line, so
its full closed rectangle is disjoint from the original approximation cap.
The two enlarged caps cover the compact set and have positive distances to
the respective contour pieces used in bounded additive splitting.
-/

noncomputable section

namespace AutomaticContinuity.ThinRectangleGeometry

open Set Metric Complex RectangleCauchy

def leftCap (C : Set ℂ) (η : ℝ) : Set ℂ := C ∩ {z | z.re ≤ 2*η}
def rightCap (C : Set ℂ) (η : ℝ) : Set ℂ := C ∩ {z | η ≤ z.re}

theorem isCompact_leftCap {C : Set ℂ} (hC : IsCompact C) (η : ℝ) :
    IsCompact (leftCap C η) := hC.inter_right (isClosed_le continuous_re continuous_const)

theorem isCompact_rightCap {C : Set ℂ} (hC : IsCompact C) (η : ℝ) :
    IsCompact (rightCap C η) := hC.inter_right (isClosed_le continuous_const continuous_re)

theorem exists_contour_gap {A T : Set ℂ} (hA : IsClosed A) (hT : IsCompact T)
    (hdis : Disjoint A T) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ A, ∀ ζ ∈ T, δ ≤ ‖ζ-z‖ := by
  have hTA : T ⊆ Aᶜ := fun ζ hζ hz => Set.disjoint_left.mp hdis hz hζ
  obtain ⟨δ, hδ, htube⟩ := hT.exists_cthickening_subset_open hA.isOpen_compl hTA
  refine ⟨δ, hδ, ?_⟩
  intro z hz ζ hζ
  by_contra hgap
  have hd : dist z ζ ≤ δ := by
    rw [dist_comm, dist_eq_norm]
    exact (lt_of_not_ge hgap).le
  exact htube (mem_cthickening_of_dist_le z ζ δ T hζ hd) hz

theorem exists_buffered_caps {C U : Set ℂ} (hC : IsCompact C) (hCv : Convex ℝ C)
    (hne : (zeroSlice C).Nonempty) (hU : IsOpen U)
    (hcapU : C ∩ {z | z.re ≤ 0} ⊆ U) :
    ∃ η b t δ : ℝ, 0 < η ∧ b < t ∧ 0 < δ ∧
      closedRectangle (η/2) (5*η/2) b t ⊆ U ∧
      Disjoint (C ∩ {z | z.re ≤ 0}) (closedRectangle (η/2) (5*η/2) b t) ∧
      leftCap C η ⊆ U ∧ leftCap C η ∪ rightCap C η = C ∧
      leftCap C η ∩ rightCap C η ⊆ openRectangle (η/2) (5*η/2) b t ∧
      (∀ z ∈ leftCap C η, ∀ ζ ∈ rightContour (η/2) (5*η/2) b t, δ ≤ ‖ζ-z‖) ∧
      (∀ z ∈ rightCap C η, ∀ ζ ∈ leftContour (η/2) b t, δ ≤ ‖ζ-z‖) := by
  obtain ⟨η, b, t, hη, hbt, hrect, hband⟩ :=
    exists_thin_rectangle hC hCv hne hU (fun z hz => hcapU ⟨hz.1, hz.2.le⟩)
  have hrect' : closedRectangle (η/2) (5*η/2) b t ⊆ U := by
    intro z hz
    apply hrect
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  have hhor (x : ℝ) (hx : x ∈ Icc (η/2) (5*η/2)) :
      (x:ℂ)+(b:ℂ)*I ∉ C ∧ (x:ℂ)+(t:ℂ)*I ∉ C := by
    have hxr : |x| ≤ 3*η := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    constructor
    · intro hz
      have he := hband _ hz (by simpa using hxr)
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
        mul_one, mul_zero, add_zero, zero_add] at he
      exact (lt_irrefl b) he.1
    · intro hz
      have he := hband _ hz (by simpa using hxr)
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
        mul_one, mul_zero, add_zero, zero_add] at he
      exact (lt_irrefl t) he.2
  have hdisA : Disjoint (leftCap C η) (rightContour (η/2) (5*η/2) b t) := by
    apply Set.disjoint_left.mpr
    intro z hz hzc
    rcases hzc with (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨y, hy, rfl⟩
    · exact (hhor x hx).1 hz.1
    · exact (hhor x hx).2 hz.1
    · have hr := hz.2
      simp at hr
      linarith
  have hdisB : Disjoint (rightCap C η) (leftContour (η/2) b t) := by
    apply Set.disjoint_left.mpr
    rintro z hz ⟨y, hy, rfl⟩
    have hr := hz.2
    simp at hr
    linarith
  obtain ⟨δA, hδA, hgapA⟩ := exists_contour_gap (isCompact_leftCap hC η).isClosed
    (isCompact_rightContour (η/2) (5*η/2) b t) hdisA
  obtain ⟨δB, hδB, hgapB⟩ := exists_contour_gap (isCompact_rightCap hC η).isClosed
    (isCompact_leftContour (η/2) b t) hdisB
  refine ⟨η, b, t, min δA δB, hη, hbt, lt_min hδA hδB, hrect', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro z hz hzr
    have hz0 : z.re ≤ 0 := hz.2
    have hzr0 : η/2 ≤ z.re := hzr.1.1
    linarith
  · intro z hz
    have hz2 : z.re ≤ 2*η := hz.2
    by_cases hr : z.re ≤ 0
    · exact hcapU ⟨hz.1, hr⟩
    · have him := hband z hz.1 (abs_le.mpr ⟨by linarith, by linarith⟩)
      exact hrect ⟨⟨by linarith, by linarith⟩, ⟨him.1.le, him.2.le⟩⟩
  · ext z
    constructor
    · intro hz
      exact hz.elim And.left And.left
    · intro hz
      by_cases hr : z.re ≤ 2*η
      · exact Or.inl ⟨hz, hr⟩
      · exact Or.inr ⟨hz, show η ≤ z.re by linarith⟩
  · intro z hz
    have hz1 : η ≤ z.re := hz.2.2
    have hz2 : z.re ≤ 2*η := hz.1.2
    have him := hband z hz.1.1 (abs_le.mpr ⟨by linarith, by linarith⟩)
    exact ⟨⟨by linarith, by linarith⟩, him⟩
  · intro z hz ζ hζ
    exact (min_le_left _ _).trans (hgapA z hz ζ hζ)
  · intro z hz ζ hζ
    exact (min_le_right _ _).trans (hgapB z hz ζ hζ)

end AutomaticContinuity.ThinRectangleGeometry
