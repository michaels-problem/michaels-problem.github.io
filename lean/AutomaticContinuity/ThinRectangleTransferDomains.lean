import AutomaticContinuity.ThinRectangleOpenCaps
import AutomaticContinuity.ConvexCompactBuffer
import AutomaticContinuity.CoordinateCutConvexity

set_option autoImplicit false

/-! # Actual open domains and a fixed compact error buffer for one product cut

The open output domains are selected before any parameter polynomial. The
transverse output window lies inside a compact convex transverse buffer, so
the contour norm estimate controls the correction on the entire open output
domain. The error rectangle is strictly to the right of the old cutting line.
-/

noncomputable section

namespace AutomaticContinuity.ThinRectangleGeometry

open Set Metric Complex RectangleCauchy

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

structure ProductTransferData (D : Set P) (C : Set ℂ) (U V : Set (P × ℂ)) where
  base : Set P
  bufferBase : Set P
  left : Set ℂ
  right : Set ℂ
  eta : ℝ
  bottom : ℝ
  top : ℝ
  gap : ℝ
  base_open : IsOpen base
  buffer_compact : IsCompact bufferBase
  buffer_convex : Convex ℝ bufferBase
  original_subset_base : D ⊆ base
  base_subset_buffer : base ⊆ bufferBase
  left_open : IsOpen left
  right_open : IsOpen right
  eta_pos : 0 < eta
  bottom_lt_top : bottom < top
  gap_pos : 0 < gap
  cover : C ⊆ left ∪ right
  old_subset_left : C ∩ {z | z.re ≤ 0} ⊆ left
  left_domain : base ×ˢ left ⊆ U ∩ V
  right_domain : base ×ˢ right ⊆ U
  buffer_domain : bufferBase ×ˢ closedRectangle (eta/2) (5*eta/2) bottom top ⊆ U ∩ V
  overlap : left ∩ right ⊆ openRectangle (eta/2) (5*eta/2) bottom top
  gap_left : ∀ z ∈ left, ∀ ζ ∈ rightContour (eta/2) (5*eta/2) bottom top, gap ≤ ‖ζ-z‖
  gap_right : ∀ z ∈ right, ∀ ζ ∈ leftContour (eta/2) bottom top, gap ≤ ‖ζ-z‖

namespace ProductTransferData

variable {D : Set P} {C : Set ℂ} {U V : Set (P × ℂ)}

def errorSet (d : ProductTransferData D C U V) : Set (P × ℂ) :=
  d.bufferBase ×ˢ closedRectangle (d.eta/2) (5*d.eta/2) d.bottom d.top

theorem errorSet_compact (d : ProductTransferData D C U V) : IsCompact d.errorSet :=
  d.buffer_compact.prod (isCompact_Icc.reProdIm isCompact_Icc)

theorem errorSet_convex (d : ProductTransferData D C U V) : Convex ℝ d.errorSet :=
  d.buffer_convex.prod (CoordinateCutChart.convex_closedRectangle _ _ _ _)

theorem errorSet_re_lower (d : ProductTransferData D C U V) {q : P × ℂ}
    (hq : q ∈ d.errorSet) : d.eta/2 ≤ q.2.re := hq.2.1.1

theorem product_cover (d : ProductTransferData D C U V) :
    D ×ˢ C ⊆ (d.base ×ˢ d.right) ∪ (d.base ×ˢ d.left) := by
  intro q hq
  rcases d.cover hq.2 with hleft | hright
  · exact Or.inr ⟨d.original_subset_base hq.1,hleft⟩
  · exact Or.inl ⟨d.original_subset_base hq.1,hright⟩

theorem old_product_subset (d : ProductTransferData D C U V) :
    D ×ˢ (C ∩ {z | z.re ≤ 0}) ⊆ d.base ×ˢ d.left :=
  prod_mono d.original_subset_base d.old_subset_left

def splittingConstant (d : ProductTransferData D C U V) : ℝ :=
  2*((2*|5*d.eta/2-d.eta/2|+|d.top-d.bottom|)/(2*Real.pi*d.gap))

theorem splittingConstant_pos (d : ProductTransferData D C U V) : 0 < d.splittingConstant := by
  have hwidth : 0 < |d.top-d.bottom| := abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt d.bottom_lt_top))
  have hgap := d.gap_pos
  unfold splittingConstant
  positivity

end ProductTransferData

variable [ProperSpace P]

/-- Select all compact buffers and open domains for a product cut from the
actual section domain `U` and family/parameter domain `V`. -/
theorem exists_product_transfer_data
    {D : Set P} {C : Set ℂ} {U V : Set (P × ℂ)}
    (hD : IsCompact D) (hDconv : Convex ℝ D)
    (hC : IsCompact C) (hCconv : Convex ℝ C)
    (hne : (zeroSlice C).Nonempty) (hU : IsOpen U) (hV : IsOpen V)
    (hwhole : D ×ˢ C ⊆ U) (hold : D ×ˢ (C ∩ {z | z.re ≤ 0}) ⊆ V) :
    Nonempty (ProductTransferData D C U V) := by
  have hcap : IsCompact (C ∩ {z | z.re ≤ 0}) :=
    hC.inter_right (isClosed_le continuous_re continuous_const)
  obtain ⟨Ou,Vu,hOu,_,hDOu,hCVu,hUV⟩ := generalized_tube_lemma hD hC hU hwhole
  obtain ⟨Ov,Vv,hOv,_,hDOv,hcapVv,hVV⟩ := generalized_tube_lemma hD hcap hV hold
  obtain ⟨Dplus,O,hDplus,hDplusconv,hO,hDO,hODplus,hDplusUV⟩ :=
    exists_transverse_compact_convex_buffer hD hDconv (hOu.inter hOv) (subset_inter hDOu hDOv)
  have hold' : Dplus ×ˢ (C ∩ {z | z.re ≤ 0}) ⊆ U ∩ V := by
    intro q hq
    exact ⟨hUV ⟨(hDplusUV hq.1).1,hCVu hq.2.1⟩,
      hVV ⟨(hDplusUV hq.1).2,hcapVv hq.2⟩⟩
  obtain ⟨Oq,η,b,t,δ,hOq,hDplusOq,hη,hbt,hδ,hQ,_,hleft, hcover,hoverlap,hgapL,hgapR⟩ :=
    exists_buffered_product_caps hDplus hC hCconv hne (hU.inter hV) hold'
  have hleftUV : Dplus ×ˢ leftCap C η ⊆ U ∩ V :=
    (prod_mono hDplusOq Subset.rfl).trans hleft
  have hrightU : Dplus ×ˢ rightCap C η ⊆ U := by
    intro q hq
    exact hUV ⟨(hDplusUV hq.1).1,hCVu hq.2.1⟩
  obtain ⟨OL,VL,_,hVL,hDplusOL,hLcapVL,hLV⟩ :=
    generalized_tube_lemma hDplus (isCompact_leftCap hC η) (hU.inter hV) hleftUV
  obtain ⟨OR,VR,_,hVR,hDplusOR,hRcapVR,hRU⟩ :=
    generalized_tube_lemma hDplus (isCompact_rightCap hC η) hU hrightU
  obtain ⟨left,right,hleftOpen,hrightOpen,hLleft,hRright,hleftVL,hrightVR,hmeet,hgapLeft,hgapRight⟩ :=
    exists_open_caps_with_gaps (isCompact_leftCap hC η) (isCompact_rightCap hC η)
      hVL hVR (isOpen_openRectangle _ _ _ _) hLcapVL hRcapVR hoverlap hδ hgapL hgapR
  refine ⟨{
    base := O
    bufferBase := Dplus
    left := left
    right := right
    eta := η
    bottom := b
    top := t
    gap := δ/2
    base_open := hO
    buffer_compact := hDplus
    buffer_convex := hDplusconv
    original_subset_base := hDO
    base_subset_buffer := hODplus
    left_open := hleftOpen
    right_open := hrightOpen
    eta_pos := hη
    bottom_lt_top := hbt
    gap_pos := half_pos hδ
    cover := ?_
    old_subset_left := ?_
    left_domain := ?_
    right_domain := ?_
    buffer_domain := (prod_mono hDplusOq Subset.rfl).trans hQ
    overlap := hmeet
    gap_left := hgapLeft
    gap_right := hgapRight }⟩
  · intro z hz
    have hh : z ∈ leftCap C η ∪ rightCap C η := hcover.symm ▸ hz
    exact hh.elim (fun h ↦ Or.inl (hLleft h)) (fun h ↦ Or.inr (hRright h))
  · intro z hz
    apply hLleft
    exact ⟨hz.1,show z.re ≤ 2*η by have hz0 : z.re ≤ 0 := hz.2; linarith⟩
  · intro q hq
    exact hLV ⟨hDplusOL (hODplus hq.1),hleftVL hq.2⟩
  · intro q hq
    exact hRU ⟨hDplusOR (hODplus hq.1),hrightVR hq.2⟩

end AutomaticContinuity.ThinRectangleGeometry
