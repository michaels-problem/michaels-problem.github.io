import AutomaticContinuity.RectangleAdditiveSplitting

set_option autoImplicit false

/-! # Rectangular contour splitting for arbitrary separated output sets

The output sets need not be rectangles. They must avoid their corresponding
contour pieces by a fixed positive distance, and their intersection must lie
inside the contour. The full contour rectangle must still lie in the actual
holomorphic input buffer; this geometric condition is not inferred from
separation of the output sets.
-/

noncomputable section

namespace AutomaticContinuity.RectangleCauchy

open Set Complex
open scoped Interval

def leftContour (l b t : ℝ) : Set ℂ :=
  (fun y : ℝ ↦ (l:ℂ)+(y:ℂ)*I) '' Icc b t

def rightContour (l r b t : ℝ) : Set ℂ :=
  ((fun x : ℝ ↦ (x:ℂ)+(b:ℂ)*I) '' Icc l r ∪
    (fun x : ℝ ↦ (x:ℂ)+(t:ℂ)*I) '' Icc l r) ∪
      (fun y : ℝ ↦ (r:ℂ)+(y:ℂ)*I) '' Icc b t

theorem isCompact_leftContour (l b t : ℝ) : IsCompact (leftContour l b t) :=
  isCompact_Icc.image (by fun_prop)

theorem isCompact_rightContour (l r b t : ℝ) : IsCompact (rightContour l r b t) :=
  ((isCompact_Icc.image (by fun_prop)).union
    (isCompact_Icc.image (by fun_prop))).union (isCompact_Icc.image (by fun_prop))

universe u v
variable {P : Type u} {E : Type v}
variable [NormedAddCommGroup P] [NormedSpace ℂ P] [ProperSpace P]
variable [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem differentiableOn_leftPart_complContour {l r b t : ℝ} (hlr : l ≤ r) (hbt : b ≤ t)
    {f : P × ℂ → E} {V : Set (P × ℂ)} {O : Set P}
    (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) (hO : IsOpen O)
    (hrect : O ×ˢ closedRectangle l r b t ⊆ V) :
    DifferentiableOn ℂ (fun q ↦ leftPart l b t (fun ζ ↦ f (q.1,ζ)) q.2)
      (O ×ˢ (leftContour l b t)ᶜ) := by
  apply differentiableOn_leftPart hbt hV hf (hO.prod (isCompact_leftContour l b t).isClosed.isOpen_compl)
  · intro q hq y hy
    exact hrect ⟨hq.1,vertical_mem_closedRectangle ⟨le_rfl,hlr⟩ hy⟩
  · intro q hq y hy heq
    exact hq.2 ⟨y,hy,heq⟩

theorem differentiableOn_rightPart_complContour {l r b t : ℝ} (hlr : l ≤ r) (hbt : b ≤ t)
    {f : P × ℂ → E} {V : Set (P × ℂ)} {O : Set P}
    (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) (hO : IsOpen O)
    (hrect : O ×ˢ closedRectangle l r b t ⊆ V) :
    DifferentiableOn ℂ (fun q ↦ rightPart l r b t (fun ζ ↦ f (q.1,ζ)) q.2)
      (O ×ˢ (rightContour l r b t)ᶜ) := by
  apply differentiableOn_rightPart hlr hbt hV hf
    (hO.prod (isCompact_rightContour l r b t).isClosed.isOpen_compl)
  · intro q hq x hx
    exact hrect ⟨hq.1,horizontal_mem_closedRectangle ⟨le_rfl,hbt⟩ hx⟩
  · intro q hq x hx
    exact hrect ⟨hq.1,horizontal_mem_closedRectangle ⟨hbt,le_rfl⟩ hx⟩
  · intro q hq y hy
    exact hrect ⟨hq.1,vertical_mem_closedRectangle ⟨hlr,le_rfl⟩ hy⟩
  · intro q hq x hx heq
    exact hq.2 (Or.inl (Or.inl ⟨x,hx,heq⟩))
  · intro q hq x hx heq
    exact hq.2 (Or.inl (Or.inr ⟨x,hx,heq⟩))
  · intro q hq y hy heq
    exact hq.2 (Or.inr ⟨y,hy,heq⟩)

variable [CompleteSpace E]

theorem exists_bounded_additive_split_of_contour_separation
    {l r b t δ M : ℝ} (hlr : l ≤ r) (hbt : b ≤ t) (hδ : 0 < δ) (hM : 0 ≤ M)
    {A B : Set ℂ}
    (hoverlap : A ∩ B ⊆ openRectangle l r b t)
    (hgapA : ∀ z ∈ A, ∀ ζ ∈ rightContour l r b t, δ ≤ ‖ζ-z‖)
    (hgapB : ∀ z ∈ B, ∀ ζ ∈ leftContour l b t, δ ≤ ‖ζ-z‖)
    {f : P × ℂ → E} {V : Set (P × ℂ)} {O K : Set P}
    (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) (hO : IsOpen O)
    (hrect : O ×ˢ closedRectangle l r b t ⊆ V)
    (hbound : ∀ p ∈ K, ∀ z ∈ closedRectangle l r b t, ‖f (p,z)‖ ≤ M) :
    ∃ alpha beta : P × ℂ → E,
      A ⊆ (rightContour l r b t)ᶜ ∧ B ⊆ (leftContour l b t)ᶜ ∧
      DifferentiableOn ℂ alpha (O ×ˢ (rightContour l r b t)ᶜ) ∧
      DifferentiableOn ℂ beta (O ×ˢ (leftContour l b t)ᶜ) ∧
      (∀ p ∈ O, ∀ z ∈ A ∩ B, beta (p,z) - alpha (p,z) = f (p,z)) ∧
      (∀ p ∈ K, ∀ z ∈ A, ‖alpha (p,z)‖ ≤ ((2*|r-l|+|t-b|)/(2*Real.pi*δ))*M) ∧
      (∀ p ∈ K, ∀ z ∈ B, ‖beta (p,z)‖ ≤ ((2*|r-l|+|t-b|)/(2*Real.pi*δ))*M) := by
  let alpha : P × ℂ → E := fun q ↦ -rightPart l r b t (fun ζ ↦ f (q.1,ζ)) q.2
  let beta : P × ℂ → E := fun q ↦ leftPart l b t (fun ζ ↦ f (q.1,ζ)) q.2
  refine ⟨alpha,beta,?_,?_,
    (differentiableOn_rightPart_complContour hlr hbt hV hf hO hrect).neg,
    differentiableOn_leftPart_complContour hlr hbt hV hf hO hrect,?_,?_,?_⟩
  · intro z hz hzc
    have h := hgapA z hz z hzc
    simpa using (not_le.mpr hδ) (by simpa using h)
  · intro z hz hzc
    have h := hgapB z hz z hzc
    simpa using (not_le.mpr hδ) (by simpa using h)
  · intro p hp z hz
    have hc : ContinuousOn (fun ζ ↦ f (p,ζ)) (closedRectangle l r b t) :=
      hf.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun ζ hζ ↦ hrect ⟨hp,hζ⟩)
    have hd : DifferentiableOn ℂ (fun ζ ↦ f (p,ζ)) (openRectangle l r b t) :=
      hf.comp ((differentiable_const p).prodMk differentiable_id).differentiableOn
        (fun ζ hζ ↦ hrect ⟨hp,openRectangle_subset_closedRectangle l r b t hζ⟩)
    simpa only [alpha,beta,sub_neg_eq_add] using leftPart_add_rightPart_eq _ (hoverlap hz) hc hd
  · intro p hp z hz
    have hbnd (y : ℝ) (hy : y ∈ Icc b t) (x : ℝ) (hx : x ∈ Ι l r) :
        ‖f (p,(x:ℂ)+(y:ℂ)*I)‖ ≤ M := by
      apply hbound p hp _ (horizontal_mem_closedRectangle hy _)
      simpa only [uIcc_of_le hlr] using uIoc_subset_uIcc hx
    have hvbnd (y : ℝ) (hy : y ∈ Ι b t) : ‖f (p,(r:ℂ)+(y:ℂ)*I)‖ ≤ M := by
      apply hbound p hp _ (vertical_mem_closedRectangle ⟨hlr,le_rfl⟩ _)
      simpa only [uIcc_of_le hbt] using uIoc_subset_uIcc hy
    have hgb (x : ℝ) (hx : x ∈ Ι l r) : δ ≤ ‖(x:ℂ)+(b:ℂ)*I-z‖ :=
      hgapA z hz _ (Or.inl (Or.inl ⟨x,by simpa only [uIcc_of_le hlr] using uIoc_subset_uIcc hx,rfl⟩))
    have hgt (x : ℝ) (hx : x ∈ Ι l r) : δ ≤ ‖(x:ℂ)+(t:ℂ)*I-z‖ :=
      hgapA z hz _ (Or.inl (Or.inr ⟨x,by simpa only [uIcc_of_le hlr] using uIoc_subset_uIcc hx,rfl⟩))
    have hgr (y : ℝ) (hy : y ∈ Ι b t) : δ ≤ ‖(r:ℂ)+(y:ℂ)*I-z‖ :=
      hgapA z hz _ (Or.inr ⟨y,by simpa only [uIcc_of_le hbt] using uIoc_subset_uIcc hy,rfl⟩)
    simpa only [alpha,norm_neg] using norm_rightPart_le hM hδ
      (hbnd b ⟨le_rfl,hbt⟩) (hbnd t ⟨hbt,le_rfl⟩) hvbnd hgb hgt hgr
  · intro p hp z hz
    have hbnd (y : ℝ) (hy : y ∈ Ι b t) : ‖f (p,(l:ℂ)+(y:ℂ)*I)‖ ≤ M := by
      apply hbound p hp _ (vertical_mem_closedRectangle ⟨le_rfl,hlr⟩ _)
      simpa only [uIcc_of_le hbt] using uIoc_subset_uIcc hy
    have hgl (y : ℝ) (hy : y ∈ Ι b t) : δ ≤ ‖(l:ℂ)+(y:ℂ)*I-z‖ :=
      hgapB z hz _ ⟨y,by simpa only [uIcc_of_le hbt] using uIoc_subset_uIcc hy,rfl⟩
    have hleft := norm_leftPart_le (f := fun ζ ↦ f (p,ζ)) hM hδ hbnd hgl
    exact hleft.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by have := abs_nonneg (r-l); linarith) (by positivity)) hM)

end AutomaticContinuity.RectangleCauchy
