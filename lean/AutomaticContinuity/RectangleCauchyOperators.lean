import AutomaticContinuity.ContourIntegralOperators
import AutomaticContinuity.RectangleCauchyIntegral

set_option autoImplicit false

/-! # The two fixed rectangular Cauchy operators

The downward left edge defines `leftPart`; the other three edges define
`rightPart`. Their sum is the normalized positively oriented boundary
integral. Each is holomorphic jointly in all parameters wherever its own
contour is avoided, with an explicit contour-length / separation bound.
-/

noncomputable section

namespace AutomaticContinuity.RectangleCauchy

open Set Complex
open scoped Interval

universe u v
variable {P : Type u} {E : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]

def cauchyFactor : ℂ := (2 * Real.pi * I)⁻¹

theorem norm_cauchyFactor : ‖cauchyFactor‖ = 1 / (2 * Real.pi) := by
  simp [cauchyFactor, Real.pi_pos.le, abs_of_nonneg, one_div]

def horizontalCauchy (l r y : ℝ) (f : ℂ → E) (z : ℂ) : E :=
  horizontalIntegral l r y (fun ζ ↦ (ζ - z)⁻¹ • f ζ)

def verticalCauchy (b t x : ℝ) (f : ℂ → E) (z : ℂ) : E :=
  verticalIntegral b t x (fun ζ ↦ (ζ - z)⁻¹ • f ζ)

def leftPart (l b t : ℝ) (f : ℂ → E) (z : ℂ) : E :=
  -(cauchyFactor • verticalCauchy b t l f z)

def rightPart (l r b t : ℝ) (f : ℂ → E) (z : ℂ) : E :=
  cauchyFactor • (horizontalCauchy l r b f z - horizontalCauchy l r t f z +
    verticalCauchy b t r f z)

theorem leftPart_add_rightPart (l r b t : ℝ) (f : ℂ → E) (z : ℂ) :
    leftPart l b t f z + rightPart l r b t f z =
      cauchyFactor • rectangleIntegral l r b t (fun ζ ↦ (ζ-z)⁻¹ • f ζ) := by
  simp only [leftPart, rightPart, rectangleIntegral, horizontalCauchy, verticalCauchy,
    smul_sub, smul_add]
  abel

theorem norm_horizontalCauchy_le {l r y M δ : ℝ} {f : ℂ → E} {z : ℂ}
    (hM : 0 ≤ M) (hδ : 0 < δ)
    (hf : ∀ x ∈ Ι l r, ‖f ((x:ℂ)+(y:ℂ)*I)‖ ≤ M)
    (hgap : ∀ x ∈ Ι l r, δ ≤ ‖(x:ℂ)+(y:ℂ)*I-z‖) :
    ‖horizontalCauchy l r y f z‖ ≤ (M/δ)*|r-l| :=
  ContourIntegralOperators.norm_cauchyIntegral_le hM hδ hf hgap

theorem norm_verticalCauchy_le {b t x M δ : ℝ} {f : ℂ → E} {z : ℂ}
    (hM : 0 ≤ M) (hδ : 0 < δ)
    (hf : ∀ y ∈ Ι b t, ‖f ((x:ℂ)+(y:ℂ)*I)‖ ≤ M)
    (hgap : ∀ y ∈ Ι b t, δ ≤ ‖(x:ℂ)+(y:ℂ)*I-z‖) :
    ‖verticalCauchy b t x f z‖ ≤ (M/δ)*|t-b| := by
  rw [verticalCauchy, verticalIntegral, norm_smul, norm_I, one_mul]
  exact ContourIntegralOperators.norm_cauchyIntegral_le hM hδ hf hgap

theorem norm_leftPart_le {l b t M δ : ℝ} {f : ℂ → E} {z : ℂ}
    (hM : 0 ≤ M) (hδ : 0 < δ)
    (hf : ∀ y ∈ Ι b t, ‖f ((l:ℂ)+(y:ℂ)*I)‖ ≤ M)
    (hgap : ∀ y ∈ Ι b t, δ ≤ ‖(l:ℂ)+(y:ℂ)*I-z‖) :
    ‖leftPart l b t f z‖ ≤ (|t-b| / (2*Real.pi*δ))*M := by
  rw [leftPart, norm_neg, norm_smul, norm_cauchyFactor]
  calc
    _ ≤ (1/(2*Real.pi))*((M/δ)*|t-b|) :=
      mul_le_mul_of_nonneg_left (norm_verticalCauchy_le hM hδ hf hgap) (by positivity)
    _ = _ := by ring

theorem norm_rightPart_le {l r b t M δ : ℝ} {f : ℂ → E} {z : ℂ}
    (hM : 0 ≤ M) (hδ : 0 < δ)
    (hbottom : ∀ x ∈ Ι l r, ‖f ((x:ℂ)+(b:ℂ)*I)‖ ≤ M)
    (htop : ∀ x ∈ Ι l r, ‖f ((x:ℂ)+(t:ℂ)*I)‖ ≤ M)
    (hright : ∀ y ∈ Ι b t, ‖f ((r:ℂ)+(y:ℂ)*I)‖ ≤ M)
    (hgbottom : ∀ x ∈ Ι l r, δ ≤ ‖(x:ℂ)+(b:ℂ)*I-z‖)
    (hgtop : ∀ x ∈ Ι l r, δ ≤ ‖(x:ℂ)+(t:ℂ)*I-z‖)
    (hgright : ∀ y ∈ Ι b t, δ ≤ ‖(r:ℂ)+(y:ℂ)*I-z‖) :
    ‖rightPart l r b t f z‖ ≤ ((2*|r-l|+|t-b|)/(2*Real.pi*δ))*M := by
  have h₁ := norm_horizontalCauchy_le hM hδ hbottom hgbottom
  have h₂ := norm_horizontalCauchy_le hM hδ htop hgtop
  have h₃ := norm_verticalCauchy_le hM hδ hright hgright
  rw [rightPart, norm_smul, norm_cauchyFactor]
  calc
    _ ≤ (1/(2*Real.pi))*(((M/δ)*|r-l|+(M/δ)*|r-l|)+(M/δ)*|t-b|) := by
      gcongr
      exact (norm_add_le _ _).trans (add_le_add
        ((norm_sub_le _ _).trans (add_le_add h₁ h₂)) h₃)
    _ = _ := by ring

section Holomorphy

variable [NormedAddCommGroup P] [NormedSpace ℂ P] [ProperSpace P]

theorem differentiableOn_horizontalCauchy {l r y : ℝ} (hlr : l ≤ r)
    {f : P × ℂ → E} {V U : Set (P × ℂ)}
    (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) (hU : IsOpen U)
    (htrace : ∀ q ∈ U, ∀ x ∈ Icc l r, (q.1, (x:ℂ)+(y:ℂ)*I) ∈ V)
    (havoid : ∀ q ∈ U, ∀ x ∈ Icc l r, (x:ℂ)+(y:ℂ)*I ≠ q.2) :
    DifferentiableOn ℂ (fun q ↦ horizontalCauchy l r y (fun ζ ↦ f (q.1,ζ)) q.2) U := by
  exact ContourIntegralOperators.differentiableOn_cauchyIntegral hlr (by fun_prop)
    hV hf hU htrace havoid

theorem differentiableOn_verticalCauchy {b t x : ℝ} (hbt : b ≤ t)
    {f : P × ℂ → E} {V U : Set (P × ℂ)}
    (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) (hU : IsOpen U)
    (htrace : ∀ q ∈ U, ∀ y ∈ Icc b t, (q.1, (x:ℂ)+(y:ℂ)*I) ∈ V)
    (havoid : ∀ q ∈ U, ∀ y ∈ Icc b t, (x:ℂ)+(y:ℂ)*I ≠ q.2) :
    DifferentiableOn ℂ (fun q ↦ verticalCauchy b t x (fun ζ ↦ f (q.1,ζ)) q.2) U := by
  exact (ContourIntegralOperators.differentiableOn_cauchyIntegral hbt (by fun_prop)
    hV hf hU htrace havoid).const_smul I

theorem differentiableOn_leftPart {l b t : ℝ} (hbt : b ≤ t)
    {f : P × ℂ → E} {V U : Set (P × ℂ)}
    (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) (hU : IsOpen U)
    (htrace : ∀ q ∈ U, ∀ y ∈ Icc b t, (q.1, (l:ℂ)+(y:ℂ)*I) ∈ V)
    (havoid : ∀ q ∈ U, ∀ y ∈ Icc b t, (l:ℂ)+(y:ℂ)*I ≠ q.2) :
    DifferentiableOn ℂ (fun q ↦ leftPart l b t (fun ζ ↦ f (q.1,ζ)) q.2) U :=
  ((differentiableOn_verticalCauchy hbt hV hf hU htrace havoid).const_smul cauchyFactor).neg

theorem differentiableOn_rightPart {l r b t : ℝ} (hlr : l ≤ r) (hbt : b ≤ t)
    {f : P × ℂ → E} {V U : Set (P × ℂ)}
    (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) (hU : IsOpen U)
    (hb : ∀ q ∈ U, ∀ x ∈ Icc l r, (q.1, (x:ℂ)+(b:ℂ)*I) ∈ V)
    (ht : ∀ q ∈ U, ∀ x ∈ Icc l r, (q.1, (x:ℂ)+(t:ℂ)*I) ∈ V)
    (hr : ∀ q ∈ U, ∀ y ∈ Icc b t, (q.1, (r:ℂ)+(y:ℂ)*I) ∈ V)
    (hgb : ∀ q ∈ U, ∀ x ∈ Icc l r, (x:ℂ)+(b:ℂ)*I ≠ q.2)
    (hgt : ∀ q ∈ U, ∀ x ∈ Icc l r, (x:ℂ)+(t:ℂ)*I ≠ q.2)
    (hgr : ∀ q ∈ U, ∀ y ∈ Icc b t, (r:ℂ)+(y:ℂ)*I ≠ q.2) :
    DifferentiableOn ℂ (fun q ↦ rightPart l r b t (fun ζ ↦ f (q.1,ζ)) q.2) U :=
  (((differentiableOn_horizontalCauchy hlr hV hf hU hb hgb).sub
    (differentiableOn_horizontalCauchy hlr hV hf hU ht hgt)).add
      (differentiableOn_verticalCauchy hbt hV hf hU hr hgr)).const_smul cauchyFactor

end Holomorphy

end AutomaticContinuity.RectangleCauchy
