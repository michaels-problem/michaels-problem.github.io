import AutomaticContinuity.PolynomialExteriorCutoff
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false

/-!
# A union theorem for polynomially separated compact sets

Two compact polynomially convex sets have polynomially convex union whenever
one polynomial maps them to the radius-`1/8` discs around zero and one. The
proof glues normalized separating polynomials using the explicit cubic cutoff.
It does not invoke a Runge or Kallin theorem or assume convexity of the union.
-/

noncomputable section

namespace AutomaticContinuity.PolynomialConvexUnion

open Set MvPolynomial

universe u v
variable {X : Type u} {σ : Type v}

private theorem norm_blend_le {a b c : ℂ} {B δ : ℝ}
    (hB : 0 ≤ B) (_hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hBδ : B * δ ≤ 1 / 8)
    (ha : ‖a‖ ≤ 1 / 8) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ δ) :
    ‖a * (1 - c) + b * c‖ ≤ 3 / 8 := by
  have hcomp : ‖1 - c‖ ≤ 1 + δ := by
    exact (norm_sub_le _ _).trans (by simpa only [norm_one] using add_le_add le_rfl hc)
  calc
    ‖a * (1 - c) + b * c‖ ≤ ‖a * (1 - c)‖ + ‖b * c‖ := norm_add_le _ _
    _ = ‖a‖ * ‖1 - c‖ + ‖b‖ * ‖c‖ := by rw [norm_mul, norm_mul]
    _ ≤ (1 / 8 : ℝ) * (1 + δ) + B * δ := by gcongr
    _ ≤ 3 / 8 := by nlinarith

/-- The separating polynomial hypothesis supplies an explicit common cutoff;
compactness is used only to bound the cross-values of the two point-separators. -/
theorem isPolynomiallyConvexOf_union [TopologicalSpace X]
    (e : X → σ → ℂ) (he : Continuous e) {K L : Set X}
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hK : IsPolynomiallyConvexOf e K) (hL : IsPolynomiallyConvexOf e L)
    (q : MvPolynomial σ ℂ)
    (hqK : ∀ y ∈ K, ‖eval (e y) q‖ ≤ 1 / 8)
    (hqL : ∀ y ∈ L, ‖eval (e y) q - 1‖ ≤ 1 / 8) :
    IsPolynomiallyConvexOf e (K ∪ L) := by
  apply (isPolynomiallyConvexOf_iff_separation e (K ∪ L)).mpr
  intro x hx
  have hxK : x ∉ K := fun hxK => hx (Or.inl hxK)
  have hxL : x ∉ L := fun hxL => hx (Or.inr hxL)
  obtain ⟨a, hax, haK⟩ := PolynomialExteriorCutoff.exists_normalized_polynomial_of_convex
    e K hK x hxK (by norm_num : (0 : ℝ) < 1 / 8)
  obtain ⟨b, hbx, hbL⟩ := PolynomialExteriorCutoff.exists_normalized_polynomial_of_convex
    e L hL x hxL (by norm_num : (0 : ℝ) < 1 / 8)
  obtain ⟨Ca, hCa⟩ := hLcompact.exists_bound_of_continuousOn
    (((MvPolynomial.continuous_eval a).comp he).continuousOn)
  obtain ⟨Cb, hCb⟩ := hKcompact.exists_bound_of_continuousOn
    (((MvPolynomial.continuous_eval b).comp he).continuousOn)
  let B : ℝ := max 0 (max Ca Cb)
  have hB : 0 ≤ B := le_max_left _ _
  have hCaB : Ca ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hCbB : Cb ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  let δ : ℝ := 1 / (8 * (B + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ * (8 * (B + 1)) = 1 := by dsimp [δ]; field_simp
  have hBδ0 : 0 ≤ B * δ := mul_nonneg hB hδ.le
  have hδ1 : δ ≤ 1 := by nlinarith
  have hBδ : B * δ ≤ 1 / 8 := by nlinarith
  obtain ⟨c, hcK, hcL, _, _⟩ := PolynomialCutoff.exists_polynomial_cutoff
    (e '' K) (e '' L) q
    (by rintro _ ⟨y, hy, rfl⟩; exact hqK y hy)
    (by rintro _ ⟨y, hy, rfl⟩; exact hqL y hy) hδ
  let p : MvPolynomial σ ℂ := a * (1 - c) + b * c
  have hpx : eval (e x) p = 1 := by
    simp only [p, map_add, map_mul, map_sub, map_one, hax, hbx]
    ring
  refine ⟨p, 3 / 8, ?_, ?_⟩
  · intro y hy
    rcases hy with hyK | hyL
    · simp only [p, map_add, map_mul, map_sub, map_one]
      exact norm_blend_le hB hδ.le hδ1 hBδ (haK y hyK).le
        ((hCb y hyK).trans hCbB) (hcK (e y) ⟨y, hyK, rfl⟩).le
    · have hcut : ‖1 - eval (e y) c‖ ≤ δ := by
        rw [norm_sub_rev]
        exact (hcL (e y) ⟨y, hyL, rfl⟩).le
      have hbound := norm_blend_le hB hδ.le hδ1 hBδ (hbL y hyL).le
        ((hCa y hyL).trans hCaB) hcut
      have heval : eval (e y) p =
          eval (e y) b * (1 - (1 - eval (e y) c)) +
            eval (e y) a * (1 - eval (e y) c) := by
        simp only [p, map_add, map_mul, map_sub, map_one]
        ring
      rwa [heval]
  · rw [hpx, norm_one]
    norm_num

end AutomaticContinuity.PolynomialConvexUnion
