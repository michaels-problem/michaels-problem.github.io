import AutomaticContinuity.CoordinateCutChart

set_option autoImplicit false

/-! # Compact and convex source sets in a coordinate-cut chart -/

noncomputable section

namespace AutomaticContinuity.CoordinateCutChart

open Set

def linearPart {n : ℕ} (j : Fin n) (a : ℂ) :
    FinitePoint n →ₗ[ℝ] Remaining j × ℂ where
  toFun z := (fun i => z i, a * z j)
  map_add' z w := by ext <;> simp [mul_add]
  map_smul' s z := by
    ext
    · simp
    · simp
      ring

def affineChart {n : ℕ} (j : Fin n) (a : ℂ) (ha : a ≠ 0) (b : ℝ) :
    FinitePoint n →ᵃ[ℝ] Remaining j × ℂ where
  toFun := chart j a ha b
  linear := linearPart j a
  map_vadd' z w := by
    apply Prod.ext
    · rfl
    · change a * (w j + z j) - (b : ℂ) = a * w j + (a * z j - (b : ℂ))
      ring

theorem convex_preimage {n : ℕ} (j : Fin n) (a : ℂ) (ha : a ≠ 0) (b : ℝ)
    {S : Set (Remaining j × ℂ)} (hS : Convex ℝ S) :
    Convex ℝ ((homeomorph j a ha b) ⁻¹' S) :=
  hS.affine_preimage (affineChart j a ha b)

theorem isCompact_preimage {n : ℕ} (j : Fin n) (a : ℂ) (ha : a ≠ 0) (b : ℝ)
    {S : Set (Remaining j × ℂ)} (hS : IsCompact S) :
    IsCompact ((homeomorph j a ha b) ⁻¹' S) :=
  (homeomorph j a ha b).isCompact_preimage.mpr hS

theorem convex_closedRectangle (l r b t : ℝ) :
    Convex ℝ (RectangleCauchy.closedRectangle l r b t) := by
  exact (convex_Icc l r).linear_preimage Complex.reLm |>.inter
    ((convex_Icc b t).linear_preimage Complex.imLm)

end AutomaticContinuity.CoordinateCutChart
