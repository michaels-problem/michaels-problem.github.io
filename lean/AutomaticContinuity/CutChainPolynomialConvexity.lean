import AutomaticContinuity.ConvexProductPolynomialConvexity
import AutomaticContinuity.CircumscribedCoordinatePolygons

set_option autoImplicit false

/-! # Actual polynomial convexity of every finite halfspace stage -/

noncomputable section

namespace AutomaticContinuity.FiniteHalfspaceExhaustion

open Set

def coordinateRegion {n N : ℕ} (S : ℝ) (q : Fin N → CoordinateCut n)
    (k : ℕ) (j : Fin n) : Set ℂ :=
  {ζ | |ζ.re| ≤ S ∧ |ζ.im| ≤ S ∧
    ∀ i : Fin N, k ≤ i.val → (q i).coordinate = j →
      ((q i).coefficient * ζ).re ≤ (q i).bound}

theorem mem_cutChain_iff_coordinates {n N : ℕ} (S : ℝ)
    (q : Fin N → CoordinateCut n) (k : ℕ) (z : FinitePoint n) :
    z ∈ cutChain (closedBox n S) q k ↔ ∀ j, z j ∈ coordinateRegion S q k j := by
  constructor
  · rintro ⟨hz, hcuts⟩ j
    refine ⟨(hz j).1, (hz j).2, ?_⟩
    intro i hki hij
    have h := mem_iInter₂.mp hcuts i hki
    change ((q i).coefficient * z (q i).coordinate).re ≤ (q i).bound at h
    simpa only [hij] using h
  · intro hz
    refine ⟨fun j => ⟨(hz j).1, (hz j).2.1⟩, mem_iInter₂.mpr ?_⟩
    intro i hki
    exact (hz (q i).coordinate).2.2 i hki rfl

theorem convex_coordinateRegion {n N : ℕ} (S : ℝ)
    (q : Fin N → CoordinateCut n) (k : ℕ) (j : Fin n) :
    Convex ℝ (coordinateRegion S q k j) := by
  intro x hx y hy a b ha hb hab
  have habs {u v : ℝ} (hu : |u| ≤ S) (hv : |v| ≤ S) : |a*u+b*v| ≤ S := by
    calc
      |a*u+b*v| ≤ |a*u|+|b*v| := abs_add_le _ _
      _ = a*|u|+b*|v| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a*S+b*S := add_le_add (mul_le_mul_of_nonneg_left hu ha)
        (mul_le_mul_of_nonneg_left hv hb)
      _ = S := by rw [← add_mul, hab, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · simpa using habs hx.1 hy.1
  · simpa using habs hx.2.1 hy.2.1
  · intro i hki hij
    have hlin : ((q i).coefficient * (a • x + b • y)).re =
        a * ((q i).coefficient*x).re + b * ((q i).coefficient*y).re := by
      simp [Complex.real_smul, mul_add, Complex.mul_re]
      ring
    rw [hlin]
    calc
      _ ≤ a*(q i).bound+b*(q i).bound := add_le_add
        (mul_le_mul_of_nonneg_left (hx.2.2 i hki hij) ha)
        (mul_le_mul_of_nonneg_left (hy.2.2 i hki hij) hb)
      _ = (q i).bound := by rw [← add_mul, hab, one_mul]

theorem isPolynomiallyConvex_cutChain {n N : ℕ} {S : ℝ} (hS : 0 ≤ S)
    (q : Fin N → CoordinateCut n) (k : ℕ) :
    IsPolynomiallyConvexOf (fun z : FinitePoint n => z)
      (cutChain (closedBox n S) q k) := by
  let K := cutChain (closedBox n S) q k
  have hKc : IsCompact K := isCompact_cutChain (isCompact_closedBox n hS) q k
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  exact PolynomialFunctionAlgebra.isPolynomiallyConvex_of_convex_product K
    (coordinateRegion S q k) (mem_cutChain_iff_coordinates S q k)
    (convex_coordinateRegion S q k)

end AutomaticContinuity.FiniteHalfspaceExhaustion
