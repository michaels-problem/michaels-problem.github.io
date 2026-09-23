import AutomaticContinuity.PolynomialResolventContinuation
import AutomaticContinuity.PlanarEscapeRays

set_option autoImplicit false

/-! # Polynomial convexity of products of planar convex sets and separated caps

The proof uses explicit escape rays and the spectrum of the actual closed
polynomial function algebra. No approximation theorem is assumed.
-/

noncomputable section

namespace AutomaticContinuity.PolynomialFunctionAlgebra

open Set

variable {σ : Type*} (K : Set (σ → ℂ)) [CompactSpace K]

theorem isPolynomiallyConvex_of_product_escape (C : σ → Set ℂ)
    (hK : ∀ z, z ∈ K ↔ ∀ j, z j ∈ C j)
    (hescape : ∀ j ζ, ζ ∉ C j →
      ∃ T : Set ℂ, IsPreconnected T ∧ ζ ∈ T ∧
        T ⊆ (C j)ᶜ ∧ ¬ Bornology.IsBounded T) :
    IsPolynomiallyConvexOf (fun z : σ → ℂ => z) K := by
  apply (isPolynomiallyConvexOf_iff_separation _ _).mpr
  intro z hz
  have hex : ∃ j, z j ∉ C j := by
    by_contra! h
    exact hz ((hK z).mpr h)
  obtain ⟨j, hj⟩ := hex
  obtain ⟨T, hT, hzT, hTC, hTb⟩ := hescape j (z j) hj
  have havoid : T ⊆ (coordinateRange K j)ᶜ := by
    rintro ζ hζ ⟨x, rfl⟩
    exact hTC hζ ((hK x.val).mp x.property j)
  have hunit := coordinateDenominator_isUnit_of_unbounded_connected K j (z j) T
    hT hzT havoid hTb
  obtain ⟨q, hq, hqz⟩ := exists_coordinate_separator_of_isUnit K j (z j) hunit
    (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨q, 1 / 2, ?_, ?_⟩
  · intro x hx
    exact (hq ⟨x, hx⟩).le
  · rw [hqz z rfl, norm_one]
    norm_num

theorem isPolynomiallyConvex_of_convex_product (C : σ → Set ℂ)
    (hK : ∀ z, z ∈ K ↔ ∀ j, z j ∈ C j) (hC : ∀ j, Convex ℝ (C j)) :
    IsPolynomiallyConvexOf (fun z : σ → ℂ => z) K :=
  isPolynomiallyConvex_of_product_escape K C hK fun j _ hz =>
    PlanarEscapeRays.exists_escape_convex (hC j) hz

theorem isPolynomiallyConvex_of_product_separatedCaps [DecidableEq σ]
    (C : σ → Set ℂ) (j : σ) {c d : ℝ} (hcd : c < d)
    (hK : ∀ z, z ∈ K ↔
      z j ∈ PlanarEscapeRays.separatedCaps (C j) c d ∧
        ∀ i, i ≠ j → z i ∈ C i)
    (hC : ∀ i, Convex ℝ (C i)) :
    IsPolynomiallyConvexOf (fun z : σ → ℂ => z) K := by
  let D : σ → Set ℂ := fun i =>
    if i = j then PlanarEscapeRays.separatedCaps (C i) c d else C i
  apply isPolynomiallyConvex_of_product_escape K D
  · intro z
    rw [hK]
    constructor
    · rintro ⟨hj, hi⟩ i
      by_cases hij : i = j
      · subst i
        simpa [D] using hj
      · simpa [D, hij] using hi i hij
    · intro h
      refine ⟨?_, ?_⟩
      · simpa [D] using h j
      · intro i hij
        simpa [D, hij] using h i
  · intro i ζ hζ
    by_cases hij : i = j
    · subst i
      simpa [D] using PlanarEscapeRays.exists_escape_separatedCaps (hC j) hcd
        (show ζ ∉ PlanarEscapeRays.separatedCaps (C j) c d by simpa [D] using hζ)
    · simpa [D, hij] using PlanarEscapeRays.exists_escape_convex (hC i)
        (show ζ ∉ C i by simpa [D, hij] using hζ)

end AutomaticContinuity.PolynomialFunctionAlgebra
