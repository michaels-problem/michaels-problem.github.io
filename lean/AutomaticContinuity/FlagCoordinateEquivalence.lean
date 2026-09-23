import AutomaticContinuity.FlagPolynomialSeparation

set_option autoImplicit false

/-!
# Ordinary complex coordinates for the compact forbidden graph

The source coordinates together with the two target coordinates form an actual
complex continuous linear equivalence.  The generalized polynomial hull used
for the product presentation is exactly the usual, identity-coordinate hull
after this equivalence.  Thus the geometric result concerns an ordinary compact
polynomially convex subset of a finite-dimensional complex coordinate space.
-/

noncomputable section

namespace AutomaticContinuity.FlagPolynomialSeparation

theorem continuous_coordinates (n : ℕ) : Continuous (@coordinates n) := by
  apply continuous_pi
  intro i
  rcases i with j | b
  · exact (continuous_apply j).comp continuous_fst
  · cases b
    · exact continuous_fst.comp continuous_snd
    · exact continuous_snd.comp continuous_snd

/-- The full coordinate map, with its genuine product-topology inverse. -/
def coordinatesContinuousLinearEquiv (n : ℕ) : Point n ≃L[ℂ] (Variables n → ℂ) where
  toLinearEquiv := coordinatesLinearEquiv n
  continuous_toFun := continuous_coordinates n
  continuous_invFun :=
    (continuous_pi fun j => continuous_apply (Sum.inl j)).prodMk
      ((continuous_apply (Sum.inr false)).prodMk (continuous_apply (Sum.inr true)))

@[simp] theorem coordinatesContinuousLinearEquiv_apply (n : ℕ) (p : Point n) :
    coordinatesContinuousLinearEquiv n p = coordinates p := rfl

@[simp] theorem coordinatesContinuousLinearEquiv_symm_apply (n : ℕ)
    (f : Variables n → ℂ) :
    (coordinatesContinuousLinearEquiv n).symm f =
      ((fun j => f (Sum.inl j)), (f (Sum.inr false), f (Sum.inr true))) := rfl

/-- Membership in the conventional polynomial hull is precisely membership in
the product-coordinate hull before the coordinate equivalence. -/
theorem coordinates_mem_standardHull_iff {n : ℕ} (K : Set (Point n)) (p : Point n) :
    coordinates p ∈ polynomialHullOf (fun z : Variables n → ℂ => z)
      (coordinates '' K) ↔ p ∈ polynomialHullOf coordinates K := by
  constructor
  · intro hp P C hC
    apply hp P C
    rintro _ ⟨q, hq, rfl⟩
    exact hC q hq
  · intro hp P C hC
    exact hp P C (fun q hq => hC (coordinates q) ⟨q, hq, rfl⟩)

/-- The generalized hull is transported to the usual hull in the complete
finite set of complex coordinates; no restricted polynomial class is used. -/
theorem coordinates_image_polynomialHull {n : ℕ} (K : Set (Point n)) :
    coordinates '' polynomialHullOf coordinates K =
      polynomialHullOf (fun z : Variables n → ℂ => z) (coordinates '' K) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact (coordinates_mem_standardHull_iff K p).mpr hp
  · intro z hz
    obtain ⟨p, rfl⟩ := (coordinatesLinearEquiv n).surjective z
    exact ⟨p, (coordinates_mem_standardHull_iff K p).mp hz, rfl⟩

theorem isPolynomiallyConvex_coordinates_image_iff {n : ℕ} (K : Set (Point n)) :
    IsPolynomiallyConvexOf (fun z : Variables n → ℂ => z) (coordinates '' K) ↔
      IsPolynomiallyConvexOf coordinates K := by
  constructor
  · intro h
    apply Set.Subset.antisymm
    · intro p hp
      have hmem : coordinates p ∈ coordinates '' K := by
        rw [← h]
        exact (coordinates_mem_standardHull_iff K p).mpr hp
      obtain ⟨q, hq, hqp⟩ := hmem
      have heq : q = p := (coordinatesLinearEquiv n).injective hqp
      simpa only [heq] using hq
    · exact subset_polynomialHullOf coordinates K
  · intro h
    change polynomialHullOf (fun z : Variables n → ℂ => z) (coordinates '' K) = _
    rw [← coordinates_image_polynomialHull, h]

theorem isCompact_coordinates_compactForbiddenGraph (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (coordinates '' FlagTotalSpace.compactForbiddenGraph n R) :=
  (FlagTotalSpace.isCompact_compactForbiddenGraph n hR).image (continuous_coordinates n)

/-- The forbidden graph in ordinary `n + 2` complex coordinates is polynomially
convex, with the standard identity-coordinate definition. -/
theorem isPolynomiallyConvex_coordinates_compactForbiddenGraph (n : ℕ) {R : ℝ}
    (hR : 0 ≤ R) :
    IsPolynomiallyConvexOf (fun z : Variables n → ℂ => z)
      (coordinates '' FlagTotalSpace.compactForbiddenGraph n R) :=
  (isPolynomiallyConvex_coordinates_image_iff _).mpr
    (isPolynomiallyConvex_compactForbiddenGraph n hR)

end AutomaticContinuity.FlagPolynomialSeparation
