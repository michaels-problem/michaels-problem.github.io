import AutomaticContinuity.CircumscribedCoordinatePolygons

set_option autoImplicit false

/-! # The finite cut chain is an actual product of compact convex planar sets -/

noncomputable section

namespace AutomaticContinuity.FiniteHalfspaceExhaustion

open Set

def IsCompactConvexProduct {n : ℕ} (L : Set (FinitePoint n)) : Prop :=
  ∃ C : Fin n → Set ℂ, (∀ k, IsCompact (C k) ∧ Convex ℝ (C k)) ∧
    L = Set.pi univ C

theorem cutChain_eq_pi_coordinate_image {n N : ℕ} (S : ℝ)
    (q : Fin N → CoordinateCut n) (j : ℕ) :
    cutChain (closedBox n S) q j =
      Set.pi univ (fun k : Fin n => (fun z : FinitePoint n => z k) ''
        cutChain (closedBox n S) q j) := by
  ext z
  constructor
  · intro hz k _
    exact ⟨z, hz, rfl⟩
  · intro hz
    refine ⟨?_, mem_iInter₂.mpr ?_⟩
    · intro k
      obtain ⟨w, hw, hwk⟩ := hz k (mem_univ k)
      simpa only [hwk] using hw.1 k
    · intro i hi
      obtain ⟨w, hw, hwk⟩ := hz (q i).coordinate (mem_univ _)
      have hwi := mem_iInter₂.mp hw.2 i hi
      change ((q i).coefficient * z (q i).coordinate).re ≤ (q i).bound
      change ((q i).coefficient * w (q i).coordinate).re ≤ (q i).bound at hwi
      simpa only [hwk] using hwi

theorem isCompactConvexProduct_cutChain {n N : ℕ} {S : ℝ} (hS : 0 ≤ S)
    (q : Fin N → CoordinateCut n) (j : ℕ) :
    IsCompactConvexProduct (cutChain (closedBox n S) q j) := by
  refine ⟨fun k => (fun z : FinitePoint n => z k) '' cutChain (closedBox n S) q j,
    ?_, cutChain_eq_pi_coordinate_image S q j⟩
  intro k
  exact ⟨(isCompact_cutChain (isCompact_closedBox n hS) q j).image (continuous_apply k),
    (convex_cutChain (convex_closedBox n S) q j).linear_image (LinearMap.proj k)⟩

end AutomaticContinuity.FiniteHalfspaceExhaustion
