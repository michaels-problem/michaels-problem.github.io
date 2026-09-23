import AutomaticContinuity.ConvexFlagApproximationPrinciple
import AutomaticContinuity.CoordinateProductGeometry

set_option autoImplicit false

/-! # The empty and unchanged approximation cases -/

noncomputable section

namespace AutomaticContinuity.FlagSectionApproximation

open Set FlagTotalSpace

theorem approximable_empty {n : ℕ} (L : Set (FinitePoint n)) (h : FinitePoint n → Pair) :
    Approximable ∅ L h := by
  apply (approximable_largeValue ∅ L).congr
  intro z hz
  exact False.elim hz

theorem approximable_self_of_holomorphicNear {n : ℕ} {K : Set (FinitePoint n)}
    (h : FinitePoint n → Pair) (hhol : HolomorphicNear K h)
    (hadm : ∀ z ∈ K, (z,h z) ∈ totalSet n) : Approximable K K h := by
  obtain ⟨U,hU,hKU,hh⟩ := hhol
  let V := U ∩ (fun z => (z,h z)) ⁻¹' totalSet n
  have hV : IsOpen V :=
    (continuousOn_id.prodMk hh.continuousOn).isOpen_inter_preimage hU (isOpen_totalSet n)
  exact approximable_of_extension h hV (fun z hz => ⟨hKU hz,hadm z hz⟩)
    (hh.mono inter_subset_left) (fun _ hz => hz.2)

end AutomaticContinuity.FlagSectionApproximation

namespace AutomaticContinuity.FiniteHalfspaceExhaustion

open Set

theorem IsCompactConvexProduct.isCompact {n : ℕ} {L : Set (FinitePoint n)}
    (hL : IsCompactConvexProduct L) : IsCompact L := by
  obtain ⟨C,hC,rfl⟩ := hL
  convert isCompact_pi_infinite (fun i => (hC i).1) using 1
  ext x
  simp [Set.mem_pi]

theorem IsCompactConvexProduct.convex {n : ℕ} {L : Set (FinitePoint n)}
    (hL : IsCompactConvexProduct L) : Convex ℝ L := by
  obtain ⟨C,hC,rfl⟩ := hL
  exact convex_pi (fun i _ => (hC i).2)

end AutomaticContinuity.FiniteHalfspaceExhaustion
