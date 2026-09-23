import AutomaticContinuity.FlagApproximationOpenness
import AutomaticContinuity.FlagApproximationTransfer

set_option autoImplicit false

/-! # Fixed buffered transfer data approximate every holomorphic parameter composition -/

noncomputable section

namespace AutomaticContinuity.FlagApproximationTransfer

open Set FlagTotalSpace FlagSectionApproximation

/-- The whole-target extending section, domains, inverse coordinates on the
buffered overlap, splitting norm, and target margins are fixed before the
arbitrary new parameter map and its approximation accuracy are selected. -/
theorem approximableCompositions_of_transfer_data {n : ℕ}
    {K L C A B U V W : Set (FinitePoint n)}
    (hK : IsCompact K) (hC : IsCompact C)
    (hA : IsOpen A) (hB : IsOpen B) (hV : IsOpen V)
    (hLAB : L ⊆ A ∪ B) (hKB : K ⊆ B) (hAU : A ⊆ U) (hBV : B ⊆ V)
    (hCV : C ⊆ V) (hWU : W ⊆ U) (hWV : W ⊆ V)
    (g θ : FinitePoint n → Pair) (G : FinitePoint n × Pair → Pair)
    (hg : DifferentiableOn ℂ g U) (hG : DifferentiableOn ℂ G (V ×ˢ univ))
    (hθ : ContinuousOn θ C) (hθeq : ∀ z ∈ C, G (z, θ z) = g z)
    {δA δB M : ℝ} (hδA : 0 < δA) (hδB : 0 < δB) (hM : 0 < M)
    (hmarginA : ∀ z ∈ A, ∀ e : Pair, euclideanPairNorm e ≤ δA →
      (z, g z + e) ∈ totalSet n)
    (hmarginB : ∀ z ∈ B, ∀ t e : Pair, euclideanPairNorm e ≤ δB →
      (z, G (z, t) + e) ∈ totalSet n)
    (happrox : ∀ φ : FinitePoint n → Pair, HolomorphicNear K φ →
      ParameterApproximation K C φ θ)
    (hsplit : BoundedSplitting A B W C M) : ApproximableCompositions K L G := by
  intro φ hφ
  obtain ⟨O, _hO, hKO, hφO⟩ := hφ
  exact approximable_of_transfer_data hK hC hA hB hV hLAB hKB hAU hBV hCV hWU hWV
    g (fun z => G (z, φ z)) φ θ G hg hG (hφO.continuousOn.mono hKO) hθ
    (fun _ _ => rfl) hθeq hδA hδB hM hmarginA hmarginB
    (happrox φ ⟨O, _hO, hKO, hφO⟩) hsplit

end AutomaticContinuity.FlagApproximationTransfer
