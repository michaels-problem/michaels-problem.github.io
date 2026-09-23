import AutomaticContinuity.CoordinateProductGeometry
import AutomaticContinuity.FlagConvexGlobalization
import AutomaticContinuity.FlagSectionApproximation
import AutomaticContinuity.FlagUnitExtension

set_option autoImplicit false

/-!
# Reduction of the exact flag approximation theorem to one coordinate half-cut

The premise is a single approximation theorem on products of compact convex
planar sets. The finite coordinate-cut chain, its error accumulation, global
continuous patching and the final exhaustion are proved here or in imported
checked modules. This file does not assert the analytic half-cut premise.
-/

noncomputable section

namespace AutomaticContinuity

open Set FlagTotalSpace FiniteHalfspaceExhaustion FlagSectionApproximation

def FiniteFlagHalfCutApproximationStatement : Prop :=
  ∀ (n : ℕ) (L : Set (FinitePoint n)), IsCompactConvexProduct L →
    ∀ (q : CoordinateCut n) (h : FinitePoint n → ℂ × ℂ)
      (U : Set (FinitePoint n)), IsOpen U → L ∩ q.halfspace ⊆ U →
      DifferentiableOn ℂ h U →
      (∀ z ∈ L ∩ q.halfspace, (z, h z) ∈ totalSet n) →
      Approximable (L ∩ q.halfspace) L h

namespace FiniteFlagCutReduction

theorem approximable_along_chain (hCut : FiniteFlagHalfCutApproximationStatement)
    {n N : ℕ} {S : ℝ} (hS : 0 ≤ S) (q : Fin N → CoordinateCut n)
    (h : FinitePoint n → ℂ × ℂ) {U : Set (FinitePoint n)}
    (hU : IsOpen U) (hK0U : cutChain (closedBox n S) q 0 ⊆ U)
    (hh : DifferentiableOn ℂ h U) (hadm : ∀ z ∈ U, (z, h z) ∈ totalSet n) :
    Approximable (cutChain (closedBox n S) q 0) (closedBox n S) h := by
  have hall : ∀ m : ℕ, m ≤ N →
      Approximable (cutChain (closedBox n S) q 0) (cutChain (closedBox n S) q m) h := by
    intro m
    induction m with
    | zero =>
      intro _
      exact approximable_of_extension h hU hK0U hh hadm
    | succ m ih =>
      intro hm ε hε
      obtain ⟨g, V, hV, hKmV, hg, hgadm, hgh⟩ :=
        ih (by omega) (ε/2) (half_pos hε)
      let i : Fin N := ⟨m, by omega⟩
      have hcut := hCut n (cutChain (closedBox n S) q (m+1))
        (isCompactConvexProduct_cutChain hS q (m+1)) (q i) g V hV
      rw [← cutChain_step (closedBox n S) q i] at hcut
      have hgapp := hcut hKmV hg (fun z hz => hgadm z (hKmV hz))
      obtain ⟨f, W, hW, hKmW, hf, hfadm, hfg⟩ := hgapp (ε/2) (half_pos hε)
      refine ⟨f, W, hW, hKmW, hf, hfadm, ?_⟩
      intro z hz
      have hzm := cutChain_mono (closedBox n S) q (Nat.zero_le m) hz
      have htri := euclideanPairNorm_add_le (f z-g z) (g z-h z)
      rw [sub_add_sub_cancel] at htri
      exact htri.trans_lt (by linarith [hfg z hzm, hgh z hz])
  simpa only [cutChain_final] using hall N le_rfl

theorem unitExtension_of_halfCut (hCut : FiniteFlagHalfCutApproximationStatement) :
    FiniteFlagUnitExtensionStatement := by
  intro n _hn R hR h hc hh hb ε hε
  obtain ⟨U, hU, hKU, hh⟩ := hh
  have hadm : ∀ z, (z, h z) ∈ totalSet n := fun z =>
    mem_totalSet_iff.mpr (fun k hk hkn hzk => hb k hk hkn z hzk)
  obtain ⟨N, q, hK0, hK0U, hKN, _, _, _⟩ :=
    exists_polydisc_enlargement_chain hR (lt_add_one R) hU hKU
  have hS : 0 ≤ R+1 := by linarith
  obtain ⟨g, V, hV, hLV, hg, hgadm, hclose⟩ :=
    approximable_along_chain hCut hS q h hU hK0U hh (fun z _ => hadm z) ε hε
  have hKL : polydisc n R ⊆ closedBox n (R+1) :=
    (FlagLocalExtension.polydisc_mono n (by linarith : R ≤ R+1)).trans
      (polydisc_subset_closedBox n (R+1))
  have hLne : (closedBox n (R+1)).Nonempty :=
    ⟨0, fun j => by simp [hS]⟩
  obtain ⟨H, hHc, hHadm, hHclose, W, hW, hLW, hHhol⟩ :=
    FlagConvexGlobalization.exists_global_section_approx
      (isCompact_closedBox n hS) (convex_closedBox n (R+1)) hLne hV hLV hKL
      h g hc hadm hg (fun z hz => hgadm z (hLV hz))
      (fun z hz => hclose z (interior_subset (hK0 hz)))
  refine ⟨H, hHc, ⟨W, hW, ?_, hHhol⟩, ?_, hHclose⟩
  · exact (polydisc_subset_closedBox n (R+1)).trans hLW
  · intro k hk hkn z hzk
    exact mem_totalSet_iff.mp (hHadm z) k hk hkn hzk

theorem finiteFlagApproximation_of_halfCut (hCut : FiniteFlagHalfCutApproximationStatement) :
    FiniteFlagApproximationStatement :=
  finiteFlagUnitExtension_iff_approximation.mp (unitExtension_of_halfCut hCut)

end FiniteFlagCutReduction
end AutomaticContinuity
