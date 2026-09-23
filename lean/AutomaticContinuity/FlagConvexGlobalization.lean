import AutomaticContinuity.FlagConvexHomotopy
import AutomaticContinuity.FlagHomotopyPatching
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false

/-!
# Global continuous sections from a holomorphic germ on a convex compact

A holomorphic section admissible on a convex compact can replace any global
continuous admissible section near that compact. An admissible homotopy is
constructed on a convex open buffer and cut off there. The output equals the
given holomorphic germ near the compact; no approximation is assumed or proved.
-/

noncomputable section

namespace AutomaticContinuity.FlagConvexGlobalization

open Set Metric FlagTotalSpace

abbrev Pair := ℂ × ℂ

theorem exists_global_section {n : ℕ} {K U : Set (FinitePoint n)}
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (hU : IsOpen U) (hKU : K ⊆ U)
    (h g : FinitePoint n → Pair) (hh : Continuous h)
    (hadm : ∀ z, (z, h z) ∈ totalSet n)
    (hg : DifferentiableOn ℂ g U) (gadm : ∀ z ∈ K, (z, g z) ∈ totalSet n) :
    ∃ H : FinitePoint n → Pair, Continuous H ∧
      (∀ z, (z, H z) ∈ totalSet n) ∧
      ∃ V : Set (FinitePoint n), IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
        EqOn H g V ∧ DifferentiableOn ℂ H V := by
  let O := U ∩ (fun z => (z, g z)) ⁻¹' totalSet n
  have hO : IsOpen O :=
    (continuousOn_id.prodMk hg.continuousOn).isOpen_inter_preimage hU (isOpen_totalSet n)
  have hKO : K ⊆ O := fun z hz => ⟨hKU hz, gadm z hz⟩
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_thickening_subset_open hO hKO
  let W := thickening δ K
  have hKW : K ⊆ W := self_subset_thickening hδ K
  have hWU : W ⊆ U := fun z hz => (hδO hz).1
  obtain ⟨F, hFcont, hFzero, hFone, hFadm⟩ :=
    FlagConvexHomotopy.exists_ambient_homotopy (hKconv.thickening δ)
      (hKne.mono hKW) h g hh.continuousOn (hg.continuousOn.mono hWU)
      (fun z _ => hadm z) (fun z hz => (hδO hz).2)
  obtain ⟨H, hHcont, hHadm, _, _, V, hV, hKV, hVWU, hHeq, hHhol⟩ :=
    FlagHomotopyPatching.exists_patch (A := ∅) hK isOpen_thickening hU hKW hKU
      h g F hh hadm hFcont hFzero hFone hFadm hg (show (0 : ℝ) < 1 by norm_num)
      (by simp)
  exact ⟨H, hHcont, hHadm, V, hV, hKV, hVWU.trans inter_subset_right, hHeq, hHhol⟩

/-- Approximation on a smaller set transfers unchanged because globalization
agrees exactly with the chosen germ throughout the larger compact. -/
theorem exists_global_section_approx {n : ℕ} {K L U : Set (FinitePoint n)}
    (hL : IsCompact L) (hLconv : Convex ℝ L) (hLne : L.Nonempty)
    (hU : IsOpen U) (hLU : L ⊆ U) (hKL : K ⊆ L)
    (h g : FinitePoint n → Pair) (hh : Continuous h)
    (hadm : ∀ z, (z, h z) ∈ totalSet n)
    (hg : DifferentiableOn ℂ g U) (gadm : ∀ z ∈ L, (z, g z) ∈ totalSet n)
    {ε : ℝ} (hclose : ∀ z ∈ K, euclideanPairNorm (g z - h z) < ε) :
    ∃ H : FinitePoint n → Pair, Continuous H ∧
      (∀ z, (z, H z) ∈ totalSet n) ∧
      (∀ z ∈ K, euclideanPairNorm (H z - h z) < ε) ∧
      ∃ V : Set (FinitePoint n), IsOpen V ∧ L ⊆ V ∧ DifferentiableOn ℂ H V := by
  obtain ⟨H, hHcont, hHadm, V, hV, hLV, _, hHeq, hHhol⟩ :=
    exists_global_section hL hLconv hLne hU hLU h g hh hadm hg gadm
  refine ⟨H, hHcont, hHadm, ?_, V, hV, hLV, hHhol⟩
  intro z hz
  rw [hHeq (hLV (hKL hz))]
  exact hclose z hz

end AutomaticContinuity.FlagConvexGlobalization
