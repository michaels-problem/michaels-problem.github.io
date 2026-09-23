import AutomaticContinuity.FlagSectionPatching
import Mathlib.Topology.UrysohnsLemma

set_option autoImplicit false

/-!
# Global patching from an explicitly supplied admissible local homotopy

A continuous cutoff is supported inside the homotopy's open base domain
and equals one on an open neighbourhood of the target compact set. Evaluating
the homotopy at the cutoff time and using the old section outside the domain
gives a globally continuous admissible section. Holomorphy is inherited only
where the cutoff is identically one. The local admissible homotopy is an
explicit hypothesis; this file proves no analytic deformation or gluing theorem.
-/

noncomputable section

namespace AutomaticContinuity.FlagHomotopyPatching

open Set Filter FlagTotalSpace
open scoped Topology

abbrev Pair := ℂ × ℂ

def patch {X : Type*} (W : Set X) (h : X → Pair) (H : ℝ × X → Pair)
    (ρ : X → ℝ) (x : X) : Pair := by
  classical
  exact if x ∈ W then H (ρ x, x) else h x

theorem patch_of_mem {X : Type*} {W : Set X} (h : X → Pair) (H : ℝ × X → Pair)
    (ρ : X → ℝ) {x : X} (hx : x ∈ W) : patch W h H ρ x = H (ρ x, x) := by
  simp [patch, hx]

theorem patch_of_notMem {X : Type*} {W : Set X} (h : X → Pair) (H : ℝ × X → Pair)
    (ρ : X → ℝ) {x : X} (hx : x ∉ W) : patch W h H ρ x = h x := by
  simp [patch, hx]

theorem patch_of_zero {X : Type*} {W : Set X} (h : X → Pair) (H : ℝ × X → Pair)
    (ρ : X → ℝ) (hzero : ∀ x ∈ W, H (0, x) = h x) {x : X} (hx : ρ x = 0) :
    patch W h H ρ x = h x := by
  by_cases hw : x ∈ W
  · rw [patch_of_mem h H ρ hw, hx, hzero x hw]
  · exact patch_of_notMem h H ρ hw

theorem continuous_patch {X : Type*} [TopologicalSpace X] {W : Set X}
    (hW : IsOpen W) {h : X → Pair} {H : ℝ × X → Pair} {ρ : X → ℝ}
    (hh : Continuous h) (hH : ContinuousOn H (Icc 0 1 ×ˢ W)) (hρ : Continuous ρ)
    (hρrange : ∀ x, ρ x ∈ Icc 0 1) (hsupp : tsupport ρ ⊆ W)
    (hzero : ∀ x ∈ W, H (0, x) = h x) : Continuous (patch W h H ρ) := by
  have hlocal : ContinuousOn (fun x => H (ρ x, x)) W :=
    hH.comp (hρ.prodMk continuous_id).continuousOn (fun x hx => ⟨hρrange x, hx⟩)
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ W
  · apply (hlocal.continuousAt (hW.mem_nhds hx)).congr_of_eventuallyEq
    filter_upwards [hW.mem_nhds hx] with y hy
    exact patch_of_mem h H ρ hy
  · have hxS : x ∉ tsupport ρ := fun hxS => hx (hsupp hxS)
    apply hh.continuousAt.congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport ρ).isOpen_compl.mem_nhds hxS] with y hy
    exact patch_of_zero h H ρ hzero (image_eq_zero_of_notMem_tsupport hy)

theorem admissible_patch {n : ℕ} {W : Set (FinitePoint n)}
    {h : FinitePoint n → Pair} {H : ℝ × FinitePoint n → Pair} {ρ : FinitePoint n → ℝ}
    (hh : ∀ x, (x, h x) ∈ totalSet n)
    (hH : ∀ t ∈ Icc 0 1, ∀ x ∈ W, (x, H (t, x)) ∈ totalSet n)
    (hρ : ∀ x, ρ x ∈ Icc 0 1) : ∀ x, (x, patch W h H ρ x) ∈ totalSet n := by
  intro x
  by_cases hx : x ∈ W
  · rw [patch_of_mem h H ρ hx]
    exact hH (ρ x) (hρ x) x hx
  · rw [patch_of_notMem h H ρ hx]
    exact hh x

theorem error_patch {n : ℕ} {W A : Set (FinitePoint n)}
    {h : FinitePoint n → Pair} {H : ℝ × FinitePoint n → Pair} {ρ : FinitePoint n → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hρ : ∀ x, ρ x ∈ Icc 0 1)
    (hclose : ∀ t ∈ Icc 0 1, ∀ x ∈ A ∩ W, euclideanPairNorm (H (t, x) - h x) < ε) :
    ∀ x ∈ A, euclideanPairNorm (patch W h H ρ x - h x) < ε := by
  intro x hx
  by_cases hw : x ∈ W
  · rw [patch_of_mem h H ρ hw]
    exact hclose (ρ x) (hρ x) x ⟨hx, hw⟩
  · rw [patch_of_notMem h H ρ hw, sub_self, euclideanPairNorm_zero]
    exact hε

/-- A supplied admissible local homotopy gives a genuine global continuous
patch. The cutoff is one on an actual open neighbourhood of the compact, so
holomorphy there is inherited from its endpoint. No analytic homotopy or
approximation is constructed by this topological statement. -/
theorem exists_patch {n : ℕ} {C W V A : Set (FinitePoint n)}
    (hC : IsCompact C) (hW : IsOpen W) (hV : IsOpen V) (hCW : C ⊆ W) (hCV : C ⊆ V)
    (h g : FinitePoint n → Pair) (H : ℝ × FinitePoint n → Pair)
    (hh : Continuous h) (hadm : ∀ x, (x, h x) ∈ totalSet n)
    (hH : ContinuousOn H (Icc 0 1 ×ˢ W))
    (hH0 : ∀ x ∈ W, H (0, x) = h x) (hH1 : ∀ x ∈ W, H (1, x) = g x)
    (hHadm : ∀ t ∈ Icc 0 1, ∀ x ∈ W, (x, H (t, x)) ∈ totalSet n)
    (hg : DifferentiableOn ℂ g V) {ε : ℝ} (hε : 0 < ε)
    (hclose : ∀ t ∈ Icc 0 1, ∀ x ∈ A ∩ W, euclideanPairNorm (H (t, x) - h x) < ε) :
    ∃ f : FinitePoint n → Pair, Continuous f ∧ (∀ x, (x, f x) ∈ totalSet n) ∧
      (∀ x ∉ W, f x = h x) ∧
      (∀ x ∈ A, euclideanPairNorm (f x - h x) < ε) ∧
      ∃ O : Set (FinitePoint n), IsOpen O ∧ C ⊆ O ∧ O ⊆ W ∩ V ∧
        EqOn f g O ∧ DifferentiableOn ℂ f O := by
  obtain ⟨K, hK, _hKclosed, hCK, hKWV⟩ :=
    exists_compact_closed_between hC (hW.inter hV) (subset_inter hCW hCV)
  obtain ⟨ρ, hρone, _hρcompact, hρsupport, hρrange⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK (hW.inter hV) hKWV
  let f := patch W h H ρ
  have hfg : EqOn f g (interior K) := by
    intro x hx
    have hxK := interior_subset hx
    have hxW := (hKWV hxK).1
    change patch W h H ρ x = g x
    rw [patch_of_mem h H ρ hxW, hρone hxK, Pi.one_apply, hH1 x hxW]
  refine ⟨f, continuous_patch hW hh hH ρ.continuous hρrange
      (hρsupport.trans inter_subset_left) hH0,
    admissible_patch hadm hHadm hρrange, ?_, error_patch hε hρrange hclose,
    interior K, isOpen_interior, hCK, interior_subset.trans hKWV, hfg, ?_⟩
  · intro x hx
    exact patch_of_notMem h H ρ hx
  · exact (hg.mono (interior_subset.trans (hKWV.trans inter_subset_right))).congr hfg

end AutomaticContinuity.FlagHomotopyPatching
