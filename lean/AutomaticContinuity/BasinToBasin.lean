import AutomaticContinuity.BasinGlobalization

set_option autoImplicit false

/-!
# Globalizing a local conjugacy between its two entry basins

A genuine local conjugacy gives a homeomorphism between the source and target
entry basins. There is no assumption that the target basin is the whole target
space. Under the holomorphic hypotheses both ambient representatives are
holomorphic on their respective open basins.
-/

noncomputable section

namespace AutomaticContinuity.BasinGlobalization.LocalConjugacy

open Set

section Topological

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {T : E ≃ₜ E} {A : F ≃ₜ F} {U : Set E} {V : Set F}
    (D : LocalConjugacy T A U V)

include D in
/-- Forward invariance of the local target follows from local conjugacy. -/
theorem target_forward_invariant : MapsTo A V V := by
  intro y hy
  have hc := D.conjugacy (D.invFun y) (D.invMapsTo hy)
  rw [D.right_inv y hy] at hc
  rw [← hc]
  exact D.mapsTo (D.forward_invariant (D.invMapsTo hy))

/-- Reverse the local conjugacy, including its derived invariance and equation. -/
def symm : LocalConjugacy A T V U where
  toFun := D.invFun
  invFun := D.toFun
  source_open := D.target_open
  target_open := D.source_open
  mapsTo := D.invMapsTo
  invMapsTo := D.mapsTo
  left_inv := D.right_inv
  right_inv := D.left_inv
  continuousOn_toFun := D.continuousOn_invFun
  continuousOn_invFun := D.continuousOn_toFun
  forward_invariant := D.target_forward_invariant
  conjugacy := by
    intro y hy
    have hc := D.conjugacy (D.invFun y) (D.invMapsTo hy)
    rw [D.right_inv y hy] at hc
    rw [← hc]
    exact D.left_inv _ (D.forward_invariant (D.invMapsTo hy))

/-- The entry-time relation reverses without changing the entry time. -/
theorem related_symm_iff (x : E) (y : F) : D.symm.Related y x ↔ D.Related x y := by
  constructor
  · rintro ⟨m, hm, he⟩
    change D.invFun ((A ^ m) y) = (T ^ m) x at he
    have hmx : (T ^ m) x ∈ U := he ▸ D.invMapsTo hm
    refine ⟨m, hmx, ?_⟩
    rw [← he, D.right_inv _ hm]
  · rintro ⟨m, hm, he⟩
    have hmy : (A ^ m) y ∈ V := he ▸ D.mapsTo hm
    refine ⟨m, hmy, ?_⟩
    change D.invFun ((A ^ m) y) = (T ^ m) x
    rw [← he, D.left_inv _ hm]

theorem globalMap_mem_target_basin (x : basin T U) : D.globalMap x ∈ basin A V := by
  obtain ⟨m, hm, he⟩ := D.related_globalMap x
  exact ⟨m, he ▸ D.mapsTo hm⟩

/-- The global map with its target restricted to the actual target basin. -/
def basinMap (x : basin T U) : basin A V :=
  ⟨D.globalMap x, D.globalMap_mem_target_basin x⟩

@[simp] theorem coe_basinMap (x : basin T U) : (D.basinMap x : F) = D.globalMap x := rfl

theorem symm_basinMap_basinMap (x : basin T U) : D.symm.basinMap (D.basinMap x) = x := by
  apply Subtype.ext
  exact D.related_source_unique
    ((D.related_symm_iff _ _).mp (D.symm.related_globalMap (D.basinMap x)))
    (D.related_globalMap x)

theorem basinMap_symm_basinMap (y : basin A V) : D.basinMap (D.symm.basinMap y) = y := by
  apply Subtype.ext
  exact D.related_unique (D.related_globalMap (D.symm.basinMap y))
    ((D.related_symm_iff _ _).mp (D.symm.related_globalMap y))

/-- The actual basin-to-basin homeomorphism requires no target-exhaustion
hypothesis. Its two maps are the two entry-time extensions. -/
def basinHomeomorph : basin T U ≃ₜ basin A V where
  toFun := D.basinMap
  invFun := D.symm.basinMap
  left_inv := D.symm_basinMap_basinMap
  right_inv := D.basinMap_symm_basinMap
  continuous_toFun := D.continuous_globalMap.subtype_mk _
  continuous_invFun := D.symm.continuous_globalMap.subtype_mk _

@[simp] theorem coe_basinHomeomorph (x : basin T U) :
    (D.basinHomeomorph x : F) = D.globalMap x := rfl

@[simp] theorem coe_basinHomeomorph_symm (y : basin A V) :
    (D.basinHomeomorph.symm y : E) = D.symm.globalMap y := rfl

end Topological

section Holomorphic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {T : E ≃ₜ E} {A : F ≃ₜ F} {U : Set E} {V : Set F}
    (D : LocalConjugacy T A U V)

/-- Holomorphic globalization in both directions onto the two actual basins.
The maps are represented by ambient functions so their complex derivatives
are stated on open subsets of the original complex normed spaces. -/
theorem exists_biholomorphic_basins
    (hT : Differentiable ℂ (T : E → E))
    (hTinv : Differentiable ℂ (T.symm : E → E))
    (hA : Differentiable ℂ (A : F → F))
    (hAinv : Differentiable ℂ (A.symm : F → F))
    (hh : DifferentiableOn ℂ D.toFun U)
    (hk : DifferentiableOn ℂ D.invFun V) :
    ∃ H : basin T U ≃ₜ basin A V, ∃ h : E → F, ∃ k : F → E,
      DifferentiableOn ℂ h (basin T U) ∧
      DifferentiableOn ℂ k (basin A V) ∧
      (∀ x : basin T U, (H x : F) = h x) ∧
      (∀ y : basin A V, (H.symm y : E) = k y) ∧
      (∀ x ∈ U, h x = D.toFun x) ∧
      (∀ y ∈ V, k y = D.invFun y) := by
  refine ⟨D.basinHomeomorph, D.globalExtension, D.symm.globalExtension,
    D.differentiableOn_globalExtension hT hAinv hh,
    D.symm.differentiableOn_globalExtension hA hTinv hk, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (D.globalExtension_of_mem x.property).symm
  · intro y
    exact (D.symm.globalExtension_of_mem y.property).symm
  · exact fun x hx => D.globalExtension_eq_local hx
  · exact fun y hy => D.symm.globalExtension_eq_local hy

end Holomorphic

end AutomaticContinuity.BasinGlobalization.LocalConjugacy
