import AutomaticContinuity.BasinGlobalization

/-!
# Basin exclusion and translation of an exterior fixed point

A forward-invariant forbidden set cannot meet the entry basin of a disjoint
local domain. Translating a fixed point to zero preserves the actual basin and
its holomorphic parameterization. No basin parameterization is assumed to
follow merely from attraction.
-/

noncomputable section

namespace AutomaticContinuity.BasinAvoidance

open Set Metric

universe u

section Topological

variable {E : Type u} [TopologicalSpace E]

/-- Forward invariance alone excludes the forbidden set from the full entry
basin of a disjoint local domain. Closedness is unnecessary for this implication. -/
theorem basin_subset_compl (T : E ≃ₜ E) {K U : Set E}
    (hK : MapsTo T K K) (hUK : Disjoint U K) :
    BasinGlobalization.basin T U ⊆ Kᶜ := by
  rintro x ⟨m, hm⟩ hx
  exact Set.disjoint_left.mp hUK hm
    (BasinGlobalization.mapsTo_pow_of_mapsTo T hK m hx)

theorem disjoint_basin (T : E ≃ₜ E) {K U : Set E}
    (hK : MapsTo T K K) (hUK : Disjoint U K) :
    Disjoint (BasinGlobalization.basin T U) K :=
  Set.disjoint_left.mpr fun _ hx hKx => basin_subset_compl T hK hUK hx hKx

end Topological

section Translation

variable {E : Type u} [NormedAddCommGroup E]

/-- An exterior point of a closed forward-invariant set has a positive radius
such that every smaller ball has its whole entry basin outside that set. -/
theorem exists_radius_basin_subset_compl (T : E ≃ₜ E) {K : Set E}
    (hclosed : IsClosed K) (hK : MapsTo T K K) {p : E} (hp : p ∉ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, r ≤ δ →
      BasinGlobalization.basin T (ball p r) ⊆ Kᶜ := by
  obtain ⟨δ, hδ, hδK⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hp)
  refine ⟨δ, hδ, fun r hr => basin_subset_compl T hK ?_⟩
  apply Set.disjoint_left.mpr
  intro x hx hxK
  exact hδK (ball_subset_ball hr hx) hxK

/-- Conjugate by the translation `x ↦ x + p`, so the new origin is the old `p`. -/
def centered (T : E ≃ₜ E) (p : E) : E ≃ₜ E where
  toFun x := T (x + p) - p
  invFun x := T.symm (x + p) - p
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := (T.continuous.comp (continuous_id.add_const p)).sub continuous_const
  continuous_invFun := (T.symm.continuous.comp (continuous_id.add_const p)).sub continuous_const

@[simp] theorem centered_apply (T : E ≃ₜ E) (p x : E) :
    centered T p x = T (x + p) - p := rfl

@[simp] theorem centered_symm_apply (T : E ≃ₜ E) (p x : E) :
    (centered T p).symm x = T.symm (x + p) - p := rfl

theorem centered_zero (T : E ≃ₜ E) {p : E} (hp : T p = p) :
    centered T p 0 = 0 := by simp [hp]

theorem centered_pow_apply (T : E ≃ₜ E) (p x : E) (m : ℕ) :
    (centered T p ^ m) x = (T ^ m) (x + p) - p := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', pow_succ', Homeomorph.mul_apply, Homeomorph.mul_apply,
        centered_apply, ih, sub_add_cancel]

/-- Translation carries the zero-centered local basin exactly onto the basin
of the same-radius ball centered at the original point. -/
theorem mem_centered_basin_iff (T : E ≃ₜ E) (p x : E) (r : ℝ) :
    x ∈ BasinGlobalization.basin (centered T p) (ball 0 r) ↔
      x + p ∈ BasinGlobalization.basin T (ball p r) := by
  simp only [BasinGlobalization.basin, mem_ofPred_eq, centered_pow_apply,
    mem_ball, dist_eq_norm, sub_zero]

/-- The actual homeomorphism between the translated entry basins. -/
def centeredBasinHomeomorph (T : E ≃ₜ E) (p : E) (r : ℝ) :
    BasinGlobalization.basin (centered T p) (ball 0 r) ≃ₜ
      BasinGlobalization.basin T (ball p r) where
  toFun x := ⟨x.val + p, (mem_centered_basin_iff T p x r).mp x.property⟩
  invFun y := ⟨y.val - p, (mem_centered_basin_iff T p (y.val - p) r).mpr
    (by simpa only [sub_add_cancel] using y.property)⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  continuous_toFun := (continuous_subtype_val.add_const p).subtype_mk _
  continuous_invFun := (continuous_subtype_val.sub continuous_const).subtype_mk _

@[simp] theorem centeredBasinHomeomorph_apply (T : E ≃ₜ E) (p : E) (r : ℝ)
    (x : BasinGlobalization.basin (centered T p) (ball 0 r)) :
    (centeredBasinHomeomorph T p r x : E) = x + p := rfl

@[simp] theorem centeredBasinHomeomorph_symm_apply (T : E ≃ₜ E) (p : E) (r : ℝ)
    (x : BasinGlobalization.basin T (ball p r)) :
    ((centeredBasinHomeomorph T p r).symm x : E) = x - p := rfl

end Translation

section Holomorphic

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem differentiable_centered (T : E ≃ₜ E) (p : E)
    (hT : Differentiable ℂ (T : E → E)) : Differentiable ℂ (centered T p : E → E) :=
  (hT.comp (differentiable_id.add_const p)).sub_const p

theorem differentiable_centered_symm (T : E ≃ₜ E) (p : E)
    (hT : Differentiable ℂ (T.symm : E → E)) :
    Differentiable ℂ ((centered T p).symm : E → E) :=
  (hT.comp (differentiable_id.add_const p)).sub_const p

theorem hasFDerivAt_centered_zero (T : E ≃ₜ E) (p : E) (A : E →L[ℂ] E)
    (hT : HasFDerivAt (T : E → E) A p) :
    HasFDerivAt (centered T p : E → E) A 0 := by
  have ht : HasFDerivAt (fun x : E => x + p) (ContinuousLinearMap.id ℂ E) 0 :=
    (hasFDerivAt_id 0).add_const p
  have hT' : HasFDerivAt (T : E → E) A (0 + p) := by simpa only [zero_add] using hT
  change HasFDerivAt (fun x : E => T (x + p) - p) A 0
  simpa only [ContinuousLinearMap.comp_id, Function.comp_def] using (hT'.comp 0 ht).sub_const p

/-- Transfer an actual holomorphic basin parameterization back from centered
coordinates, including holomorphicity of its inverse on the full target. -/
theorem transfer_biholomorphic_basin (T : E ≃ₜ E) (p : E) (r : ℝ)
    (H : BasinGlobalization.basin (centered T p) (ball 0 r) ≃ₜ E)
    (h : E → E)
    (hh : DifferentiableOn ℂ h (BasinGlobalization.basin (centered T p) (ball 0 r)))
    (hH : ∀ x : BasinGlobalization.basin (centered T p) (ball 0 r), H x = h x)
    (hInv : Differentiable ℂ (fun y => (H.symm y : E))) :
    ∃ G : BasinGlobalization.basin T (ball p r) ≃ₜ E, ∃ g : E → E,
      DifferentiableOn ℂ g (BasinGlobalization.basin T (ball p r)) ∧
      (∀ x : BasinGlobalization.basin T (ball p r), G x = g x) ∧
      Differentiable ℂ (fun y => (G.symm y : E)) := by
  let J := centeredBasinHomeomorph T p r
  refine ⟨J.symm.trans H, fun x => h (x - p), ?_, ?_, ?_⟩
  · apply hh.comp (differentiable_id.sub_const p).differentiableOn
    intro x hx
    apply (mem_centered_basin_iff T p (x - p) r).mpr
    simpa only [sub_add_cancel] using hx
  · intro x
    exact hH (J.symm x)
  · exact hInv.add_const p

end Holomorphic

end AutomaticContinuity.BasinAvoidance
