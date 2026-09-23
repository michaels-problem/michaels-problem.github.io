import AutomaticContinuity.ConcreteBallAvoidance
import AutomaticContinuity.SmallScaleHenonGeometry
import AutomaticContinuity.EuclideanPairRotations

set_option autoImplicit false

/-!
# Biholomorphic domains and normalized entire embeddings in a ball complement

The domains through arbitrary exterior points are obtained from the actual
canonical Hénon basins by Euclidean norm preserving complex linear rotations.
The derivative normalization uses the actual holomorphic inverse of the basin
parameterization; injectivity alone is not used to infer invertibility of a
complex derivative.
-/

noncomputable section

namespace AutomaticContinuity.BallComplementEmbeddings

open Set Filter SmallScaleHenonTrapping
open scoped Topology

/-- Every exterior point belongs to an actual biholomorphic domain contained
in the complement of the closed Euclidean ball. -/
theorem exists_biholomorphic_domain {r : ℝ} (hr : 0 < r) (p : ℂ × ℂ)
    (hp : r < euclideanPairNorm p) :
    ∃ Ω : Set (ℂ × ℂ), IsOpen Ω ∧ p ∈ Ω ∧
      (∀ v ∈ Ω, r < euclideanPairNorm v) ∧
      ∃ H : Ω ≃ₜ (ℂ × ℂ), ∃ h : (ℂ × ℂ) → ℂ × ℂ,
        DifferentiableOn ℂ h Ω ∧ (∀ x : Ω, H x = h x) ∧
        Differentiable ℂ (fun y : ℂ × ℂ => (H.symm y : ℂ × ℂ)) := by
  obtain ⟨β, a, hβ, hβq, hra, heq, _, _⟩ := exists_exteriorPoint_of_norm hr hp
  obtain ⟨Ω, hΩ, hpoint, hout, H, h, hhd, hHeq, hId⟩ :=
    ConcreteBallAvoidance.exists_biholomorphic_domain hβ hβq hr hra
  have hpos : 0 < euclideanPairNorm (exteriorPoint β a) := heq.symm ▸ (hr.trans hp)
  obtain ⟨e, he, henorm⟩ := EuclideanPairRotations.exists_rotation (exteriorPoint β a) p hpos heq
  let Ω' := e.symm ⁻¹' Ω
  let J : Ω' ≃ₜ Ω := {
    toFun := fun x => ⟨e.symm x, x.property⟩
    invFun := fun y => ⟨e y, by simpa only [Ω', mem_preimage, e.symm_apply_apply] using y.property⟩
    left_inv := fun x => Subtype.ext (e.apply_symm_apply x)
    right_inv := fun y => Subtype.ext (e.symm_apply_apply y)
    continuous_toFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk
      (fun x => x.property)
    continuous_invFun := (e.continuous.comp continuous_subtype_val).subtype_mk
      (fun y => by simpa only [Ω', mem_preimage, Function.comp_def, e.symm_apply_apply]
        using y.property) }
  refine ⟨Ω', hΩ.preimage e.symm.continuous, ?_, ?_, J.trans H,
    fun x => h (e.symm x), ?_, ?_, ?_⟩
  · change e.symm p ∈ Ω
    rw [← he, e.symm_apply_apply]
    exact hpoint
  · intro v hv
    have hnorm := henorm (e.symm v)
    rw [e.apply_symm_apply] at hnorm
    exact hnorm ▸ hout (e.symm v) hv
  · exact hhd.comp e.symm.differentiable.differentiableOn (fun _ hx => hx)
  · intro x
    exact hHeq (J x)
  · exact e.differentiable.comp hId

/-- An actual holomorphic coordinate map and holomorphic inverse normalize
the inverse parameterization to have identity derivative at the chosen point. -/
theorem normalized_embedding_of_domain {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Ω : Set E} (hΩ : IsOpen Ω) {p : E} (hp : p ∈ Ω)
    (H : Ω ≃ₜ E) (h : E → E) (hhd : DifferentiableOn ℂ h Ω)
    (hHeq : ∀ x : Ω, H x = h x)
    (hId : Differentiable ℂ (fun y : E => (H.symm y : E))) :
    ∃ f : E → E, Differentiable ℂ f ∧ Function.Injective f ∧ f 0 = p ∧
      HasFDerivAt f (ContinuousLinearMap.id ℂ E) 0 ∧ ∀ z, f z ∈ Ω := by
  let I : E → E := fun y => (H.symm y : E)
  have hleft : ∀ x ∈ Ω, I (h x) = x := by
    intro x hx
    rw [← hHeq ⟨x, hx⟩]
    exact congrArg Subtype.val (H.symm_apply_apply ⟨x, hx⟩)
  let K := fderiv ℂ h p
  let L := fderiv ℂ I (h p)
  have hhAt : HasFDerivAt h K p :=
    (hhd.differentiableAt (hΩ.mem_nhds hp)).hasFDerivAt
  have hIAt : HasFDerivAt I L (h p) := (hId (h p)).hasFDerivAt
  have hchain : HasFDerivAt (fun x => I (h x)) (L.comp K) p := hIAt.comp p hhAt
  have hnear : (fun x : E => x) =ᶠ[𝓝 p] (fun x => I (h x)) := by
    filter_upwards [hΩ.mem_nhds hp] with x hx
    exact (hleft x hx).symm
  have hLK : L.comp K = ContinuousLinearMap.id ℂ E :=
    (hchain.congr_of_eventuallyEq hnear).unique (hasFDerivAt_id p)
  have hKleft : Function.LeftInverse L K := by
    intro x
    exact congrArg (fun M : E →L[ℂ] E => M x) hLK
  let f : E → E := fun z => I (h p + K z)
  have hfn : HasFDerivAt f (ContinuousLinearMap.id ℂ E) 0 := by
    have hIAt' : HasFDerivAt I L (h p + K 0) := by simpa using hIAt
    simpa only [hLK, Function.comp_def, f] using hIAt'.comp 0 (K.hasFDerivAt.const_add (h p))
  refine ⟨f, hId.comp (K.differentiable.const_add (h p)), ?_, ?_, hfn, ?_⟩
  · intro x y hxy
    have hEq : H.symm (h p + K x) = H.symm (h p + K y) := Subtype.ext hxy
    exact hKleft.injective (add_left_cancel (H.symm.injective hEq))
  · simpa only [f, map_zero, add_zero] using hleft p hp
  · intro z
    exact (H.symm (h p + K z)).property

/-- An entire injective parameterization through any exterior point can be
normalized to have the identity complex derivative at zero. -/
theorem exists_normalized_entire_embedding {r : ℝ} (hr : 0 < r) (p : ℂ × ℂ)
    (hp : r < euclideanPairNorm p) :
    ∃ f : (ℂ × ℂ) → ℂ × ℂ, Differentiable ℂ f ∧ Function.Injective f ∧
      f 0 = p ∧ HasFDerivAt f (ContinuousLinearMap.id ℂ (ℂ × ℂ)) 0 ∧
      ∀ z, r < euclideanPairNorm (f z) := by
  obtain ⟨Ω, hΩ, hpΩ, hout, H, h, hhd, hHeq, hId⟩ := exists_biholomorphic_domain hr p hp
  obtain ⟨f, hf, hfinj, hf0, hfd, hfΩ⟩ := normalized_embedding_of_domain hΩ hpΩ H h hhd hHeq hId
  exact ⟨f, hf, hfinj, hf0, hfd, fun z => hout (f z) (hfΩ z)⟩

end AutomaticContinuity.BallComplementEmbeddings
