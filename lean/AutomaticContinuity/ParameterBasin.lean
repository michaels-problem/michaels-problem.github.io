import AutomaticContinuity.BasinToBasin
import AutomaticContinuity.NormalizedParameterChart

set_option autoImplicit false

/-!
# Holomorphic trivialization of an actual parameter basin

The automorphisms and local conjugacy are genuine maps on the product space.
Preservation of the parameter and attraction in the linear fibres identify the
target entry basin with the full product over the base. No family of
automorphisms satisfying approximation requirements is constructed here.
-/

noncomputable section

namespace AutomaticContinuity.ParameterBasin

open Set Filter Metric BasinGlobalization
open scoped Topology

section Topological

variable {P E : Type*} [TopologicalSpace P] [TopologicalSpace E] [Zero E]

omit [Zero E] in
theorem fst_pow (T : (P × E) ≃ₜ (P × E))
    (hT : ∀ z, (T z).1 = z.1) (n : ℕ) (z : P × E) :
    ((T ^ n) z).1 = z.1 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [pow_succ', Homeomorph.mul_apply, hT] using ih

omit [Zero E] in
theorem basin_subset_product (T : (P × E) ≃ₜ (P × E))
    (hT : ∀ z, (T z).1 = z.1) {U : Set (P × E)} {B : Set P}
    (hU : U ⊆ B ×ˢ univ) : basin T U ⊆ B ×ˢ univ := by
  rintro z ⟨n, hn⟩
  exact ⟨by simpa only [fst_pow T hT] using (hU hn).1, mem_univ _⟩

/-- Fibre attraction exhausts the full product above the base, even though
the target neighbourhood need not be a cylinder. -/
theorem basin_eq_product (A : (P × E) ≃ₜ (P × E))
    (hA : ∀ z, (A z).1 = z.1) {V : Set (P × E)} {B : Set P}
    (hV : IsOpen V) (hVB : V ⊆ B ×ˢ univ)
    (hzero : ∀ p ∈ B, (p, (0 : E)) ∈ V)
    (hattract : ∀ p ∈ B, ∀ y : E,
      Tendsto (fun n : ℕ => (A ^ n) (p, y)) atTop (𝓝 (p, 0))) :
    basin A V = B ×ˢ univ := by
  apply Subset.antisymm (basin_subset_product A hA hVB)
  intro z hz
  obtain ⟨n, hn⟩ := ((hattract z.1 hz.1 z.2).eventually
    (hV.mem_nhds (hzero z.1 hz.1))).exists
  exact ⟨n, hn⟩

omit [Zero E] in
theorem globalMap_fst {T A : (P × E) ≃ₜ (P × E)}
    {U V : Set (P × E)} (D : LocalConjugacy T A U V)
    (hT : ∀ z, (T z).1 = z.1) (hA : ∀ z, (A z).1 = z.1)
    (hD : ∀ z ∈ U, (D.toFun z).1 = z.1) (z : basin T U) :
    (D.globalMap z).1 = (z : P × E).1 := by
  obtain ⟨n, hn, he⟩ := D.related_globalMap z
  have hf := congrArg Prod.fst he
  simpa only [hD _ hn, fst_pow T hT, fst_pow A hA] using hf.symm

end Topological

section Holomorphic

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Globalizing a local fibre-preserving conjugacy gives a holomorphic
trivialization onto the full product over the base. Both maps have ambient
holomorphic representatives and preserve the actual parameter. -/
theorem exists_biholomorphic_product
    {T A : (P × E) ≃ₜ (P × E)} {U V : Set (P × E)} {B : Set P}
    (D : LocalConjugacy T A U V)
    (hTf : ∀ z, (T z).1 = z.1) (hAf : ∀ z, (A z).1 = z.1)
    (hDf : ∀ z ∈ U, (D.toFun z).1 = z.1)
    (hVB : V ⊆ B ×ˢ univ) (hzero : ∀ p ∈ B, (p, (0 : E)) ∈ V)
    (hattract : ∀ p ∈ B, ∀ y : E,
      Tendsto (fun n : ℕ => (A ^ n) (p, y)) atTop (𝓝 (p, 0)))
    (hT : Differentiable ℂ (T : P × E → P × E))
    (hTinv : Differentiable ℂ (T.symm : P × E → P × E))
    (hA : Differentiable ℂ (A : P × E → P × E))
    (hAinv : Differentiable ℂ (A.symm : P × E → P × E))
    (hh : DifferentiableOn ℂ D.toFun U) (hk : DifferentiableOn ℂ D.invFun V) :
    ∃ H : basin T U ≃ₜ (B ×ˢ (univ : Set E)),
      ∃ h k : P × E → P × E,
      DifferentiableOn ℂ h (basin T U) ∧
      DifferentiableOn ℂ k (B ×ˢ univ) ∧
      (∀ x : basin T U, (H x : P × E) = h x) ∧
      (∀ y : B ×ˢ (univ : Set E), (H.symm y : P × E) = k y) ∧
      (∀ x : basin T U, (H x : P × E).1 = (x : P × E).1) ∧
      (∀ y : B ×ˢ (univ : Set E), (H.symm y : P × E).1 = (y : P × E).1) ∧
      (∀ x ∈ U, h x = D.toFun x) := by
  have heq := basin_eq_product A hAf D.target_open hVB hzero hattract
  let H := D.basinHomeomorph.trans (Homeomorph.setCongr heq)
  have hf : ∀ x : basin T U, (H x : P × E).1 = (x : P × E).1 :=
    fun x => globalMap_fst D hTf hAf hDf x
  refine ⟨H, D.globalExtension, D.symm.globalExtension,
    D.differentiableOn_globalExtension hT hAinv hh, ?_, ?_, ?_, hf, ?_, ?_⟩
  · rw [← heq]
    exact D.symm.differentiableOn_globalExtension hA hTinv hk
  · intro x
    exact (D.globalExtension_of_mem x.property).symm
  · intro y
    exact (D.symm.globalExtension_of_mem (by
      change (y : P × E) ∈ basin A V
      rw [heq]
      exact y.property)).symm
  · intro y
    have h := hf (H.symm y)
    rw [H.apply_symm_apply] at h
    exact h.symm
  · exact fun x hx => D.globalExtension_eq_local hx

end Holomorphic

end AutomaticContinuity.ParameterBasin
