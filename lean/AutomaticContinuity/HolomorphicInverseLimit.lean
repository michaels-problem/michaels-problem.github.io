import AutomaticContinuity.SeveralVariableUniformLimit
import Mathlib.Topology.UniformSpace.UniformApproximation

set_option autoImplicit false

/-!
# Inverse identities survive locally uniform convergence

This is the limit-identification step for a possible sequence of holomorphic
automorphisms. The approximating maps have actual inverse identities; those
identities for the limits are proved by convergence at moving points. The
construction of such a sequence, its convergence domains, and the inclusions
of the limit images in those domains are separate obligations.
-/

noncomputable section

namespace AutomaticContinuity.HolomorphicInverseLimit

open Filter Set
open scoped Topology

section Topological

variable {E F ι : Type*} [UniformSpace E] [UniformSpace F]
    [T2Space E] [T2Space F]
    {l : Filter ι} [l.NeBot]
    {U : Set E} {V : Set F}
    {fSeq : ι → E → F} {gSeq : ι → F → E} {f : E → F} {g : F → E}

omit [T2Space F] in
/-- One inverse identity passes to the limit. Local uniform convergence is
used on the inverse sequence at the moving points `fSeq i x`. -/
theorem left_inverse_on_of_limits (hV : IsOpen V)
    (hf : ∀ x ∈ U, Tendsto (fun i => fSeq i x) l (𝓝 (f x)))
    (hg : TendstoLocallyUniformlyOn gSeq g l V)
    (hgc : ContinuousOn g V) (hfV : MapsTo f U V)
    (hInv : ∀ᶠ i in l, ∀ x ∈ U, gSeq i (fSeq i x) = x) :
    ∀ x ∈ U, g (f x) = x := by
  intro x hx
  have hfx : f x ∈ V := hfV hx
  have hmove : Tendsto (fun i => fSeq i x) l (𝓝[V] (f x)) := by
    rw [nhdsWithin_eq_nhds.mpr (hV.mem_nhds hfx)]
    exact hf x hx
  have hcomp : Tendsto (fun i => gSeq i (fSeq i x)) l (𝓝 (g (f x))) :=
    hg.tendsto_comp (hgc (f x) hfx) hfx hmove
  have hconst : Tendsto (fun i => gSeq i (fSeq i x)) l (𝓝 x) :=
    tendsto_const_nhds.congr' (hInv.mono fun i hi => (hi x hx).symm)
  exact tendsto_nhds_unique hcomp hconst

/-- Both actual inverse identities pass to the limits; continuity of the
limits follows from local uniform convergence of continuous maps. -/
theorem inverse_on_of_locallyUniformlyOn (hU : IsOpen U) (hV : IsOpen V)
    (hf : TendstoLocallyUniformlyOn fSeq f l U)
    (hg : TendstoLocallyUniformlyOn gSeq g l V)
    (hfc : ∀ i, ContinuousOn (fSeq i) U) (hgc : ∀ i, ContinuousOn (gSeq i) V)
    (hfV : MapsTo f U V) (hgU : MapsTo g V U)
    (hLeft : ∀ᶠ i in l, ∀ x ∈ U, gSeq i (fSeq i x) = x)
    (hRight : ∀ᶠ i in l, ∀ y ∈ V, fSeq i (gSeq i y) = y) :
    (∀ x ∈ U, g (f x) = x) ∧ (∀ y ∈ V, f (g y) = y) := by
  have hfCont : ContinuousOn f U := hf.continuousOn (Eventually.of_forall hfc).frequently
  have hgCont : ContinuousOn g V := hg.continuousOn (Eventually.of_forall hgc).frequently
  exact ⟨left_inverse_on_of_limits hV (fun _ hx => hf.tendsto_at hx)
      hg hgCont hfV hLeft,
    left_inverse_on_of_limits hU (fun _ hy => hg.tendsto_at hy)
      hf hfCont hgU hRight⟩

/-- The actual limits restrict to a homeomorphism of their open domains.
Neither inverse identity of the limits is assumed. -/
def homeomorphOfLocallyUniformInverseLimits (hU : IsOpen U) (hV : IsOpen V)
    (hf : TendstoLocallyUniformlyOn fSeq f l U)
    (hg : TendstoLocallyUniformlyOn gSeq g l V)
    (hfc : ∀ i, ContinuousOn (fSeq i) U) (hgc : ∀ i, ContinuousOn (gSeq i) V)
    (hfV : MapsTo f U V) (hgU : MapsTo g V U)
    (hLeft : ∀ᶠ i in l, ∀ x ∈ U, gSeq i (fSeq i x) = x)
    (hRight : ∀ᶠ i in l, ∀ y ∈ V, fSeq i (gSeq i y) = y) : U ≃ₜ V where
  toFun x := ⟨f x, hfV x.property⟩
  invFun y := ⟨g y, hgU y.property⟩
  left_inv x := Subtype.ext
    ((inverse_on_of_locallyUniformlyOn hU hV hf hg hfc hgc hfV hgU hLeft hRight).1
      x x.property)
  right_inv y := Subtype.ext
    ((inverse_on_of_locallyUniformlyOn hU hV hf hg hfc hgc hfV hgU hLeft hRight).2
      y y.property)
  continuous_toFun :=
    (continuousOn_iff_continuous_domRestrict.mp
      (hf.continuousOn (Eventually.of_forall hfc).frequently)).subtype_mk _
  continuous_invFun :=
    (continuousOn_iff_continuous_domRestrict.mp
      (hg.continuousOn (Eventually.of_forall hgc).frequently)).subtype_mk _

end Topological

section Holomorphic

variable {E F ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [ProperSpace F]
    {l : Filter ι} [l.NeBot]
    {U : Set E} {V : Set F}
    {fSeq : ι → E → F} {gSeq : ι → F → E} {f : E → F} {g : F → E}

/-- In proper complex normed spaces, locally uniform limits of holomorphic
inverse pairs induce a homeomorphism whose ambient forward and inverse maps
are holomorphic on their respective open domains. -/
theorem exists_holomorphic_inverse_limit (hU : IsOpen U) (hV : IsOpen V)
    (hf : TendstoLocallyUniformlyOn fSeq f l U)
    (hg : TendstoLocallyUniformlyOn gSeq g l V)
    (hfhol : ∀ i, DifferentiableOn ℂ (fSeq i) U)
    (hghol : ∀ i, DifferentiableOn ℂ (gSeq i) V)
    (hfV : MapsTo f U V) (hgU : MapsTo g V U)
    (hLeft : ∀ᶠ i in l, ∀ x ∈ U, gSeq i (fSeq i x) = x)
    (hRight : ∀ᶠ i in l, ∀ y ∈ V, fSeq i (gSeq i y) = y) :
    DifferentiableOn ℂ f U ∧ DifferentiableOn ℂ g V ∧
      ∃ H : U ≃ₜ V, (∀ x : U, (H x : F) = f x) ∧
        (∀ y : V, (H.symm y : E) = g y) := by
  refine ⟨SeveralVariableUniformLimit.differentiableOn_of_tendstoLocallyUniformlyOn
      hU hfhol hf,
    SeveralVariableUniformLimit.differentiableOn_of_tendstoLocallyUniformlyOn hV hghol hg,
    homeomorphOfLocallyUniformInverseLimits hU hV hf hg
      (fun i => (hfhol i).continuousOn) (fun i => (hghol i).continuousOn)
      hfV hgU hLeft hRight, ?_, ?_⟩ <;> intro x <;> rfl

end Holomorphic

end AutomaticContinuity.HolomorphicInverseLimit
