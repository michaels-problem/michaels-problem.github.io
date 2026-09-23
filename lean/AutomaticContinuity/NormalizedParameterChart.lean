import AutomaticContinuity.UniformParameterKoenigs
import AutomaticContinuity.FiniteHolomorphicRegularity
import Mathlib.Analysis.Normed.Ring.Units

set_option autoImplicit false

/-!
# A parameter-preserving local biholomorphic chart

A jointly holomorphic normalized family `H(p,x)` lifts to `(p,H(p,x))`.
Its full derivative is the identity at every `(p,0)`: the parameter derivative
vanishes because `H(p,0)=0`, while the fibre derivative is the identity. In
proper complex normed spaces the inverse function theorem therefore gives a
genuine joint local biholomorphism, preserving the parameter in both directions.
This is a local-family result and supplies no compact gluing theorem.
-/

noncomputable section

namespace AutomaticContinuity.NormalizedParameterChart

open Filter Metric Set
open scoped Topology

universe u v
variable {P : Type u} {E : Type v}
variable [NormedAddCommGroup P] [NormedSpace ℂ P]
variable [NormedAddCommGroup E] [NormedSpace ℂ E]

def lift (H : P × E → E) (z : P × E) : P × E := (z.1, H z)

/-- The normalization determines the full joint derivative of the lifted map. -/
theorem hasFDerivAt_lift {H : P × E → E} {U : Set P} {r : ℝ}
    (hU : IsOpen U) (hr : 0 < r)
    (hH : DifferentiableOn ℂ H (U ×ˢ ball 0 r))
    (hzero : ∀ p ∈ U, H (p, 0) = 0)
    (hder : ∀ p ∈ U, HasFDerivAt (fun x => H (p, x)) (ContinuousLinearMap.id ℂ E) 0)
    {p : P} (hp : p ∈ U) :
    HasFDerivAt (lift H) (ContinuousLinearMap.id ℂ (P × E)) (p, 0) := by
  let D := fderiv ℂ H (p, 0)
  have hD : HasFDerivAt H D (p, 0) :=
    (hH.differentiableAt ((hU.prod isOpen_ball).mem_nhds ⟨hp, mem_ball_self hr⟩)).hasFDerivAt
  have hconst : HasFDerivAt (fun p' : P => H (p', 0)) (0 : P →L[ℂ] E) p := by
    apply (hasFDerivAt_const (0 : E) p).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hp] with p' hp'
    exact hzero p' hp'
  have hleft := (hD.comp p ((hasFDerivAt_id p).prodMk (hasFDerivAt_const (0 : E) p))).unique hconst
  have hright := (hD.comp (0 : E)
    ((hasFDerivAt_const p (0 : E)).prodMk (hasFDerivAt_id (0 : E)))).unique (hder p hp)
  have hDp (v : P) : D (v, 0) = 0 := by
    simpa using congrArg (fun L : P →L[ℂ] E => L v) hleft
  have hDx (w : E) : D (0, w) = w := by
    simpa using congrArg (fun L : E →L[ℂ] E => L w) hright
  have hDeq : D = ContinuousLinearMap.snd ℂ P E := by
    apply ContinuousLinearMap.ext
    intro z
    calc
      D z = D (z.1, 0) + D (0, z.2) := by
        simpa only [Prod.mk_add_mk, add_zero, zero_add] using D.map_add (z.1, 0) (0, z.2)
      _ = z.2 := by rw [hDp, hDx, zero_add]
  have hfull := (hasFDerivAt_fst (𝕜 := ℂ) (p := (p, (0 : E)))).prodMk hD
  have hId : (ContinuousLinearMap.fst ℂ P E).prod D = ContinuousLinearMap.id ℂ (P × E) := by
    ext z <;> simp [hDeq]
  rw [hId] at hfull
  exact hfull

variable [ProperSpace P] [ProperSpace E]

/-- A complete joint local chart for a normalized holomorphic family. The
inverse is holomorphic on its actual target and preserves the parameter there.
The ambient forward map is exactly the given lift, with no further shrinking
or alteration of its values. -/
theorem exists_localBiholomorph {H : P × E → E} {U : Set P} {r : ℝ}
    (hU : IsOpen U) (hr : 0 < r)
    (hH : DifferentiableOn ℂ H (U ×ˢ ball 0 r))
    (hzero : ∀ p ∈ U, H (p, 0) = 0)
    (hder : ∀ p ∈ U, HasFDerivAt (fun x => H (p, x)) (ContinuousLinearMap.id ℂ E) 0)
    {p : P} (hp : p ∈ U) :
    ∃ e : OpenPartialHomeomorph (P × E) (P × E),
      (e : P × E → P × E) = lift H ∧
      (p, (0 : E)) ∈ e.source ∧ (p, (0 : E)) ∈ e.target ∧
      e.source ⊆ U ×ˢ ball 0 r ∧
      DifferentiableOn ℂ e e.source ∧ DifferentiableOn ℂ e.symm e.target ∧
      (∀ z, (e z).1 = z.1) ∧ (∀ z ∈ e.target, (e.symm z).1 = z.1) ∧
      HasStrictFDerivAt e (ContinuousLinearMap.id ℂ (P × E)) (p, 0) ∧
      HasStrictFDerivAt e.symm (ContinuousLinearMap.id ℂ (P × E)) (p, 0) ∧
      ∃ δ > 0, e.source = ball p δ ×ˢ ball (0 : E) δ := by
  let z₀ : P × E := (p, 0)
  let W : Set (P × E) := U ×ˢ ball 0 r
  have hW : IsOpen W := hU.prod isOpen_ball
  have hzW : z₀ ∈ W := ⟨hp, mem_ball_self hr⟩
  have hdiff : DifferentiableOn ℂ (lift H) W := differentiableOn_fst.prodMk hH
  have hnorm : HasFDerivAt (lift H) (ContinuousLinearMap.id ℂ (P × E)) z₀ :=
    hasFDerivAt_lift hU hr hH hzero hder hp
  have hstrict : HasStrictFDerivAt (lift H) (ContinuousLinearMap.id ℂ (P × E)) z₀ := by
    have hs := FiniteHolomorphicRegularity.hasStrictFDerivAt hW hdiff hzW
    rwa [hnorm.fderiv] at hs
  have hstrict' : HasStrictFDerivAt (lift H)
      ((ContinuousLinearEquiv.refl ℂ (P × E)) : (P × E) →L[ℂ] (P × E)) z₀ := hstrict
  let e₀ := hstrict'.toOpenPartialHomeomorph (lift H)
  have he₀ : (e₀ : P × E → P × E) = lift H := rfl
  have hzsource : z₀ ∈ e₀.source := hstrict'.mem_toOpenPartialHomeomorph_source
  have hfix : lift H z₀ = z₀ := by simp [lift, z₀, hzero p hp]
  have hunit0 : IsUnit (fderiv ℂ (lift H) z₀) := by
    rw [hnorm.fderiv]
    exact isUnit_one
  have hcont := FiniteHolomorphicRegularity.continuousAt_fderiv hW hdiff hzW
  have hunit : {z : P × E | IsUnit (fderiv ℂ (lift H) z)} ∈ 𝓝 z₀ :=
    hcont (Units.isOpen.mem_nhds hunit0)
  obtain ⟨δ, hδ, hδraw⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (e₀.open_source.mem_nhds hzsource) (inter_mem (hW.mem_nhds hzW) hunit))
  have hδsub : ball z₀ δ ⊆ W ∩ {z | IsUnit (fderiv ℂ (lift H) z)} :=
    fun _ hz => (hδraw hz).2
  have hδsource : ball z₀ δ ⊆ e₀.source := fun _ hz => (hδraw hz).1
  let e := e₀.restrOpen (ball z₀ δ) isOpen_ball
  have he : (e : P × E → P × E) = lift H := rfl
  have hzsource' : z₀ ∈ e.source := ⟨hzsource, mem_ball_self hδ⟩
  have hztarget : z₀ ∈ e.target := by
    simpa only [he, hfix] using e.map_source hzsource'
  have hsource : e.source ⊆ W := fun z hz => (hδsub hz.2).1
  have hinv : DifferentiableOn ℂ e.symm e.target := by
    intro z hz
    have hs := e.map_target hz
    obtain ⟨u, hu⟩ := (hδsub hs.2).2
    have hueq : ((ContinuousLinearEquiv.ofUnit u) : (P × E) →L[ℂ] (P × E)) =
        fderiv ℂ (lift H) (e.symm z) := by
      apply ContinuousLinearMap.ext
      intro v
      change (u : (P × E) →L[ℂ] (P × E)) v = _
      rw [hu]
    have hd := (hdiff.differentiableAt (hW.mem_nhds (hsource hs))).hasFDerivAt
    rw [← hueq] at hd
    exact (e.hasFDerivAt_symm hz hd).differentiableAt.differentiableWithinAt
  have hforward : ∀ z, (e z).1 = z.1 := fun _ => rfl
  have hbackward : ∀ z ∈ e.target, (e.symm z).1 = z.1 := by
    intro z hz
    have h := congrArg Prod.fst (e.right_inv hz)
    simpa only [hforward] using h
  have hesource : e.source = ball z₀ δ :=
    Set.Subset.antisymm (fun _ hz => hz.2) (fun _ hz => ⟨hδsource hz, hz⟩)
  have hefix : e z₀ = z₀ := hfix
  have heinv : e.symm z₀ = z₀ := by
    conv_lhs => rw [← hefix]
    exact e.left_inv hzsource'
  have hstrict_at : HasStrictFDerivAt e
      ((ContinuousLinearEquiv.refl ℂ (P × E)) : (P × E) →L[ℂ] (P × E)) (e.symm z₀) := by
    rw [heinv]
    exact hstrict'
  have hsInv : HasStrictFDerivAt e.symm (ContinuousLinearMap.id ℂ (P × E)) z₀ := by
    simpa only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl] using
      e.hasStrictFDerivAt_symm hztarget hstrict_at
  refine ⟨e, he, hzsource', hztarget, hsource, hdiff.mono hsource,
    hinv, hforward, hbackward, hstrict, hsInv, δ, hδ, ?_⟩
  simpa only [ball_prod_same] using hesource

end AutomaticContinuity.NormalizedParameterChart
