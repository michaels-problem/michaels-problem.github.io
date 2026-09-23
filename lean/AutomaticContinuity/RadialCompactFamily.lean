import AutomaticContinuity.CompactFamilyHolomorphy
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Complex.Tietze

set_option autoImplicit false

/-! # Actual holomorphic radial families on a compact convex set

A continuous extension from a closed thickening supplies an ambient family.
On an open set of complex dilation parameters containing the real interval
`[0,1]`, that family agrees exactly with the given holomorphic function.
-/

noncomputable section
namespace AutomaticContinuity.RadialCompactFamily
open Set Metric Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def radialMap (c : E) (t : ℂ) (x : E) : E := c + t • (x - c)

@[simp] theorem radialMap_zero (c x : E) : radialMap c 0 x = c := by simp [radialMap]
@[simp] theorem radialMap_one (c x : E) : radialMap c 1 x = x := by simp [radialMap]

theorem radialMap_mem {K : Set E} (hK : Convex ℝ K) {c x : E}
    (hc : c ∈ K) (hx : x ∈ K) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    radialMap c (t : ℂ) x ∈ K := by
  have hh := hK hc hx (sub_nonneg.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
  convert hh using 1
  change c + (t : ℂ) • (x - c) = (1-t) • c + t • x
  have heq : (t : ℂ) • (x - c) = t • (x - c) := by
    convert! (RCLike.real_smul_eq_coe_smul (K := ℂ) t (x-c)).symm using 1
  rw [heq, smul_sub, sub_smul, one_smul]
  abel

def radialContinuousMap (K : Set E) (c : E) (t : ℂ) : C(K,E) :=
  ⟨fun x => radialMap c t x.val, by unfold radialMap; fun_prop⟩

theorem continuous_radialContinuousMap (K : Set E) (c : E) :
    Continuous (radialContinuousMap K c) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ℂ × K => c + p.1 • (p.2.val - c))
  fun_prop

/-- The parameter domain has all desired fibre points in a prescribed open
set. Compactness of the original base makes this parameter domain open. -/
def radialDomain (K : Set E) (c : E) (W : Set E) : Set ℂ :=
  {t | ∀ x : K, radialMap c t x.val ∈ W}

theorem isOpen_radialDomain (K : Set E) [CompactSpace K] (c : E)
    {W : Set E} (hW : IsOpen W) : IsOpen (radialDomain K c W) := by
  have hh := (ContinuousMap.isOpen_setOfPred_mapsTo (X := K) isCompact_univ hW).preimage
    (continuous_radialContinuousMap K c)
  convert hh using 1
  ext t
  constructor
  · intro ht x _
    exact ht x
  · intro ht x
    exact ht (mem_univ x)

theorem exists_holomorphic_radial_family {K U : Set E} [CompactSpace K]
    (hK : IsCompact K) (hconv : Convex ℝ K) (hU : IsOpen U) (hKU : K ⊆ U)
    {c : E} (hc : c ∈ K) (f : E → ℂ) (hf : DifferentiableOn ℂ f U) :
    ∃ (O : Set ℂ) (F : ℂ → C(K,ℂ)), IsOpen O ∧
      (∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) ∈ O) ∧ Continuous F ∧
      DifferentiableOn ℂ F O ∧
      (∀ t ∈ O, ∀ x : K, F t x = f (radialMap c t x.val)) := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  let D : Set E := cthickening δ K
  let W : Set E := thickening δ K
  let fD : C(D,ℂ) := ⟨fun x => f x.val, (hf.continuousOn.mono hδU).domRestrict⟩
  obtain ⟨g, hg⟩ := fD.exists_restrict_eq isClosed_cthickening
  have heq : ∀ x ∈ D, g x = f x := by
    intro x hx
    exact congrArg (fun h : C(D,ℂ) => h ⟨x,hx⟩) hg
  let O := radialDomain K c W
  let F : ℂ → C(K,ℂ) := fun t => g.comp (radialContinuousMap K c t)
  have hO : IsOpen O := isOpen_radialDomain K c isOpen_thickening
  have hinterval : ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) ∈ O := by
    intro t ht x
    exact self_subset_thickening hδ K (radialMap_mem hconv hc x.property ht)
  have hFc : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : ℂ × K => g (c + p.1 • (p.2.val - c)))
    fun_prop
  have hFeq : ∀ t ∈ O, ∀ x : K, F t x = f (radialMap c t x.val) := by
    intro t ht x
    exact heq _ (thickening_subset_cthickening δ K (ht x))
  refine ⟨O, F, hO, hinterval, hFc, ?_, hFeq⟩
  apply CompactFamilyHolomorphy.differentiableOn_of_continuousOn F hO hFc.continuousOn
  intro x
  have hcompose : DifferentiableOn ℂ (fun t : ℂ => f (radialMap c t x.val)) O :=
    hf.comp (by unfold radialMap; fun_prop)
      (fun t ht => hδU (thickening_subset_cthickening δ K (ht x)))
  exact hcompose.congr (fun t ht => hFeq t ht x)

end AutomaticContinuity.RadialCompactFamily
