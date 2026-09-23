import AutomaticContinuity.HolomorphicInverseLimit
import Mathlib.Topology.OpenPartialHomeomorph.Basic

set_option autoImplicit false

/-!
# Globalizing an actual local conjugacy on its basin

The hypotheses explicitly supply a local conjugacy and exhaustion of the
target by inverse iterates. Attraction alone is not asserted to produce a
biholomorphism. The extension is independent of the entry time into the
local domain.
-/

noncomputable section

namespace AutomaticContinuity.BasinGlobalization

open Set Filter
open scoped Topology

section Topological

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- The points whose orbit enters the specified local domain. -/
def basin (T : E ≃ₜ E) (U : Set E) : Set E :=
  {x | ∃ m : ℕ, (T ^ m) x ∈ U}

theorem homeomorph_pow_apply (T : E ≃ₜ E) (m : ℕ) (x : E) :
    (T ^ m) x = (T : E → E)^[m] x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', Homeomorph.mul_apply, Function.iterate_succ_apply', ih]

theorem mem_basin_iff_iterate (T : E ≃ₜ E) (U : Set E) (x : E) :
    x ∈ basin T U ↔ ∃ m : ℕ, (T : E → E)^[m] x ∈ U := by
  simp only [basin, mem_ofPred_eq, homeomorph_pow_apply]

theorem isOpen_basin (T : E ≃ₜ E) {U : Set E} (hU : IsOpen U) :
    IsOpen (basin T U) := by
  have heq : basin T U = ⋃ m : ℕ, (T ^ m) ⁻¹' U := by ext x; simp [basin]
  rw [heq]
  exact isOpen_iUnion fun m => hU.preimage (T ^ m).continuous

theorem subset_basin (T : E ≃ₜ E) (U : Set E) : U ⊆ basin T U := by
  intro x hx
  exact ⟨0, by simpa using hx⟩

theorem mapsTo_pow_of_mapsTo (T : E ≃ₜ E) {U : Set E}
    (hT : MapsTo T U U) (m : ℕ) : MapsTo (T ^ m) U U := by
  induction m with
  | zero => intro x hx; simpa using hx
  | succ m ih =>
    intro x hx
    simpa only [pow_succ', Homeomorph.mul_apply] using hT (ih hx)

theorem mem_basin_apply_iff (T : E ≃ₜ E) {U : Set E} (hT : MapsTo T U U) (x : E) :
    T x ∈ basin T U ↔ x ∈ basin T U := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m + 1, by simpa only [pow_succ, Homeomorph.mul_apply] using hm⟩
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have heq : (T ^ m) (T x) = T ((T ^ m) x) := by
      have he : T ^ m * T = T * T ^ m := (Commute.self_pow T m).eq.symm
      exact congrArg (fun e : E ≃ₜ E => e x) he
    rw [heq]
    exact hT hm

/-- Ambient representatives of a local homeomorphism, with an actual
conjugacy equation on an open forward-invariant source domain. -/
structure LocalConjugacy (T : E ≃ₜ E) (A : F ≃ₜ F) (U : Set E) (V : Set F) where
  toFun : E → F
  invFun : F → E
  source_open : IsOpen U
  target_open : IsOpen V
  mapsTo : MapsTo toFun U V
  invMapsTo : MapsTo invFun V U
  left_inv : ∀ x ∈ U, invFun (toFun x) = x
  right_inv : ∀ y ∈ V, toFun (invFun y) = y
  continuousOn_toFun : ContinuousOn toFun U
  continuousOn_invFun : ContinuousOn invFun V
  forward_invariant : MapsTo T U U
  conjugacy : ∀ x ∈ U, toFun (T x) = A (toFun x)

namespace LocalConjugacy

variable {T : E ≃ₜ E} {A : F ≃ₜ F} {U : Set E} {V : Set F}
    (D : LocalConjugacy T A U V)

/-- Restrict an actual local homeomorphism to any smaller open invariant
domain on which its ambient maps satisfy the conjugacy equation. -/
def ofOpenPartialHomeomorph (e : OpenPartialHomeomorph E F)
    (hU : IsOpen U) (hUs : U ⊆ e.source)
    (hTU : MapsTo T U U)
    (hconj : ∀ x ∈ U, e (T x) = A (e x)) :
    LocalConjugacy T A U (e '' U) where
  toFun := e
  invFun := e.symm
  source_open := hU
  target_open := e.isOpen_image_of_subset_source hU hUs
  mapsTo := fun x hx => ⟨x, hx, rfl⟩
  invMapsTo := by
    rintro _ ⟨x, hx, rfl⟩
    simpa only [e.left_inv (hUs hx)] using hx
  left_inv := fun _ hx => e.left_inv (hUs hx)
  right_inv := by
    rintro _ ⟨x, hx, rfl⟩
    rw [e.left_inv (hUs hx)]
  continuousOn_toFun := e.continuousOn.mono hUs
  continuousOn_invFun := e.symm.continuousOn.mono (by
    rintro _ ⟨x, hx, rfl⟩
    exact e.mapsTo (hUs hx))
  forward_invariant := hTU
  conjugacy := hconj

theorem conjugacy_pow (m : ℕ) {x : E} (hx : x ∈ U) :
    D.toFun ((T ^ m) x) = (A ^ m) (D.toFun x) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_succ', Homeomorph.mul_apply, Homeomorph.mul_apply,
      D.conjugacy _ (mapsTo_pow_of_mapsTo T D.forward_invariant m hx), ih]

/-- The defining compatibility relation for the global extension. -/
def Related (x : E) (y : F) : Prop :=
  ∃ m : ℕ, (T ^ m) x ∈ U ∧ D.toFun ((T ^ m) x) = (A ^ m) y

theorem related_extend {x : E} {y : F} {m : ℕ}
    (hx : (T ^ m) x ∈ U) (he : D.toFun ((T ^ m) x) = (A ^ m) y) (n : ℕ) :
    (T ^ (n + m)) x ∈ U ∧ D.toFun ((T ^ (n + m)) x) = (A ^ (n + m)) y := by
  simp only [pow_add, Homeomorph.mul_apply]
  exact ⟨mapsTo_pow_of_mapsTo T D.forward_invariant n hx,
    (D.conjugacy_pow n hx).trans (congrArg (fun z => (A ^ n) z) he)⟩

theorem related_unique {x : E} {y z : F} (hy : D.Related x y) (hz : D.Related x z) :
    y = z := by
  obtain ⟨m, hxm, hym⟩ := hy
  obtain ⟨n, hxn, hzn⟩ := hz
  have hmy := (D.related_extend hxm hym n).2
  have hnz := (D.related_extend hxn hzn m).2
  rw [Nat.add_comm m n] at hnz
  exact (A ^ (n + m)).injective (hmy.symm.trans hnz)

theorem related_source_unique {x z : E} {y : F}
    (hx : D.Related x y) (hz : D.Related z y) : x = z := by
  obtain ⟨m, hxm, hm⟩ := hx
  obtain ⟨n, hzn, hn⟩ := hz
  obtain ⟨hxn', hm'⟩ := D.related_extend hxm hm n
  obtain ⟨hzm', hn'⟩ := D.related_extend hzn hn m
  rw [Nat.add_comm m n] at hzm' hn'
  apply (T ^ (n + m)).injective
  calc
    (T ^ (n + m)) x = D.invFun (D.toFun ((T ^ (n + m)) x)) :=
      (D.left_inv _ hxn').symm
    _ = D.invFun (D.toFun ((T ^ (n + m)) z)) := congrArg D.invFun (hm'.trans hn'.symm)
    _ = (T ^ (n + m)) z := D.left_inv _ hzm'

theorem exists_related {x : E} (hx : x ∈ basin T U) : ∃ y : F, D.Related x y := by
  obtain ⟨m, hm⟩ := hx
  exact ⟨(A ^ m).symm (D.toFun ((T ^ m) x)), m, hm, by simp⟩

def globalMap (x : basin T U) : F := Classical.choose (D.exists_related x.property)

theorem related_globalMap (x : basin T U) : D.Related x (D.globalMap x) :=
  Classical.choose_spec (D.exists_related x.property)

/-- On every entry-time chart the global map is the expected explicit formula. -/
theorem globalMap_eq {x : basin T U} (m : ℕ) (hx : (T ^ m) (x : E) ∈ U) :
    D.globalMap x = (A ^ m).symm (D.toFun ((T ^ m) (x : E))) :=
  D.related_unique (D.related_globalMap x) ⟨m, hx, by simp⟩

theorem globalMap_conjugacy (x : basin T U) :
    D.globalMap ⟨T x, (mem_basin_apply_iff T D.forward_invariant x).mpr x.property⟩ =
      A (D.globalMap x) := by
  obtain ⟨m, hm, he⟩ := D.related_globalMap x
  obtain ⟨hm', he'⟩ := D.related_extend hm he 1
  rw [Nat.add_comm 1 m, pow_succ, Homeomorph.mul_apply] at hm'
  rw [Nat.add_comm 1 m, pow_succ, pow_succ, Homeomorph.mul_apply,
    Homeomorph.mul_apply] at he'
  exact D.related_unique (D.related_globalMap _) ⟨m, hm', he'⟩

theorem globalMap_injective : Function.Injective D.globalMap := by
  intro x z hxz
  apply Subtype.ext
  exact D.related_source_unique (D.related_globalMap x)
    (hxz ▸ D.related_globalMap z)

theorem globalMap_surjective (hex : ∀ y : F, ∃ m : ℕ, (A ^ m) y ∈ V) :
    Function.Surjective D.globalMap := by
  intro y
  obtain ⟨m, hm⟩ := hex y
  let x : E := (T ^ m).symm (D.invFun ((A ^ m) y))
  have hx : (T ^ m) x ∈ U := by simpa only [x, Homeomorph.apply_symm_apply] using D.invMapsTo hm
  refine ⟨⟨x, m, hx⟩, ?_⟩
  apply D.related_unique (D.related_globalMap ⟨x, m, hx⟩)
  exact ⟨m, hx, by simpa only [x, Homeomorph.apply_symm_apply] using D.right_inv _ hm⟩

def globalEquiv (hex : ∀ y : F, ∃ m : ℕ, (A ^ m) y ∈ V) : basin T U ≃ F :=
  Equiv.ofBijective D.globalMap ⟨D.globalMap_injective, D.globalMap_surjective hex⟩

theorem globalEquiv_symm_eq (hex : ∀ y : F, ∃ m : ℕ, (A ^ m) y ∈ V)
    {y : F} (m : ℕ) (hy : (A ^ m) y ∈ V) :
    ((D.globalEquiv hex).symm y : E) = (T ^ m).symm (D.invFun ((A ^ m) y)) := by
  have hrel : D.Related ((D.globalEquiv hex).symm y : E) y := by
    have heq : D.globalMap ((D.globalEquiv hex).symm y) = y :=
      (D.globalEquiv hex).apply_symm_apply y
    simpa only [heq] using D.related_globalMap ((D.globalEquiv hex).symm y)
  apply D.related_source_unique hrel
  refine ⟨m, ?_, ?_⟩
  · simpa only [Homeomorph.apply_symm_apply] using D.invMapsTo hy
  · simpa only [Homeomorph.apply_symm_apply] using D.right_inv _ hy

theorem continuous_globalMap : Continuous D.globalMap := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨m, hm⟩ := x.property
  have hc : Continuous (fun z : basin T U => (T ^ m) (z : E)) :=
    (T ^ m).continuous.comp continuous_subtype_val
  have hh : ContinuousAt D.toFun ((T ^ m) (x : E)) :=
    D.continuousOn_toFun.continuousAt (D.source_open.mem_nhds hm)
  have hcomp : ContinuousAt (fun z : basin T U =>
      (A ^ m).symm (D.toFun ((T ^ m) (z : E)))) x :=
    (A ^ m).symm.continuous.continuousAt.comp
      (hh.comp (f := fun z : basin T U => (T ^ m) (z : E)) hc.continuousAt)
  apply hcomp.congr
  filter_upwards [hc.continuousAt.preimage_mem_nhds (D.source_open.mem_nhds hm)] with z hz
  exact (D.globalMap_eq m hz).symm

theorem continuous_globalEquiv_symm (hex : ∀ y : F, ∃ m : ℕ, (A ^ m) y ∈ V) :
    Continuous (D.globalEquiv hex).symm := by
  apply continuous_induced_rng.mpr
  apply continuous_iff_continuousAt.mpr
  intro y
  obtain ⟨m, hm⟩ := hex y
  have hh : ContinuousAt D.invFun ((A ^ m) y) :=
    D.continuousOn_invFun.continuousAt (D.target_open.mem_nhds hm)
  have hcomp : ContinuousAt (fun z : F => (T ^ m).symm (D.invFun ((A ^ m) z))) y :=
    (T ^ m).symm.continuous.continuousAt.comp (hh.comp (A ^ m).continuous.continuousAt)
  apply hcomp.congr
  filter_upwards [(A ^ m).continuous.continuousAt.preimage_mem_nhds
    (D.target_open.mem_nhds hm)] with z hz
  exact (D.globalEquiv_symm_eq hex m hz).symm

/-- The basin is homeomorphic to the full target once the target iterates
enter the local conjugacy image. -/
def globalHomeomorph (hex : ∀ y : F, ∃ m : ℕ, (A ^ m) y ∈ V) : basin T U ≃ₜ F where
  toEquiv := D.globalEquiv hex
  continuous_toFun := D.continuous_globalMap
  continuous_invFun := D.continuous_globalEquiv_symm hex

end LocalConjugacy

end Topological

section Holomorphic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {T : E ≃ₜ E} {A : F ≃ₜ F} {U : Set E} {V : Set F}

theorem differentiable_homeomorph_pow (T : E ≃ₜ E)
    (hT : Differentiable ℂ (T : E → E)) (m : ℕ) :
    Differentiable ℂ (fun x => (T ^ m) x) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simpa only [pow_succ', Homeomorph.mul_apply, Function.comp_def] using hT.comp ih

theorem differentiable_homeomorph_symm_pow (T : E ≃ₜ E)
    (hT : Differentiable ℂ (T.symm : E → E)) (m : ℕ) :
    Differentiable ℂ (fun x => (T ^ m).symm x) := by
  have heq : (T ^ m).symm = T.symm ^ m := by
    change (T ^ m)⁻¹ = (T⁻¹) ^ m
    exact (inv_pow T m).symm
  rw [heq]
  exact differentiable_homeomorph_pow T.symm hT m

namespace LocalConjugacy

variable (D : LocalConjugacy T A U V)

/-- An ambient representative of the global map. Its values off the basin
are set to zero; all analytic assertions concern the open basin. -/
def globalExtension (x : E) : F := by
  classical
  exact if hx : x ∈ basin T U then D.globalMap ⟨x, hx⟩ else 0

omit [NormedSpace ℂ E] [NormedSpace ℂ F] in
@[simp] theorem globalExtension_of_mem {x : E} (hx : x ∈ basin T U) :
    D.globalExtension x = D.globalMap ⟨x, hx⟩ := by simp [globalExtension, hx]

omit [NormedSpace ℂ E] [NormedSpace ℂ F] in
theorem globalExtension_eq_local {x : E} (hx : x ∈ U) :
    D.globalExtension x = D.toFun x := by
  rw [D.globalExtension_of_mem (subset_basin T U hx)]
  exact D.globalMap_eq (x := ⟨x, subset_basin T U hx⟩) 0 (by simpa using hx)

/-- Holomorphicity of the global extension follows chart by chart from its
explicit entry-time formula. No normal-family or basin theorem is assumed. -/
theorem differentiableOn_globalExtension
    (hT : Differentiable ℂ (T : E → E))
    (hAinv : Differentiable ℂ (A.symm : F → F))
    (hh : DifferentiableOn ℂ D.toFun U) :
    DifferentiableOn ℂ D.globalExtension (basin T U) := by
  intro x hx
  obtain ⟨m, hm⟩ := hx
  have hhAt : DifferentiableAt ℂ D.toFun ((T ^ m) x) :=
    (hh _ hm).differentiableAt (D.source_open.mem_nhds hm)
  have hcomp : DifferentiableAt ℂ (fun z : E =>
      (A ^ m).symm (D.toFun ((T ^ m) z))) x :=
    ((differentiable_homeomorph_symm_pow A hAinv m).differentiableAt).comp x
      (hhAt.comp x (differentiable_homeomorph_pow T hT m).differentiableAt)
  apply (hcomp.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [(T ^ m).continuous.continuousAt.preimage_mem_nhds
    (D.source_open.mem_nhds hm)] with z hz
  rw [D.globalExtension_of_mem ⟨m, hz⟩]
  exact D.globalMap_eq m hz

theorem differentiable_globalHomeomorph_symm
    (hex : ∀ y : F, ∃ m : ℕ, (A ^ m) y ∈ V)
    (hTinv : Differentiable ℂ (T.symm : E → E))
    (hA : Differentiable ℂ (A : F → F))
    (hk : DifferentiableOn ℂ D.invFun V) :
    Differentiable ℂ (fun y : F => ((D.globalHomeomorph hex).symm y : E)) := by
  intro y
  obtain ⟨m, hm⟩ := hex y
  have hkAt : DifferentiableAt ℂ D.invFun ((A ^ m) y) :=
    (hk _ hm).differentiableAt (D.target_open.mem_nhds hm)
  have hcomp : DifferentiableAt ℂ (fun z : F =>
      (T ^ m).symm (D.invFun ((A ^ m) z))) y :=
    ((differentiable_homeomorph_symm_pow T hTinv m).differentiableAt).comp y
      (hkAt.comp y (differentiable_homeomorph_pow A hA m).differentiableAt)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [(A ^ m).continuous.continuousAt.preimage_mem_nhds
    (D.target_open.mem_nhds hm)] with z hz
  exact D.globalEquiv_symm_eq hex m hz

include D in
omit [NormedSpace ℂ E] [NormedSpace ℂ F] in
/-- Actual attraction to a point in the open local image discharges the
exhaustion hypothesis. A specific contracting linear map can supply this. -/
theorem target_exhaustion_of_tendsto_zero (h0 : (0 : F) ∈ V)
    (hA : ∀ y : F, Tendsto (fun m : ℕ => (A ^ m) y) atTop (𝓝 0)) :
    ∀ y : F, ∃ m : ℕ, (A ^ m) y ∈ V := by
  intro y
  exact ((hA y).eventually (D.target_open.mem_nhds h0)).exists

/-- The basin is biholomorphic to the full target under a genuine local
holomorphic conjugacy and target exhaustion. The witness is the constructed
extension, and its inverse is the constructed homeomorphism inverse. -/
theorem exists_biholomorphic_globalization
    (hex : ∀ y : F, ∃ m : ℕ, (A ^ m) y ∈ V)
    (hT : Differentiable ℂ (T : E → E))
    (hTinv : Differentiable ℂ (T.symm : E → E))
    (hA : Differentiable ℂ (A : F → F))
    (hAinv : Differentiable ℂ (A.symm : F → F))
    (hh : DifferentiableOn ℂ D.toFun U)
    (hk : DifferentiableOn ℂ D.invFun V) :
    ∃ H : basin T U ≃ₜ F, ∃ h : E → F,
      DifferentiableOn ℂ h (basin T U) ∧
      (∀ x : basin T U, H x = h x) ∧
      Differentiable ℂ (fun y : F => (H.symm y : E)) ∧
      (∀ x ∈ U, h x = D.toFun x) := by
  refine ⟨D.globalHomeomorph hex, D.globalExtension,
    D.differentiableOn_globalExtension hT hAinv hh, ?_,
    D.differentiable_globalHomeomorph_symm hex hTinv hA hk, ?_⟩
  · intro x
    exact (D.globalExtension_of_mem x.property).symm
  · exact fun x hx => D.globalExtension_eq_local hx

end LocalConjugacy

end Holomorphic

end AutomaticContinuity.BasinGlobalization
