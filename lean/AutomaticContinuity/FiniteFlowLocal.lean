import AutomaticContinuity.FiniteFlowHolomorphy

set_option autoImplicit false

/-!
# Finite flow products on an open invariant domain

The factors are actual equivalences, with joint holomorphy assumed only on
the specified invariant open domain. No continuity or holomorphy outside
that domain is required. Actual inverse products and their generators are
proved from the equivalence identities.
-/

noncomputable section

namespace AutomaticContinuity.FiniteFlowLocal

open Set Filter
open scoped Topology BigOperators

variable {E : Type*}

def compose (e : ℕ → E ≃ E) : ℕ → E ≃ E
  | 0 => Equiv.refl E
  | n + 1 => (compose e n).trans (e n)

@[simp] theorem compose_zero_apply (e : ℕ → E ≃ E) (x : E) : compose e 0 x = x := rfl

@[simp] theorem compose_succ_apply (e : ℕ → E ≃ E) (n : ℕ) (x : E) :
    compose e (n + 1) x = e n (compose e n x) := rfl

@[simp] theorem compose_zero_symm_apply (e : ℕ → E ≃ E) (x : E) :
    (compose e 0).symm x = x := rfl

@[simp] theorem compose_succ_symm_apply (e : ℕ → E ≃ E) (n : ℕ) (x : E) :
    (compose e (n + 1)).symm x = (compose e n).symm ((e n).symm x) := rfl

theorem mapsTo_compose (e : ℕ → E ≃ E) (n : ℕ) {Ω : Set E}
    (he : ∀ i < n, MapsTo (e i) Ω Ω) : MapsTo (compose e n) Ω Ω := by
  induction n with
  | zero => exact fun _ hx => hx
  | succ n ih =>
    exact (he n (Nat.lt_succ_self n)).comp (ih (fun i hi => he i (Nat.lt_succ_of_lt hi)))

theorem mapsTo_compose_symm (e : ℕ → E ≃ E) (n : ℕ) {Ω : Set E}
    (he : ∀ i < n, MapsTo (e i).symm Ω Ω) : MapsTo (compose e n).symm Ω Ω := by
  induction n with
  | zero => exact fun _ hx => hx
  | succ n ih =>
    exact (ih (fun i hi => he i (Nat.lt_succ_of_lt hi))).comp (he n (Nat.lt_succ_self n))

theorem compose_at_zero (e : ℕ → ℂ → E ≃ E) (n : ℕ) (Ω : Set E)
    (hzero : ∀ i < n, ∀ x ∈ Ω, e i 0 x = x) {x : E} (hx : x ∈ Ω) :
    compose (fun i => e i 0) n x = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [compose_succ_apply, ih (fun i hi => hzero i (Nat.lt_succ_of_lt hi)),
      hzero n (Nat.lt_succ_self n) x hx]

theorem compose_symm_at_zero (e : ℕ → ℂ → E ≃ E) (n : ℕ) (Ω : Set E)
    (hzero : ∀ i < n, ∀ x ∈ Ω, e i 0 x = x) {x : E} (hx : x ∈ Ω) :
    (compose (fun i => e i 0) n).symm x = x := by
  apply (compose (fun i => e i 0) n).injective
  rw [Equiv.apply_symm_apply, compose_at_zero e n Ω hzero hx]

variable [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hasDerivAt_parameter_comp {F : ℂ × E → E} {g : ℂ → E}
    {Ω : Set E} (hΩ : IsOpen Ω) {x v w : E} (hx : x ∈ Ω)
    (hF : DifferentiableAt ℂ F (0, x)) (hF0 : ∀ y ∈ Ω, F (0, y) = y)
    (hFt : HasDerivAt (fun t : ℂ => F (t, x)) v 0)
    (hg : HasDerivAt g w 0) (hg0 : g 0 = x) :
    HasDerivAt (fun t : ℂ => F (t, g t)) (v + w) 0 := by
  let A := fderiv ℂ F (0, x)
  have hA : HasFDerivAt F A (0, x) := hF.hasFDerivAt
  have ht : HasDerivAt (fun t : ℂ => (t, x)) ((1 : ℂ), (0 : E)) 0 :=
    (hasDerivAt_id (0 : ℂ)).prodMk (hasDerivAt_const (0 : ℂ) x)
  have hAv : A (1, 0) = v := (hA.comp_hasDerivAt 0 ht).unique hFt
  have hs : HasDerivAt (fun t : ℂ => x + t • w) w 0 := by
    simpa only [zero_add, one_smul] using!
      (hasDerivAt_const (0 : ℂ) x).add ((hasDerivAt_id (0 : ℂ)).smul_const w)
  have hp : HasDerivAt (fun t : ℂ => ((0 : ℂ), x + t • w)) ((0 : ℂ), w) 0 :=
    (hasDerivAt_const (0 : ℂ) (0 : ℂ)).prodMk hs
  have hAw : A (0, w) = w := by
    have hh := hA.comp_hasDerivAt_of_eq 0 hp (by simp)
    change HasDerivAt (fun t : ℂ => F (0, x + t • w)) (A (0, w)) 0 at hh
    have hct : Tendsto (fun t : ℂ => x + t • w) (𝓝 0) (𝓝 x) := by
      simpa using hs.continuousAt.tendsto
    have heq : (fun t : ℂ => x + t • w) =ᶠ[𝓝 0] fun t => F (0, x + t • w) :=
      (hct.eventually (hΩ.mem_nhds hx)).mono fun t ht => (hF0 _ ht).symm
    exact (hh.congr_of_eventuallyEq heq).unique hs
  have hpair := (hasDerivAt_id (0 : ℂ)).prodMk hg
  have hh := hA.comp_hasDerivAt_of_eq 0 hpair (by simp [hg0])
  change HasDerivAt (fun t : ℂ => F (t, g t)) (A (1, w)) 0 at hh
  have hsum : A (1, w) = v + w := by
    rw [show ((1 : ℂ), w) = (1, 0) + (0, w) by simp, map_add, hAv, hAw]
  simpa only [hsum] using hh

theorem differentiableOn_compose (e : ℕ → ℂ → E ≃ E) (n : ℕ) (Ω : Set E)
    (he : ∀ i < n, DifferentiableOn ℂ (fun z : ℂ × E => e i z.1 z.2) (univ ×ˢ Ω))
    (hmap : ∀ i < n, ∀ t, MapsTo (e i t) Ω Ω) :
    DifferentiableOn ℂ (fun z : ℂ × E => compose (fun i => e i z.1) n z.2) (univ ×ˢ Ω) := by
  induction n with
  | zero => exact differentiableOn_snd
  | succ n ih =>
    apply (he n (Nat.lt_succ_self n)).comp
      (differentiableOn_fst.prodMk (ih (fun i hi => he i (Nat.lt_succ_of_lt hi))
        (fun i hi => hmap i (Nat.lt_succ_of_lt hi))))
    intro z hz
    exact ⟨mem_univ _, mapsTo_compose (fun i => e i z.1) n
      (fun i hi => hmap i (Nat.lt_succ_of_lt hi) z.1) hz.2⟩

theorem differentiableOn_compose_symm (e : ℕ → ℂ → E ≃ E) (n : ℕ) (Ω : Set E)
    (he : ∀ i < n, DifferentiableOn ℂ (fun z : ℂ × E => (e i z.1).symm z.2) (univ ×ˢ Ω))
    (hmap : ∀ i < n, ∀ t, MapsTo (e i t).symm Ω Ω) :
    DifferentiableOn ℂ (fun z : ℂ × E => (compose (fun i => e i z.1) n).symm z.2) (univ ×ˢ Ω) := by
  induction n with
  | zero => exact differentiableOn_snd
  | succ n ih =>
    apply (ih (fun i hi => he i (Nat.lt_succ_of_lt hi))
      (fun i hi => hmap i (Nat.lt_succ_of_lt hi))).comp
      (differentiableOn_fst.prodMk (he n (Nat.lt_succ_self n)))
    intro z hz
    exact ⟨mem_univ _, hmap n (Nat.lt_succ_self n) z.1 hz.2⟩

theorem hasDerivAt_compose_zero (e : ℕ → ℂ → E ≃ E) (V : ℕ → E → E)
    (n : ℕ) (Ω : Set E) (hΩ : IsOpen Ω)
    (he : ∀ i < n, DifferentiableOn ℂ (fun z : ℂ × E => e i z.1 z.2) (univ ×ˢ Ω))
    (hmap : ∀ i < n, ∀ t, MapsTo (e i t) Ω Ω)
    (hzero : ∀ i < n, ∀ x ∈ Ω, e i 0 x = x)
    (hder : ∀ i < n, ∀ x ∈ Ω, HasDerivAt (fun t : ℂ => e i t x) (V i x) 0)
    (x : E) (hx : x ∈ Ω) :
    HasDerivAt (fun t : ℂ => compose (fun i => e i t) n x)
      (∑ i ∈ Finset.range n, V i x) 0 := by
  induction n with
  | zero => simpa [compose] using hasDerivAt_const (0 : ℂ) x
  | succ n ih =>
    have hp := ih (fun i hi => he i (Nat.lt_succ_of_lt hi))
      (fun i hi => hmap i (Nat.lt_succ_of_lt hi))
      (fun i hi => hzero i (Nat.lt_succ_of_lt hi))
      (fun i hi => hder i (Nat.lt_succ_of_lt hi))
    have hz := compose_at_zero e n Ω (fun i hi => hzero i (Nat.lt_succ_of_lt hi)) hx
    have hnhds : (univ ×ˢ Ω : Set (ℂ × E)) ∈ 𝓝 (0, x) :=
      (isOpen_univ.prod hΩ).mem_nhds ⟨mem_univ _, hx⟩
    have hh := hasDerivAt_parameter_comp hΩ hx
      ((he n (Nat.lt_succ_self n)).differentiableAt hnhds)
      (hzero n (Nat.lt_succ_self n)) (hder n (Nat.lt_succ_self n) x hx) hp hz
    simpa only [compose_succ_apply, Finset.sum_range_succ, add_comm] using hh

theorem hasDerivAt_inverse_zero (e : ℂ → E ≃ E) (V : E → E)
    (Ω : Set E) (hΩ : IsOpen Ω)
    (he : DifferentiableOn ℂ (fun z : ℂ × E => e z.1 z.2) (univ ×ˢ Ω))
    (hei : DifferentiableOn ℂ (fun z : ℂ × E => (e z.1).symm z.2) (univ ×ˢ Ω))
    (hzero : ∀ x ∈ Ω, e 0 x = x)
    (hder : ∀ x ∈ Ω, HasDerivAt (fun t : ℂ => e t x) (V x) 0)
    (x : E) (hx : x ∈ Ω) :
    HasDerivAt (fun t : ℂ => (e t).symm x) (-V x) 0 := by
  have hz : (e 0).symm x = x := by
    apply (e 0).injective
    rw [Equiv.apply_symm_apply, hzero x hx]
  have hnhds : (univ ×ˢ Ω : Set (ℂ × E)) ∈ 𝓝 (0, x) :=
    (isOpen_univ.prod hΩ).mem_nhds ⟨mem_univ _, hx⟩
  have hp := (hasDerivAt_id (0 : ℂ)).prodMk (hasDerivAt_const (0 : ℂ) x)
  have hgi := (hei.differentiableAt hnhds).hasFDerivAt.comp_hasDerivAt (0 : ℂ) hp
  change HasDerivAt (fun t : ℂ => (e t).symm x) _ 0 at hgi
  have hg : DifferentiableAt ℂ (fun t : ℂ => (e t).symm x) 0 := hgi.differentiableAt
  have hh := hasDerivAt_parameter_comp hΩ hx (he.differentiableAt hnhds)
    hzero (hder x hx) hg.hasDerivAt hz
  have hsum : V x + deriv (fun t : ℂ => (e t).symm x) 0 = 0 := by
    have hc : HasDerivAt (fun _ : ℂ => x)
        (V x + deriv (fun t : ℂ => (e t).symm x) 0) 0 := by
      simpa only [Equiv.apply_symm_apply] using hh
    exact hc.unique (hasDerivAt_const (0 : ℂ) x)
  have hv : deriv (fun t : ℂ => (e t).symm x) 0 = -V x :=
    eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hsum)
  simpa only [hv] using hg.hasDerivAt

theorem hasDerivAt_compose_symm_zero (e : ℕ → ℂ → E ≃ E) (V : ℕ → E → E)
    (n : ℕ) (Ω : Set E) (hΩ : IsOpen Ω)
    (he : ∀ i < n, DifferentiableOn ℂ (fun z : ℂ × E => e i z.1 z.2) (univ ×ˢ Ω))
    (hei : ∀ i < n, DifferentiableOn ℂ (fun z : ℂ × E => (e i z.1).symm z.2) (univ ×ˢ Ω))
    (hmap : ∀ i < n, ∀ t, MapsTo (e i t) Ω Ω)
    (hmapi : ∀ i < n, ∀ t, MapsTo (e i t).symm Ω Ω)
    (hzero : ∀ i < n, ∀ x ∈ Ω, e i 0 x = x)
    (hder : ∀ i < n, ∀ x ∈ Ω, HasDerivAt (fun t : ℂ => e i t x) (V i x) 0)
    (x : E) (hx : x ∈ Ω) :
    HasDerivAt (fun t : ℂ => (compose (fun i => e i t) n).symm x)
      (-(∑ i ∈ Finset.range n, V i x)) 0 := by
  exact hasDerivAt_inverse_zero (fun t => compose (fun i => e i t) n)
    (fun x => ∑ i ∈ Finset.range n, V i x) Ω hΩ
    (differentiableOn_compose e n Ω he hmap)
    (differentiableOn_compose_symm e n Ω hei hmapi)
    (fun _ hx => compose_at_zero e n Ω hzero hx)
    (hasDerivAt_compose_zero e V n Ω hΩ he hmap hzero hder) x hx

end AutomaticContinuity.FiniteFlowLocal
