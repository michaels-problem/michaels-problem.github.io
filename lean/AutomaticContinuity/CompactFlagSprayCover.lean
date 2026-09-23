import AutomaticContinuity.FlagLocalSprays

set_option autoImplicit false

/-!
# Finite entire-spray covers of compact admissible flag graphs

Compactness extracts an actual finite list of the proved local vertical sprays.
Each member preserves all constraints for every entire parameter, and its
parameter derivative is the identity. No compatibility between distinct
members on their overlaps, or holomorphic gluing, is asserted.
-/

noncomputable section

namespace AutomaticContinuity.CompactFlagSprayCover

open Set FlagTotalSpace FlagLocalSprays

/-- One actual local vertical spray with all its geometric and analytic data. -/
structure Spray (n : ℕ) where
  domain : Set (Point n)
  isOpen_domain : IsOpen domain
  map : Point n × Pair → Pair
  differentiable : Differentiable ℂ map
  zero_section : ∀ x : Point n, map (x, 0) = x.2
  injective_fiber : ∀ x : Point n, Function.Injective (fun t => map (x, t))
  derivative : ∀ x : Point n, HasFDerivAt (fun t => map (x, t))
    (ContinuousLinearMap.id ℂ Pair) 0
  admissible : ∀ x ∈ domain, ∀ t : Pair, (x.1, map (x, t)) ∈ totalSet n

theorem Spray.domain_subset_totalSet {n : ℕ} (S : Spray n) : S.domain ⊆ totalSet n := by
  intro x hx
  simpa only [S.zero_section, Prod.mk.eta] using S.admissible x hx 0

theorem exists_spray (n : ℕ) (q : Point n) (hq : q ∈ totalSet n) :
    ∃ S : Spray n, q ∈ S.domain := by
  obtain ⟨W, hW, hqW, S, hS, hS0, hSinj, hSd, hSout⟩ :=
    exists_normalized_vertical_spray n q hq
  exact ⟨⟨W, hW, S, hS, hS0, hSinj, hSd, hSout⟩, hqW⟩

/-- An actual finite spray cover of an arbitrary compact subset of the total
space, including the empty compact set. -/
theorem exists_finite_cover (n : ℕ) (K : Set (Point n)) (hK : IsCompact K)
    (hKZ : K ⊆ totalSet n) :
    ∃ N : ℕ, ∃ S : Fin N → Spray n,
      ∀ x ∈ K, ∃ i : Fin N, x ∈ (S i).domain := by
  classical
  choose D hD using fun q : K => exists_spray n q (hKZ q.property)
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun q : K => (D q).domain)
    (fun q => (D q).isOpen_domain) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hD ⟨x, hx⟩⟩)
  let e : Fin (Fintype.card ↥s) ≃ ↥s := (Fintype.equivFin ↥s).symm
  refine ⟨Fintype.card ↥s, fun i => D (e i).val, ?_⟩
  intro x hx
  obtain ⟨q, hxq⟩ := mem_iUnion.mp (hs hx)
  obtain ⟨hqs, hxq⟩ := mem_iUnion.mp hxq
  refine ⟨e.symm ⟨q, hqs⟩, ?_⟩
  simpa only [e.apply_symm_apply] using hxq

/-- The graph of a continuous admissible section over a compact source has a
finite cover by actual entire-parameter vertical sprays. -/
theorem exists_finite_graph_cover (n : ℕ) (K : Set (FinitePoint n))
    (hK : IsCompact K) (h : FinitePoint n → Pair) (hh : ContinuousOn h K)
    (hadm : ∀ z ∈ K, (z, h z) ∈ totalSet n) :
    ∃ N : ℕ, ∃ S : Fin N → Spray n,
      ∀ z ∈ K, ∃ i : Fin N, (z, h z) ∈ (S i).domain := by
  have hgraph : IsCompact ((fun z => (z, h z)) '' K) :=
    hK.image_of_continuousOn (continuousOn_id.prodMk hh)
  have hsubset : ((fun z => (z, h z)) '' K) ⊆ totalSet n := by
    rintro _ ⟨z, hz, rfl⟩
    exact hadm z hz
  obtain ⟨N, S, hS⟩ := exists_finite_cover n _ hgraph hsubset
  exact ⟨N, S, fun z hz => hS (z, h z) ⟨z, hz, rfl⟩⟩

end AutomaticContinuity.CompactFlagSprayCover
