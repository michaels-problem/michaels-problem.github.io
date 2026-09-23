import AutomaticContinuity.HolomorphicGraphUnion

set_option autoImplicit false

/-!
# Actual polynomial cutoffs for the forbidden graph and a section

The existing graph-offset approximation and polynomial-function-algebra
cutoff construction supply a particular polynomial, with arbitrary positive
tolerance. Its complement has the orientation used by the radial push:
small on the section graph and near one on the compact obstacle.
-/

noncomputable section

namespace AutomaticContinuity.FlagGraphCutoff

open Set MvPolynomial FlagPolynomialSeparation HolomorphicGraphConvexity
open HolomorphicGraphUnion

theorem exists_graph_separator {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    {K : Set (Point n)} (hKc : IsCompact K)
    (hK : IsPolynomiallyConvexOf coordinates K)
    (hKbase : ∀ y ∈ K, y.1 ∈ polydisc n R)
    (h : FinitePoint n → ℂ × ℂ) {U : Set (FinitePoint n)} (hU : IsOpen U)
    (hKU : polydisc n R ⊆ U) (hh : DifferentiableOn ℂ h U)
    (hdisj : Disjoint K (sectionGraph n R h)) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : Polynomial n,
      (∀ p ∈ polydisc n R, ‖evaluate (p, h p) q‖ < ε) ∧
      (∀ z ∈ K, ‖evaluate z q - 1‖ < ε) := by
  classical
  let L : Set (Point n) := sectionGraph n R h
  let K' : Set (Variables n → ℂ) := coordinates '' K
  let L' : Set (Variables n → ℂ) := coordinates '' L
  let S : Set (Variables n → ℂ) := K' ∪ L'
  have hhc : ContinuousOn h (polydisc n R) := (hh.mono hKU).continuousOn
  have hLc : IsCompact L := isCompact_sectionGraph hR hhc
  have hK'c : IsCompact K' := hKc.image (continuous_coordinates n)
  have hL'c : IsCompact L' := hLc.image (continuous_coordinates n)
  let : CompactSpace K' := isCompact_iff_compactSpace.mp hK'c
  let : CompactSpace S := isCompact_iff_compactSpace.mp (hK'c.union hL'c)
  have hKS : K' ⊆ S := subset_union_left
  have hLS : L' ⊆ S := subset_union_right
  have hK' : IsPolynomiallyConvexOf (fun z : Variables n → ℂ => z) K' :=
    (isPolynomiallyConvex_coordinates_image_iff K).mpr hK
  have hbase : ∀ z ∈ S, sourceCoordinates z ∈ polydisc n R := by
    rintro z (hz | hz)
    · obtain ⟨y, hy, rfl⟩ := hz
      exact hKbase y hy
    · obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨x, hx, rfl⟩ := hy
      exact hx
  let a : Bool → C(S, ℂ) := fun b =>
    ⟨fun z => graphOffset h b z.val, (continuousOn_graphOffset h hbase hhc b).domRestrict⟩
  have happrox : ∀ b ε, 0 < ε → ∃ p : Polynomial n,
      ∀ z : S, ‖eval z.val p - a b z‖ < ε := by
    intro b ε hε
    obtain ⟨p, hp⟩ := exists_polynomial_graphOffset_approx hR h hU hKU hh hbase b hε
    exact ⟨p, fun z => hp z z.property⟩
  have hzeroK : ∀ z : K', ∃ b, a b ⟨z.val, hKS z.property⟩ ≠ 0 := by
    intro z
    obtain ⟨y, hy, hyz⟩ := z.property
    by_contra hn
    push Not at hn
    have hf := hn false
    have hs := hn true
    change graphOffset h false z.val = 0 at hf
    change graphOffset h true z.val = 0 at hs
    rw [← hyz] at hf hs
    have hyh : y.2 = h y.1 := by
      apply Prod.ext
      · exact sub_eq_zero.mp hf
      · exact sub_eq_zero.mp hs
    have hyL : y ∈ sectionGraph n R h :=
      ⟨y.1, hKbase y hy, Prod.ext rfl hyh.symm⟩
    exact Set.disjoint_left.mp hdisj hy hyL
  have hzeroL : ∀ b (z : L'), a b ⟨z.val, hLS z.property⟩ = 0 := by
    intro b z
    obtain ⟨y, hy, hyz⟩ := z.property
    obtain ⟨x, hx, rfl⟩ := hy
    change graphOffset h b z.val = 0
    rw [← hyz]
    cases b
    · change (h x).1 - (h x).1 = 0
      exact sub_self _
    · change (h x).2 - (h x).2 = 0
      exact sub_self _
  obtain ⟨q, hqK, hqL⟩ := PolynomialFunctionCutoff.exists_polynomial_cutoff_of_approx
    K' S L' hKS hLS hK' a happrox hzeroK hzeroL hε
  refine ⟨1 - q, ?_, ?_⟩
  · intro p hp
    change ‖eval (coordinates (p, h p)) (1 - q)‖ < ε
    rw [map_sub, map_one, norm_sub_rev]
    exact hqL (coordinates (p, h p)) ⟨(p, h p), ⟨p, hp, rfl⟩, rfl⟩
  · intro z hz
    change ‖eval (coordinates z) (1 - q) - 1‖ < ε
    rw [map_sub, map_one]
    have heq : (1 : ℂ) - eval (coordinates z) q - 1 = -eval (coordinates z) q := by ring
    rw [heq, norm_neg]
    exact hqK (coordinates z) ⟨z, hz, rfl⟩

/-- The actual forbidden flag graph has a polynomial cutoff against every
admissible section holomorphic near the base polydisc. -/
theorem exists_forbidden_graph_separator {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (h : FinitePoint n → ℂ × ℂ) {U : Set (FinitePoint n)} (hU : IsOpen U)
    (hKU : polydisc n R ⊆ U) (hh : DifferentiableOn ℂ h U)
    (hadm : ∀ z ∈ polydisc n R, (z, h z) ∈ FlagTotalSpace.totalSet n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : Polynomial n,
      (∀ p ∈ polydisc n R, ‖evaluate (p, h p) q‖ < ε) ∧
      (∀ z ∈ FlagTotalSpace.compactForbiddenGraph n R, ‖evaluate z q - 1‖ < ε) := by
  apply exists_graph_separator hR
    (FlagTotalSpace.isCompact_compactForbiddenGraph n hR)
    (isPolynomiallyConvex_compactForbiddenGraph n hR)
    (fun y hy => (FlagTotalSpace.mem_compactForbiddenGraph_iff.mp hy).1)
    h hU hKU hh
  · apply Set.disjoint_left.mpr
    intro y hyK hyG
    obtain ⟨z, hz, rfl⟩ := hyG
    exact (hadm z hz) hyK.1
  · exact hε

end AutomaticContinuity.FlagGraphCutoff
