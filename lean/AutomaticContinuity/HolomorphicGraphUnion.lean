import AutomaticContinuity.HolomorphicGraphConvexity
import AutomaticContinuity.FlagCoordinateEquivalence
import AutomaticContinuity.PolynomialFunctionCutoff
import AutomaticContinuity.PolynomialConvexUnion

set_option autoImplicit false

/-!
# Polynomially convex unions with holomorphic section graphs

The graph offsets are actual functions of all source and target coordinates.
Their uniform polynomial approximation comes from scalar approximation of the
section on its base polydisc, with no polynomial assumption on the section.
-/

noncomputable section

namespace AutomaticContinuity.HolomorphicGraphUnion

open Set MvPolynomial FlagPolynomialSeparation HolomorphicGraphConvexity

def sourceCoordinates {n : ℕ} (z : Variables n → ℂ) : FinitePoint n :=
  fun j => z (Sum.inl j)

def graphOffset {n : ℕ} (h : FinitePoint n → ℂ × ℂ) (b : Bool)
    (z : Variables n → ℂ) : ℂ :=
  z (Sum.inr b) - if b then (h (sourceCoordinates z)).2 else (h (sourceCoordinates z)).1

theorem continuous_sourceCoordinates (n : ℕ) : Continuous (@sourceCoordinates n) :=
  continuous_pi fun j => continuous_apply (Sum.inl j)

@[simp] theorem sourceCoordinates_coordinates {n : ℕ} (y : Point n) :
    sourceCoordinates (coordinates y) = y.1 := rfl

theorem continuousOn_graphOffset {n : ℕ} {R : ℝ}
    (h : FinitePoint n → ℂ × ℂ) {S : Set (Variables n → ℂ)}
    (hbase : ∀ z ∈ S, sourceCoordinates z ∈ polydisc n R)
    (hh : ContinuousOn h (polydisc n R)) (b : Bool) :
    ContinuousOn (graphOffset h b) S := by
  have hc : ContinuousOn (fun z => h (sourceCoordinates z)) S :=
    hh.comp (continuous_sourceCoordinates n).continuousOn hbase
  cases b
  · exact (continuous_apply (Sum.inr false)).continuousOn.sub hc.fst
  · exact (continuous_apply (Sum.inr true)).continuousOn.sub hc.snd

theorem exists_polynomial_graphOffset_approx {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (h : FinitePoint n → ℂ × ℂ) {U : Set (FinitePoint n)} (hU : IsOpen U)
    (hKU : polydisc n R ⊆ U) (hh : DifferentiableOn ℂ h U)
    {S : Set (Variables n → ℂ)}
    (hbase : ∀ z ∈ S, sourceCoordinates z ∈ polydisc n R)
    (b : Bool) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial n, ∀ z ∈ S, ‖eval z p - graphOffset h b z‖ < ε := by
  let f : FinitePoint n → ℂ := fun z => if b then (h z).2 else (h z).1
  have hf : DifferentiableOn ℂ f U := by
    cases b
    · exact hh.fst
    · exact hh.snd
  obtain ⟨p, hp⟩ := FiniteCauchy.exists_polynomial_approx_on_polydisc
    hR f hU hKU hf hε
  refine ⟨X (Sum.inr b) - rename Sum.inl p, ?_⟩
  intro z hz
  have heq : eval z (X (Sum.inr b) - rename Sum.inl p) - graphOffset h b z =
      -(eval (sourceCoordinates z) p - f (sourceCoordinates z)) := by
    simp only [map_sub, eval_X, eval_rename]
    change z (Sum.inr b) - eval (sourceCoordinates z) p -
      (z (Sum.inr b) - f (sourceCoordinates z)) = _
    ring
  rw [heq, norm_neg]
  exact hp _ (hbase z hz)

/-- A holomorphic section graph over the base polydisc can be joined to a
disjoint compact polynomially convex set above that same base. -/
theorem isPolynomiallyConvex_union_sectionGraph {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    {K : Set (Point n)} (hKc : IsCompact K)
    (hK : IsPolynomiallyConvexOf coordinates K)
    (hKbase : ∀ y ∈ K, y.1 ∈ polydisc n R)
    (h : FinitePoint n → ℂ × ℂ) {U : Set (FinitePoint n)} (hU : IsOpen U)
    (hKU : polydisc n R ⊆ U) (hh : DifferentiableOn ℂ h U)
    (hdisj : Disjoint K (sectionGraph n R h)) :
    IsPolynomiallyConvexOf coordinates (K ∪ sectionGraph n R h) := by
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
    K' S L' hKS hLS hK' a happrox hzeroK hzeroL
    (by norm_num : (0 : ℝ) < 1 / 8)
  apply PolynomialConvexUnion.isPolynomiallyConvexOf_union coordinates (continuous_coordinates n)
    hKc hLc hK (isPolynomiallyConvex_sectionGraph hR h hU hKU hh) q
  · intro y hy
    exact (hqK (coordinates y) ⟨y, hy, rfl⟩).le
  · intro y hy
    exact (hqL (coordinates y) ⟨y, hy, rfl⟩).le

/-- The actual compact forbidden flag graph joined to the graph of an
admissible holomorphic section is polynomially convex. -/
theorem isPolynomiallyConvex_forbidden_union_sectionGraph {n : ℕ} {R : ℝ}
    (hR : 0 ≤ R) (h : FinitePoint n → ℂ × ℂ)
    {U : Set (FinitePoint n)} (hU : IsOpen U) (hKU : polydisc n R ⊆ U)
    (hh : DifferentiableOn ℂ h U)
    (hadm : ∀ z ∈ polydisc n R, (z, h z) ∈ FlagTotalSpace.totalSet n) :
    IsPolynomiallyConvexOf coordinates
      (FlagTotalSpace.compactForbiddenGraph n R ∪ sectionGraph n R h) := by
  apply isPolynomiallyConvex_union_sectionGraph hR
    (FlagTotalSpace.isCompact_compactForbiddenGraph n hR)
    (isPolynomiallyConvex_compactForbiddenGraph n hR)
    (fun y hy => (FlagTotalSpace.mem_compactForbiddenGraph_iff.mp hy).1)
    h hU hKU hh
  apply Set.disjoint_left.mpr
  intro y hyK hyG
  obtain ⟨z, hz, rfl⟩ := hyG
  exact (hadm z hz) hyK.1

/-- The same union in ordinary source-plus-target coordinates, with the
standard identity-coordinate polynomial hull. -/
theorem isPolynomiallyConvex_coordinates_forbidden_union_sectionGraph
    {n : ℕ} {R : ℝ} (hR : 0 ≤ R) (h : FinitePoint n → ℂ × ℂ)
    {U : Set (FinitePoint n)} (hU : IsOpen U) (hKU : polydisc n R ⊆ U)
    (hh : DifferentiableOn ℂ h U)
    (hadm : ∀ z ∈ polydisc n R, (z, h z) ∈ FlagTotalSpace.totalSet n) :
    IsPolynomiallyConvexOf (fun z : Variables n → ℂ => z)
      (coordinates '' (FlagTotalSpace.compactForbiddenGraph n R ∪ sectionGraph n R h)) :=
  (isPolynomiallyConvex_coordinates_image_iff _).mpr
    (isPolynomiallyConvex_forbidden_union_sectionGraph hR h hU hKU hh hadm)

end AutomaticContinuity.HolomorphicGraphUnion
