import AutomaticContinuity.FlagGraphCutoff

set_option autoImplicit false

/-!
# Forbidden flag graphs over arbitrary polynomially convex compact bases

Restriction of the actual forbidden graph requires only compactness and
polynomial convexity of the base. The graph separator additionally uses
explicit polynomial approximation of the two components of the section.
No holomorphic approximation theorem on a general compact set is assumed
implicitly in this interface.
-/

noncomputable section

namespace AutomaticContinuity.CompactBaseFlagGeometry

open Set MvPolynomial FlagPolynomialSeparation FlagTotalSpace
open HolomorphicGraphUnion HolomorphicGraphConvexity

def forbiddenGraph (n : ℕ) (L : Set (FinitePoint n)) : Set (Point n) :=
  forbiddenSet n ∩ (L ×ˢ univ)

def sectionGraphOn {n : ℕ} (L : Set (FinitePoint n))
    (h : FinitePoint n → ℂ × ℂ) : Set (Point n) := (fun z => (z, h z)) '' L

theorem exists_containing_polydisc {n : ℕ} {L : Set (FinitePoint n)} (hL : IsCompact L) :
    ∃ R : ℝ, 0 ≤ R ∧ L ⊆ polydisc n R := by
  obtain ⟨R, hR⟩ := hL.exists_bound_of_continuousOn (continuousOn_id : ContinuousOn (fun z : FinitePoint n => z) L)
  refine ⟨max 0 R, le_max_left _ _, ?_⟩
  intro z hz j
  exact (norm_le_pi_norm z j).trans ((hR z hz).trans (le_max_right _ _))

theorem forbiddenGraph_eq_inter {n : ℕ} {L : Set (FinitePoint n)} {R : ℝ}
    (hLR : L ⊆ polydisc n R) :
    forbiddenGraph n L = compactForbiddenGraph n R ∩ (L ×ˢ univ) := by
  ext z
  constructor
  · rintro ⟨hz, hzL, hzU⟩
    exact ⟨⟨hz, hLR hzL, hzU⟩, hzL, hzU⟩
  · rintro ⟨⟨hz, _, _⟩, hzL, hzU⟩
    exact ⟨hz, hzL, hzU⟩

theorem isCompact_forbiddenGraph {n : ℕ} {L : Set (FinitePoint n)} (hL : IsCompact L) :
    IsCompact (forbiddenGraph n L) := by
  obtain ⟨R, hR, hLR⟩ := exists_containing_polydisc hL
  rw [forbiddenGraph_eq_inter hLR]
  exact (isCompact_compactForbiddenGraph n hR).inter_right (hL.isClosed.prod isClosed_univ)

theorem isPolynomiallyConvex_forbiddenGraph {n : ℕ} {L : Set (FinitePoint n)}
    (hLc : IsCompact L) (hL : IsPolynomiallyConvexOf (fun z : FinitePoint n => z) L) :
    IsPolynomiallyConvexOf coordinates (forbiddenGraph n L) := by
  obtain ⟨R, hR, hLR⟩ := exists_containing_polydisc hLc
  apply (isPolynomiallyConvexOf_iff_separation _ _).mpr
  intro z hz
  by_cases hzR : z ∈ compactForbiddenGraph n R
  · have hzL : z.1 ∉ L := fun hzL => hz ⟨hzR.1, hzL, mem_univ _⟩
    obtain ⟨p, C, hp, hpz⟩ := (isPolynomiallyConvexOf_iff_separation _ _).mp hL z.1 hzL
    refine ⟨rename Sum.inl p, C, ?_, ?_⟩
    · intro y hy
      simpa only [eval_rename_source] using hp y.1 hy.2.1
    · simpa only [eval_rename_source] using hpz
  · obtain ⟨p, C, hp, hpz⟩ := (isPolynomiallyConvexOf_iff_separation _ _).mp
      (isPolynomiallyConvex_compactForbiddenGraph n hR) z hzR
    exact ⟨p, C, fun y hy => hp y ⟨hy.1, hLR hy.2.1, mem_univ _⟩, hpz⟩

theorem continuousOn_graphOffset_on {n : ℕ} {L : Set (FinitePoint n)}
    (h : FinitePoint n → ℂ × ℂ) {S : Set (Variables n → ℂ)}
    (hbase : ∀ z ∈ S, sourceCoordinates z ∈ L) (hh : ContinuousOn h L) (b : Bool) :
    ContinuousOn (graphOffset h b) S := by
  have hc : ContinuousOn (fun z => h (sourceCoordinates z)) S :=
    hh.comp (continuous_sourceCoordinates n).continuousOn hbase
  cases b
  · exact (continuous_apply (Sum.inr false)).continuousOn.sub hc.fst
  · exact (continuous_apply (Sum.inr true)).continuousOn.sub hc.snd

theorem exists_polynomial_graphOffset_approx_on {n : ℕ} {L : Set (FinitePoint n)}
    (h : FinitePoint n → ℂ × ℂ)
    (happrox : ∀ b : Bool, ∀ ε > 0, ∃ p : MvPolynomial (Fin n) ℂ,
      ∀ z ∈ L, ‖eval z p - (if b then (h z).2 else (h z).1)‖ < ε)
    {S : Set (Variables n → ℂ)} (hbase : ∀ z ∈ S, sourceCoordinates z ∈ L)
    (b : Bool) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial n, ∀ z ∈ S, ‖eval z p - graphOffset h b z‖ < ε := by
  obtain ⟨p, hp⟩ := happrox b ε hε
  refine ⟨X (Sum.inr b) - rename Sum.inl p, ?_⟩
  intro z hz
  have heq : eval z (X (Sum.inr b) - rename Sum.inl p) - graphOffset h b z =
      -(eval (sourceCoordinates z) p - (if b then (h (sourceCoordinates z)).2 else
        (h (sourceCoordinates z)).1)) := by
    simp only [map_sub, eval_X, eval_rename, graphOffset]
    change z (Sum.inr b) - eval (sourceCoordinates z) p -
      (z (Sum.inr b) - _) = _
    ring
  rw [heq, norm_neg]
  exact hp _ (hbase z hz)

theorem exists_graph_separator {n : ℕ} {L : Set (FinitePoint n)}
    (hLc : IsCompact L) {K : Set (Point n)} (hKc : IsCompact K)
    (hK : IsPolynomiallyConvexOf coordinates K) (hKbase : ∀ y ∈ K, y.1 ∈ L)
    (h : FinitePoint n → ℂ × ℂ) (hh : ContinuousOn h L)
    (happrox : ∀ b : Bool, ∀ ε > 0, ∃ p : MvPolynomial (Fin n) ℂ,
      ∀ z ∈ L, ‖eval z p - (if b then (h z).2 else (h z).1)‖ < ε)
    (hdisj : Disjoint K (sectionGraphOn L h)) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : Polynomial n,
      (∀ p ∈ L, ‖evaluate (p, h p) q‖ < ε) ∧
      ∀ z ∈ K, ‖evaluate z q - 1‖ < ε := by
  classical
  let G : Set (Point n) := sectionGraphOn L h
  let K' : Set (Variables n → ℂ) := coordinates '' K
  let G' : Set (Variables n → ℂ) := coordinates '' G
  let S : Set (Variables n → ℂ) := K' ∪ G'
  have hGc : IsCompact G := hLc.image_of_continuousOn (continuousOn_id.prodMk hh)
  have hK'c : IsCompact K' := hKc.image (continuous_coordinates n)
  have hG'c : IsCompact G' := hGc.image (continuous_coordinates n)
  let : CompactSpace K' := isCompact_iff_compactSpace.mp hK'c
  let : CompactSpace S := isCompact_iff_compactSpace.mp (hK'c.union hG'c)
  have hKS : K' ⊆ S := subset_union_left
  have hGS : G' ⊆ S := subset_union_right
  have hK' : IsPolynomiallyConvexOf (fun z : Variables n → ℂ => z) K' :=
    (isPolynomiallyConvex_coordinates_image_iff K).mpr hK
  have hbase : ∀ z ∈ S, sourceCoordinates z ∈ L := by
    rintro z (hz | hz)
    · obtain ⟨y, hy, rfl⟩ := hz
      exact hKbase y hy
    · obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨x, hx, rfl⟩ := hy
      exact hx
  let a : Bool → C(S, ℂ) := fun b =>
    ⟨fun z => graphOffset h b z.val, (continuousOn_graphOffset_on h hbase hh b).domRestrict⟩
  have happ : ∀ b ε, 0 < ε → ∃ p : Polynomial n,
      ∀ z : S, ‖eval z.val p - a b z‖ < ε := by
    intro b ε hε
    obtain ⟨p, hp⟩ := exists_polynomial_graphOffset_approx_on h happrox hbase b hε
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
    exact Set.disjoint_left.mp hdisj hy ⟨y.1, hKbase y hy, Prod.ext rfl hyh.symm⟩
  have hzeroG : ∀ b (z : G'), a b ⟨z.val, hGS z.property⟩ = 0 := by
    intro b z
    obtain ⟨y, hy, hyz⟩ := z.property
    obtain ⟨x, hx, rfl⟩ := hy
    change graphOffset h b z.val = 0
    rw [← hyz]
    cases b <;> exact sub_self _
  obtain ⟨q, hqK, hqG⟩ := PolynomialFunctionCutoff.exists_polynomial_cutoff_of_approx
    K' S G' hKS hGS hK' a happ hzeroK hzeroG hε
  refine ⟨1 - q, ?_, ?_⟩
  · intro p hp
    change ‖eval (coordinates (p, h p)) (1 - q)‖ < ε
    rw [map_sub, map_one, norm_sub_rev]
    exact hqG _ ⟨(p, h p), ⟨p, hp, rfl⟩, rfl⟩
  · intro z hz
    change ‖eval (coordinates z) (1 - q) - 1‖ < ε
    rw [map_sub, map_one]
    have heq : (1 : ℂ) - eval (coordinates z) q - 1 = -eval (coordinates z) q := by ring
    rw [heq, norm_neg]
    exact hqK _ ⟨z, hz, rfl⟩

theorem exists_forbidden_graph_separator {n : ℕ} {L : Set (FinitePoint n)}
    (hLc : IsCompact L) (hL : IsPolynomiallyConvexOf (fun z : FinitePoint n => z) L)
    (h : FinitePoint n → ℂ × ℂ) (hh : ContinuousOn h L)
    (hadm : ∀ z ∈ L, (z, h z) ∈ totalSet n)
    (happrox : ∀ b : Bool, ∀ ε > 0, ∃ p : MvPolynomial (Fin n) ℂ,
      ∀ z ∈ L, ‖eval z p - (if b then (h z).2 else (h z).1)‖ < ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : Polynomial n,
      (∀ p ∈ L, ‖evaluate (p, h p) q‖ < ε) ∧
      ∀ z ∈ forbiddenGraph n L, ‖evaluate z q - 1‖ < ε := by
  apply exists_graph_separator hLc (isCompact_forbiddenGraph hLc)
    (isPolynomiallyConvex_forbiddenGraph hLc hL) (fun y hy => hy.2.1)
    h hh happrox _ hε
  apply Set.disjoint_left.mpr
  intro y hyK hyG
  obtain ⟨z, hz, rfl⟩ := hyG
  exact (hadm z hz) hyK.1

end AutomaticContinuity.CompactBaseFlagGeometry
