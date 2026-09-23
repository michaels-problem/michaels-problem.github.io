import AutomaticContinuity.HolomorphicFlagContraction

set_option autoImplicit false

/-! # Convex compact approximation from the exact local stability input

The admissible holomorphic path, its uniform continuity, closedness of
approximability, and the large constant endpoint are proved ingredients.
Only the explicitly quantified local analytic stability assertion remains
as a premise of this assembly theorem.
-/

noncomputable section
namespace AutomaticContinuity.FlagSectionApproximation
open Set FlagTotalSpace HolomorphicFlagContraction

theorem approximable_largeValue {n : ℕ} (K L : Set (FinitePoint n)) :
    Approximable K L (fun _ => largeValue n) :=
  approximable_of_extension _ isOpen_univ (subset_univ L) (differentiableOn_const (largeValue n))
    (fun z _ => largeValue_admissible n z)

/-- Local openness at each already approximable admissible holomorphic germ
implies approximation for every admissible holomorphic germ on a compact
convex set. No local stability assertion is assumed for nonadmissible base
germs, and no stability assertion is silently obtained from a fibre family.
-/
theorem approximable_of_convex_local_stability {n : ℕ} {K L : Set (FinitePoint n)}
    (hK : IsCompact K) (hconv : Convex ℝ K)
    (hstable : ∀ g : FinitePoint n → Pair, HolomorphicNear K g →
      (∀ z ∈ K, (z,g z) ∈ totalSet n) → Approximable K L g →
      ∃ δ : ℝ, 0 < δ ∧ ∀ u : FinitePoint n → Pair,
        HolomorphicNear K u →
        (∀ z ∈ K, euclideanPairNorm (u z-g z) ≤ δ) → Approximable K L u)
    (h : FinitePoint n → Pair) (hhol : HolomorphicNear K h)
    (hadm : ∀ z ∈ K, (z,h z) ∈ totalSet n) : Approximable K L h := by
  rcases K.eq_empty_or_nonempty with hEmpty | hKne
  · apply (approximable_largeValue K L).congr
    intro z hz
    exact False.elim (by simp only [hEmpty,mem_empty_iff_false] at hz)
  obtain ⟨U,hU,hKU,hh⟩ := hhol
  obtain ⟨H,hH,h0,h1,hHhol,hHadm⟩ := exists_holomorphic_admissible_path
    hconv hKne hU hKU h hh hadm
  have hopen : OpenAlongPath K L H := openAlongPath_of_local_stability hK H hH
    (fun t => hHhol t.val t.property)
    (fun t ht => hstable (fun z => H (t.val,z)) (hHhol t.val t.property)
      (hHadm t.val t.property) ht)
  have hterminal : Approximable K L (fun z => H (1,z)) :=
    (approximable_largeValue K L).congr (fun z _ => (h1 z).symm)
  exact (approximable_zero_of_open_path hK L H hH hopen hterminal).congr
    (fun z _ => h0 z)

end AutomaticContinuity.FlagSectionApproximation
