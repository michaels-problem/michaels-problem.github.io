import AutomaticContinuity.CenteredPolynomialTubes

set_option autoImplicit false

/-!
# Initial radial data from an actual section-graph separator

Centering translates the actual compact obstacle by the actual section. A
polynomial separator with a 1/32 margin supplies a positive protected
Euclidean cylinder, preserves the near-one obstacle bound, and proves that
the centered obstacle lies strictly outside that cylinder.
-/

noncomputable section

namespace AutomaticContinuity.CenteredPolynomialFamily

open MvPolynomial Set FlagTotalSpace

variable {σ ι P : Type*}

def sectionCoordinates (j : ι → Fin 2) (h : P → ℂ × ℂ) (p : P) (i : ι) : ℂ :=
  pairCoordinates (h p) (j i)

def centerMap (h : P → ℂ × ℂ) (z : P × (ℂ × ℂ)) : P × (ℂ × ℂ) :=
  (z.1, z.2 - h z.1)

def centeredObstacle (h : P → ℂ × ℂ) (K : Set (P × (ℂ × ℂ))) : Set (P × (ℂ × ℂ)) :=
  centerMap h '' K

def originalValue (q : MvPolynomial (σ ⊕ ι) ℂ) (j : ι → Fin 2)
    (b : P → σ → ℂ) (z : P × (ℂ × ℂ)) : ℂ :=
  eval (Sum.elim (b z.1) (fun i => pairCoordinates z.2 (j i))) q

theorem centeredValue_centerMap (q : MvPolynomial (σ ⊕ ι) ℂ) (j : ι → Fin 2)
    (b : P → σ → ℂ) (h : P → ℂ × ℂ) (z : P × (ℂ × ℂ)) :
    centeredValue q j b (sectionCoordinates j h) (centerMap h z) = originalValue q j b z := by
  rw [centeredValue_eq]
  apply congrArg (fun x => eval x q)
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    simp only [Sum.elim_inr, centerMap, sectionCoordinates]
    generalize hji : j i = k
    fin_cases k <;> simp [pairCoordinates]

theorem centeredObstacle_base {L : Set P} {K : Set (P × (ℂ × ℂ))}
    (h : P → ℂ × ℂ) (hKL : K ⊆ L ×ˢ univ) :
    centeredObstacle h K ⊆ L ×ˢ univ := by
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨(hKL hz).1, mem_univ _⟩

theorem centeredObstacle_near_one (q : MvPolynomial (σ ⊕ ι) ℂ) (j : ι → Fin 2)
    (b : P → σ → ℂ) (h : P → ℂ × ℂ) {K : Set (P × (ℂ × ℂ))} {ε : ℝ}
    (hq : ∀ z ∈ K, ‖originalValue q j b z - 1‖ ≤ ε) :
    ∀ z ∈ centeredObstacle h K, ‖centeredValue q j b (sectionCoordinates j h) z - 1‖ ≤ ε := by
  rintro _ ⟨z, hz, rfl⟩
  simpa only [centeredValue_centerMap] using hq z hz

section Topology

variable [PseudoMetricSpace P]

theorem continuousOn_sectionCoordinates (j : ι → Fin 2) (h : P → ℂ × ℂ)
    {U : Set P} (hh : ContinuousOn h U) (i : ι) :
    ContinuousOn (fun p => sectionCoordinates j h p i) U := by
  have hc : Continuous (fun w : ℂ × ℂ => pairCoordinates w (j i)) := by
    unfold pairCoordinates
    generalize hji : j i = k
    fin_cases k <;> fun_prop
  exact hc.comp_continuousOn hh

theorem continuousCoefficientsOn_section_centered
    (q : MvPolynomial (σ ⊕ ι) ℂ) (j : ι → Fin 2)
    (b : P → σ → ℂ) (h : P → ℂ × ℂ) {U : Set P}
    (hb : ∀ i, ContinuousOn (fun p => b p i) U) (hh : ContinuousOn h U) :
    PolynomialFamilyRegularity.ContinuousCoefficientsOn
      (centered q j b (sectionCoordinates j h)) U :=
  continuousCoefficientsOn_centered q j b _ hb (continuousOn_sectionCoordinates j h hh)

theorem isCompact_centeredObstacle (h : P → ℂ × ℂ) {K : Set (P × (ℂ × ℂ))}
    {U : Set P} (hK : IsCompact K) (hKU : ∀ z ∈ K, z.1 ∈ U)
    (hh : ContinuousOn h U) : IsCompact (centeredObstacle h K) := by
  apply hK.image_of_continuousOn
  exact continuous_fst.continuousOn.prodMk
    (continuous_snd.continuousOn.sub (hh.comp continuous_fst.continuousOn hKU))

/-- This is the concrete initial data required by the radial cutoff step.
No existence of a polynomial separator is assumed as a new axiom: the input
is a particular polynomial satisfying the two displayed scalar inequalities. -/
theorem exists_centered_separator_data
    (q : MvPolynomial (σ ⊕ ι) ℂ) (j : ι → Fin 2)
    (b : P → σ → ℂ) (h : P → ℂ × ℂ)
    {L U : Set P} {K : Set (P × (ℂ × ℂ))}
    (hL : IsCompact L) (hK : IsCompact K) (hU : IsOpen U)
    (hLU : L ⊆ U) (hKL : K ⊆ L ×ˢ univ)
    (hb : ∀ i, ContinuousOn (fun p => b p i) U) (hh : ContinuousOn h U)
    (hgraph : ∀ p ∈ L,
      ‖eval (Sum.elim (b p) (sectionCoordinates j h p)) q‖ ≤ 1 / 32)
    (hobstacle : ∀ z ∈ K, ‖originalValue q j b z - 1‖ ≤ 1 / 32) :
    ∃ a : ℝ, 0 < a ∧ IsCompact (centeredObstacle h K) ∧
      centeredObstacle h K ⊆ L ×ˢ univ ∧
      (∀ z ∈ L ×ˢ closedEuclideanBall a,
        ‖centeredValue q j b (sectionCoordinates j h) z‖ ≤ 1 / 16) ∧
      (∀ z ∈ centeredObstacle h K,
        ‖centeredValue q j b (sectionCoordinates j h) z - 1‖ ≤ 1 / 32) ∧
      (∀ z ∈ centeredObstacle h K, a < euclideanPairNorm z.2) := by
  obtain ⟨a, ha, hsmall⟩ := exists_centered_small_cylinder q j b (sectionCoordinates j h)
    hL hU hLU hb (continuousOn_sectionCoordinates j h hh) hgraph
  have hbase := centeredObstacle_base h hKL
  have hnear := centeredObstacle_near_one q j b h hobstacle
  refine ⟨a, ha, isCompact_centeredObstacle h hK (fun z hz => hLU (hKL hz).1) hh,
    hbase, ?_, hnear, ?_⟩
  · intro z hz
    exact (hsmall z.1 hz.1 z.2 hz.2).le
  · intro z hz
    by_contra hnot
    have hnorm : euclideanPairNorm z.2 ≤ a := le_of_not_gt hnot
    have hs := hsmall z.1 (hbase hz).1 z.2 hnorm
    have hn := hnear z hz
    have ht := norm_sub_le (centeredValue q j b (sectionCoordinates j h) z)
      (centeredValue q j b (sectionCoordinates j h) z - 1)
    rw [sub_sub_cancel, norm_one] at ht
    linarith

end Topology

section Holomorphic

variable [NormedAddCommGroup P] [NormedSpace ℂ P]

theorem differentiableOn_sectionCoordinates (j : ι → Fin 2) (h : P → ℂ × ℂ)
    {U : Set P} (hh : DifferentiableOn ℂ h U) (i : ι) :
    DifferentiableOn ℂ (fun p => sectionCoordinates j h p i) U := by
  have hd : Differentiable ℂ (fun w : ℂ × ℂ => pairCoordinates w (j i)) := by
    unfold pairCoordinates
    generalize hji : j i = k
    fin_cases k
    · exact differentiable_fst
    · exact differentiable_snd
  exact hd.comp_differentiableOn hh

theorem holomorphicCoefficientsOn_section_centered
    (q : MvPolynomial (σ ⊕ ι) ℂ) (j : ι → Fin 2)
    (b : P → σ → ℂ) (h : P → ℂ × ℂ) {U : Set P}
    (hb : ∀ i, DifferentiableOn ℂ (fun p => b p i) U) (hh : DifferentiableOn ℂ h U) :
    PolynomialFamilyRegularity.HolomorphicCoefficientsOn
      (centered q j b (sectionCoordinates j h)) U :=
  holomorphicCoefficientsOn_centered q j b _ hb (differentiableOn_sectionCoordinates j h hh)

end Holomorphic

end AutomaticContinuity.CenteredPolynomialFamily
