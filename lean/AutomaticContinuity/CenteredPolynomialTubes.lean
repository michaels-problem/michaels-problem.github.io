import AutomaticContinuity.CenteredPolynomialFamily
import AutomaticContinuity.CompactCutoffTubes
import AutomaticContinuity.EuclideanBallGeometry
import Mathlib.Topology.Algebra.MvPolynomial

set_option autoImplicit false

/-!
# A protected cylinder from a separator near a section graph

The polynomial is translated by the actual section. A strict initial margin
on its compact graph yields one positive Euclidean fibre radius uniformly
over the compact base, before any cutoff amplification is performed.
-/

noncomputable section

namespace AutomaticContinuity.CenteredPolynomialFamily

open MvPolynomial Set Metric

variable {σ ι P : Type*}

def pairCoordinates (w : ℂ × ℂ) : Fin 2 → ℂ := ![w.1, w.2]

def centeredValue (q : MvPolynomial (σ ⊕ ι) ℂ) (j : ι → Fin 2)
    (b : P → σ → ℂ) (h : P → ι → ℂ) (z : P × (ℂ × ℂ)) : ℂ :=
  eval (pairCoordinates z.2) (centered q j b h z.1)

theorem centeredValue_eq (q : MvPolynomial (σ ⊕ ι) ℂ) (j : ι → Fin 2)
    (b : P → σ → ℂ) (h : P → ι → ℂ) (z : P × (ℂ × ℂ)) :
    centeredValue q j b h z =
      eval (Sum.elim (b z.1) (fun i => pairCoordinates z.2 (j i) + h z.1 i)) q :=
  eval_centered q j b h z.1 (pairCoordinates z.2)

@[simp] theorem centeredValue_zero (q : MvPolynomial (σ ⊕ ι) ℂ) (j : ι → Fin 2)
    (b : P → σ → ℂ) (h : P → ι → ℂ) (p : P) :
    centeredValue q j b h (p, 0) = eval (Sum.elim (b p) (h p)) q := by
  rw [centeredValue_eq]
  apply congrArg (fun x => eval x q)
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    generalize hji : j i = k
    fin_cases k <;> simp [pairCoordinates, hji]

section Continuity

variable [TopologicalSpace P]

theorem continuousOn_centeredValue (q : MvPolynomial (σ ⊕ ι) ℂ) (j : ι → Fin 2)
    (b : P → σ → ℂ) (h : P → ι → ℂ) {U : Set P}
    (hb : ∀ i, ContinuousOn (fun p => b p i) U)
    (hh : ∀ i, ContinuousOn (fun p => h p i) U) :
    ContinuousOn (centeredValue q j b h) (U ×ˢ univ) := by
  have he : centeredValue q j b h = fun z : P × (ℂ × ℂ) =>
      eval (Sum.elim (b z.1) (fun i => pairCoordinates z.2 (j i) + h z.1 i)) q :=
    funext (centeredValue_eq q j b h)
  rw [he]
  apply q.continuous_eval.comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  cases i with
  | inl i => exact (hb i).comp continuous_fst.continuousOn (fun _ hz => hz.1)
  | inr i =>
    have hw : Continuous (fun z : P × (ℂ × ℂ) => pairCoordinates z.2 (j i)) := by
      unfold pairCoordinates
      generalize hji : j i = k
      fin_cases k <;> fun_prop
    exact hw.continuousOn.add ((hh i).comp continuous_fst.continuousOn (fun _ hz => hz.1))

end Continuity

section CompactRadius

variable [PseudoMetricSpace P]

/-- A generic local-continuity form of the initial protected cylinder. -/
theorem exists_small_euclidean_cylinder (f : P × (ℂ × ℂ) → ℂ)
    {L U : Set P} (hL : IsCompact L) (hU : IsOpen U) (hLU : L ⊆ U)
    (hf : ContinuousOn f (U ×ˢ univ))
    (hsmall : ∀ p ∈ L, ‖f (p, 0)‖ ≤ 1 / 32) :
    ∃ a : ℝ, 0 < a ∧ ∀ p ∈ L, ∀ w : ℂ × ℂ,
      euclideanPairNorm w ≤ a → ‖f (p, w)‖ < 1 / 16 := by
  let K : Set (P × (ℂ × ℂ)) := L ×ˢ {0}
  have hK : IsCompact K := hL.prod isCompact_singleton
  have hKU : K ⊆ U ×ˢ univ := fun z hz => ⟨hLU hz.1, mem_univ _⟩
  have htwo : ∀ z ∈ K, ‖(2 : ℂ) * f z - 0‖ ≤ 1 / 16 := by
    rintro ⟨p, w⟩ ⟨hp, hw⟩
    have hw0 : w = 0 := mem_singleton_iff.mp hw
    subst w
    norm_num only [sub_zero, norm_mul, Complex.norm_ofNat]
    linarith [hsmall p hp]
  obtain ⟨a, ha, _, hbound⟩ := CompactCutoffTubes.exists_tube
    (fun z => (2 : ℂ) * f z) hK (hU.prod isOpen_univ) hKU
    (continuousOn_const.mul hf) 0 htwo
  refine ⟨a, ha, ?_⟩
  intro p hp w hw
  have hdist : dist (p, w) (p, (0 : ℂ × ℂ)) ≤ a := by
    simp only [Prod.dist_eq, dist_self, dist_zero_right, max_eq_right (norm_nonneg _)]
    exact (norm_le_euclideanPairNorm w).trans hw
  have hmem : (p, w) ∈ cthickening a K :=
    mem_cthickening_of_dist_le (p, w) (p, 0) a K ⟨hp, mem_singleton _⟩ hdist
  have hb := hbound (p, w) hmem
  norm_num only [sub_zero, norm_mul, Complex.norm_ofNat] at hb
  linarith

/-- An actual separator on the section graph gives the fixed positive
protected radius needed by the radial cutoff construction. -/
theorem exists_centered_small_cylinder (q : MvPolynomial (σ ⊕ ι) ℂ) (j : ι → Fin 2)
    (b : P → σ → ℂ) (h : P → ι → ℂ) {L U : Set P}
    (hL : IsCompact L) (hU : IsOpen U) (hLU : L ⊆ U)
    (hb : ∀ i, ContinuousOn (fun p => b p i) U)
    (hh : ∀ i, ContinuousOn (fun p => h p i) U)
    (hq : ∀ p ∈ L, ‖eval (Sum.elim (b p) (h p)) q‖ ≤ 1 / 32) :
    ∃ a : ℝ, 0 < a ∧ ∀ p ∈ L, ∀ w : ℂ × ℂ,
      euclideanPairNorm w ≤ a → ‖centeredValue q j b h (p, w)‖ < 1 / 16 := by
  exact exists_small_euclidean_cylinder (centeredValue q j b h) hL hU hLU
    (continuousOn_centeredValue q j b h hb hh) (by simpa only [centeredValue_zero] using hq)

end CompactRadius

end AutomaticContinuity.CenteredPolynomialFamily
