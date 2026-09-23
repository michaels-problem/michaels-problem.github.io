import AutomaticContinuity.AdaptiveUniformLimit
import AutomaticContinuity.EuclideanBallGeometry
import AutomaticContinuity.SeveralVariableUniformLimit

set_option autoImplicit false

/-!
# Inverse limits on expanding parameter cylinders

Actual cumulative inverse maps with geometric increment bounds have one
ambient limit, uniform on each controlled cylinder. On every open base subset
the convergence is locally uniform, and locally holomorphic approximants have
a holomorphic limit. This does not assert that the limit lands in an entry
domain; that requires the separate inverse-tail containment estimate.
-/

noncomputable section

namespace AutomaticContinuity.NonautonomousInverseLimit

open Set Filter
open scoped Topology Uniformity

abbrev Pair := ℂ × ℂ

variable {P : Type*}

def cylinder (L : Set P) (r : ℝ) : Set (P × Pair) :=
  {z | z.1 ∈ L ∧ euclideanPairNorm z.2 ≤ r}

/-- No compactness or parameter topology is needed to construct the limit. -/
theorem exists_inverse_limit (F : ℕ → P → Pair ≃ₜ Pair) (L : Set P)
    (a b : ℕ → ℝ) (ha : Monotone a) (hcover : ∀ R : ℝ, ∃ n, R ≤ a n)
    (hbpos : ∀ n, 0 < b n) (hb : ∀ n, b (n + 1) ≤ b n / 2)
    (hstep : ∀ n z, z ∈ cylinder L (a n) →
      euclideanPairNorm ((F (n + 1) z.1).symm z.2 - (F n z.1).symm z.2) ≤ b n / 4) :
    ∃ G : P × Pair → Pair,
      (∀ m, TendstoUniformlyOn (fun n z => (F n z.1).symm z.2) G atTop
        (cylinder L (a m))) ∧
      ∀ m z, z ∈ cylinder L (a m) →
        euclideanPairNorm (G z - (F m z.1).symm z.2) ≤ b m := by
  classical
  let X := {z : P × Pair // z.1 ∈ L}
  let K : ℕ → Set X := fun n => {z | euclideanPairNorm z.val.2 ≤ a n}
  have hK : Monotone K := fun i j hij x hx => hx.trans (ha hij)
  have hX : ∀ x : X, ∃ n, x ∈ K n := fun x => hcover (euclideanPairNorm x.val.2)
  obtain ⟨g, hg, htail⟩ := AdaptiveUniformLimit.exists_limit K hK hX
    (fun n (z : X) => (F n z.val.1).symm z.val.2) b hbpos hb
    (fun n z hz => (norm_le_euclideanPairNorm _).trans (hstep n z.val ⟨z.property, hz⟩))
  let G : P × Pair → Pair := fun z => if hz : z.1 ∈ L then g ⟨z, hz⟩ else 0
  refine ⟨G, ?_, ?_⟩
  · intro m
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hg m) ε hε] with n hn
    intro z hz
    simpa only [G, dite_eq_left hz.1] using hn (⟨z, hz.1⟩ : X) hz.2
  · intro m z hz
    have ht := htail m (⟨z, hz.1⟩ : X) hz.2
    have he := euclideanPairNorm_le_two_mul_norm (g ⟨z, hz.1⟩ - (F m z.1).symm z.2)
    simp only [G, dite_eq_left hz.1]
    linarith

section Topology

variable [TopologicalSpace P]

/-- Uniform convergence on growing cylinders is locally uniform on every
open subset of the controlled base. -/
theorem locallyUniformOn_of_cylinders {f : ℕ → P × Pair → Pair} {G : P × Pair → Pair}
    {L B : Set P} (hB : IsOpen B) (hBL : B ⊆ L) (a : ℕ → ℝ)
    (hcover : ∀ R : ℝ, ∃ n, R ≤ a n)
    (hlim : ∀ n, TendstoUniformlyOn f G atTop (cylinder L (a n))) :
    TendstoLocallyUniformlyOn f G atTop (B ×ˢ univ) := by
  intro u hu z hz
  obtain ⟨n, hn⟩ := hcover (euclideanPairNorm z.2 + 1)
  let O : Set (P × Pair) := B ×ˢ {w | euclideanPairNorm w < a n}
  have hO : IsOpen O := hB.prod (isOpen_lt continuous_euclideanPairNorm continuous_const)
  have hzO : z ∈ O := ⟨hz.1, by change euclideanPairNorm z.2 < a n; linarith⟩
  refine ⟨O, mem_nhdsWithin_of_mem_nhds (hO.mem_nhds hzO), ?_⟩
  filter_upwards [hlim n u hu] with j hj
  intro x hx
  exact hj x ⟨hBL hx.1, hx.2.le⟩

end Topology

section Holomorphic

variable [NormedAddCommGroup P] [NormedSpace ℂ P] [ProperSpace P]

/-- A locally holomorphic sequence of genuine cumulative inverses has a
jointly holomorphic limit on each open base subset controlled by the estimates. -/
theorem exists_holomorphic_inverse_limit (F : ℕ → P → Pair ≃ₜ Pair)
    {L U B : Set P} (hB : IsOpen B) (hBL : B ⊆ L) (hLU : L ⊆ U)
    (a b : ℕ → ℝ) (ha : Monotone a) (hcover : ∀ R : ℝ, ∃ n, R ≤ a n)
    (hbpos : ∀ n, 0 < b n) (hb : ∀ n, b (n + 1) ≤ b n / 2)
    (hhol : ∀ n, DifferentiableOn ℂ (fun z : P × Pair => (F n z.1).symm z.2) (U ×ˢ univ))
    (hstep : ∀ n z, z ∈ cylinder L (a n) →
      euclideanPairNorm ((F (n + 1) z.1).symm z.2 - (F n z.1).symm z.2) ≤ b n / 4) :
    ∃ G : P × Pair → Pair,
      (∀ m, TendstoUniformlyOn (fun n z => (F n z.1).symm z.2) G atTop
        (cylinder L (a m))) ∧
      TendstoLocallyUniformlyOn (fun n z => (F n z.1).symm z.2) G atTop (B ×ˢ univ) ∧
      DifferentiableOn ℂ G (B ×ˢ univ) ∧
      ∀ m z, z ∈ cylinder L (a m) →
        euclideanPairNorm (G z - (F m z.1).symm z.2) ≤ b m := by
  obtain ⟨G, hG, htail⟩ := exists_inverse_limit F L a b ha hcover hbpos hb hstep
  have hloc := locallyUniformOn_of_cylinders hB hBL a hcover hG
  refine ⟨G, hG, hloc, ?_, htail⟩
  exact SeveralVariableUniformLimit.differentiableOn_of_tendstoLocallyUniformlyOn
    (hB.prod isOpen_univ) (fun n => (hhol n).mono (fun z hz => ⟨hLU (hBL hz.1), hz.2⟩)) hloc

end Holomorphic

end AutomaticContinuity.NonautonomousInverseLimit
