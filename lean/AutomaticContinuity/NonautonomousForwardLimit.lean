import AutomaticContinuity.NonautonomousEntryDomains
import AutomaticContinuity.SeveralVariableUniformLimit

set_option autoImplicit false

/-!
# A holomorphic forward limit on the increasing entry domain

The limit is an ambient function, holomorphic on the open union of entry
sets. It is constructed from actual finite products and geometric error
budgets. Injectivity, surjectivity and inverse convergence are not claimed.
-/

noncomputable section

namespace AutomaticContinuity.NonautonomousForwardLimit

open Set Filter ParameterFibreComposition NonautonomousEntryDomains
open scoped Topology

variable {P : Type*} [TopologicalSpace P]

theorem exists_locally_uniform_forward_limit (e : ℕ → P → Pair ≃ₜ Pair)
    {U : Set P} (hU : IsOpen U)
    (he : ∀ i, ContinuousOn (fun z : P × Pair => e i z.1 z.2) (U ×ˢ univ))
    (r a b : ℕ → ℝ) (hra : ∀ n, r n ≤ a n)
    (hgap : ∀ n, r n + b n / 4 ≤ r (n + 1))
    (hbpos : ∀ n, 0 < b n) (hb : ∀ n, b (n + 1) ≤ b n / 2)
    (hstep : ∀ n p, p ∈ U → ∀ w, euclideanPairNorm w ≤ a n →
      euclideanPairNorm (e n p w - w) ≤ b n / 4) :
    ∃ F : P × Pair → Pair,
      TendstoLocallyUniformlyOn (fun n z => product e n z.1 z.2) F atTop (domain e U r) ∧
      (∀ m, TendstoUniformlyOn (fun n z => product e n z.1 z.2) F atTop (entry e U r m)) ∧
      ∀ m z, z ∈ entry e U r m →
        euclideanPairNorm (F z - product e m z.1 z.2) ≤ b m := by
  classical
  obtain ⟨G, hG, htail⟩ := exists_forward_limit e U r a b hra hgap hbpos hb hstep
  let F : P × Pair → Pair := fun z => if hz : z ∈ domain e U r then G ⟨z, hz⟩ else 0
  have hFU (m : ℕ) : TendstoUniformlyOn
      (fun n (z : P × Pair) => product e n z.1 z.2) F atTop (entry e U r m) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hG m) ε hε] with n hn
    intro z hz
    have hzD := entry_subset_domain e U r m hz
    simpa only [F, dite_eq_left hzD] using hn ⟨z, hzD⟩ hz
  refine ⟨F, ?_, hFU, ?_⟩
  · exact tendstoLocallyUniformlyOn_iUnion
      (fun m => isOpen_entry e hU r m (fun i _ => he i))
      (fun m => (hFU m).tendstoLocallyUniformlyOn)
  · intro m z hz
    have hzD := entry_subset_domain e U r m hz
    simpa only [F, dite_eq_left hzD] using htail m ⟨z, hzD⟩ hz

end AutomaticContinuity.NonautonomousForwardLimit

namespace AutomaticContinuity.NonautonomousForwardLimit

open Set Filter ParameterFibreComposition NonautonomousEntryDomains
open scoped Topology

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [ProperSpace P]

/-- The same constructed forward limit is jointly holomorphic on the actual
open entry domain. No inverse or biholomorphicity premise is used. -/
theorem exists_holomorphic_forward_limit (e : ℕ → P → Pair ≃ₜ Pair)
    {U : Set P} (hU : IsOpen U)
    (he : ∀ i, DifferentiableOn ℂ (fun z : P × Pair => e i z.1 z.2) (U ×ˢ univ))
    (r a b : ℕ → ℝ) (hra : ∀ n, r n ≤ a n)
    (hgap : ∀ n, r n + b n / 4 ≤ r (n + 1))
    (hbpos : ∀ n, 0 < b n) (hb : ∀ n, b (n + 1) ≤ b n / 2)
    (hstep : ∀ n p, p ∈ U → ∀ w, euclideanPairNorm w ≤ a n →
      euclideanPairNorm (e n p w - w) ≤ b n / 4) :
    ∃ F : P × Pair → Pair,
      DifferentiableOn ℂ F (domain e U r) ∧
      TendstoLocallyUniformlyOn (fun n z => product e n z.1 z.2) F atTop (domain e U r) ∧
      (∀ m, TendstoUniformlyOn (fun n z => product e n z.1 z.2) F atTop (entry e U r m)) ∧
      ∀ m z, z ∈ entry e U r m →
        euclideanPairNorm (F z - product e m z.1 z.2) ≤ b m := by
  obtain ⟨F, hFloc, hFunif, htail⟩ := exists_locally_uniform_forward_limit e hU
    (fun i => (he i).continuousOn) r a b hra hgap hbpos hb hstep
  refine ⟨F, ?_, hFloc, hFunif, htail⟩
  exact SeveralVariableUniformLimit.differentiableOn_of_tendstoLocallyUniformlyOn
    (isOpen_domain e hU r (fun i => (he i).continuousOn))
    (fun n => (differentiableOn_product e n U (fun i _ => he i)).mono
      (domain_subset_base e U r)) hFloc

end AutomaticContinuity.NonautonomousForwardLimit
