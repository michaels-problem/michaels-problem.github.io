import AutomaticContinuity.NonautonomousForwardLimit
import AutomaticContinuity.NonautonomousInverseTails
import AutomaticContinuity.HolomorphicInverseLimit

set_option autoImplicit false

/-!
# Identifying the nonautonomous limit domain

Given inverse convergence and the local quantitative step estimates, inverse
tails prove that the inverse limit actually enters the constructed domain.
Both inverse identities and the biholomorphism then follow from locally
uniform convergence. The domain inclusion is proved, not assumed.
-/

noncomputable section

namespace AutomaticContinuity.NonautonomousBiholomorphism

open Set Filter ParameterFibreComposition NonautonomousEntryDomains
open scoped Topology

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [ProperSpace P]

omit [NormedSpace ℂ P] [ProperSpace P] in
private theorem locallyUniform_fst (S : Set (P × Pair)) :
    TendstoLocallyUniformlyOn (fun (_ : ℕ) (z : P × Pair) => z.1)
      (fun z => z.1) atTop S := by
  apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  exact Eventually.of_forall (fun _ _ _ => by simpa only [dist_self] using hε)

omit [NormedAddCommGroup P] [NormedSpace ℂ P] [ProperSpace P] in
/-- The inverse limit lies in an entry set because every finite inverse tail
stays in one closed ball strictly inside that entry ball. -/
theorem inverse_limit_mem_domain (e : ℕ → P → Pair ≃ₜ Pair)
    (U : Set P) (r a b : ℕ → ℝ)
    (hra : ∀ n, r n ≤ a n) (ha : Monotone a)
    (hbpos : ∀ n, 0 < b n) (hb : ∀ n, b (n + 1) ≤ b n / 2)
    (hlarge : ∀ R : ℝ, ∃ j, R + b j / 2 < r j)
    (hinv : ∀ n p, p ∈ U → ∀ w, euclideanPairNorm w ≤ a n →
      euclideanPairNorm ((e n p).symm w - w) ≤ b n / 4)
    {p : P} (hp : p ∈ U) (y w : Pair)
    (hlim : Tendsto (fun n => (product e n p).symm y) atTop (𝓝 w)) :
    (p, w) ∈ domain e U r := by
  obtain ⟨j, hj⟩ := hlarge (euclideanPairNorm y)
  apply entry_subset_domain e U r j
  apply inverse_limit_mem_entry e U r j hp y w hj hlim
  exact NonautonomousInverseTails.eventually_inverse_tail_le_of_geometric_budget
    e p a b (fun n => (hbpos n).le) hb j y le_rfl le_rfl
    (fun i hi => hj.le.trans ((hra j).trans (ha hi)))
    (fun i _ w hw => hinv i p hp w hw)

/-- Once the inverse sequence converges, all remaining domain and inverse
identities follow from the checked finite-step hypotheses. -/
theorem exists_biholomorphism_of_inverse_convergence
    (e : ℕ → P → Pair ≃ₜ Pair) {U : Set P} (hU : IsOpen U)
    (he : ∀ i, DifferentiableOn ℂ (fun z : P × Pair => e i z.1 z.2) (U ×ˢ univ))
    (heinv : ∀ i, DifferentiableOn ℂ (fun z : P × Pair => (e i z.1).symm z.2) (U ×ˢ univ))
    (r a b : ℕ → ℝ) (hra : ∀ n, r n ≤ a n) (ha : Monotone a)
    (hgap : ∀ n, r n + b n / 4 ≤ r (n + 1))
    (hbpos : ∀ n, 0 < b n) (hb : ∀ n, b (n + 1) ≤ b n / 2)
    (hlarge : ∀ R : ℝ, ∃ j, R + b j / 2 < r j)
    (hstep : ∀ n p, p ∈ U → ∀ w, euclideanPairNorm w ≤ a n →
      euclideanPairNorm (e n p w - w) ≤ b n / 4)
    (hinv : ∀ n p, p ∈ U → ∀ w, euclideanPairNorm w ≤ a n →
      euclideanPairNorm ((e n p).symm w - w) ≤ b n / 4)
    (G : P × Pair → Pair)
    (hG : TendstoLocallyUniformlyOn
      (fun n (z : P × Pair) => (product e n z.1).symm z.2) G atTop (U ×ˢ univ)) :
    ∃ F : P × Pair → Pair,
      DifferentiableOn ℂ (fun z => (z.1, F z)) (domain e U r) ∧
      DifferentiableOn ℂ (fun z => (z.1, G z)) (U ×ˢ univ) ∧
      ∃ H : domain e U r ≃ₜ (U ×ˢ (univ : Set Pair)),
        (∀ x : domain e U r, (H x : P × Pair) = (x.val.1, F x.val)) ∧
        (∀ y : U ×ˢ (univ : Set Pair), (H.symm y : P × Pair) = (y.val.1, G y.val)) := by
  obtain ⟨F, _, hF, _, _⟩ := NonautonomousForwardLimit.exists_holomorphic_forward_limit
    e hU he r a b hra hgap hbpos hb hstep
  have hGdom : MapsTo (fun z : P × Pair => (z.1, G z)) (U ×ˢ univ) (domain e U r) := by
    intro z hz
    exact inverse_limit_mem_domain e U r a b hra ha hbpos hb hlarge hinv hz.1
      z.2 (G z) (hG.tendsto_at hz)
  have hFbase : MapsTo (fun z : P × Pair => (z.1, F z)) (domain e U r) (U ×ˢ univ) := by
    intro z hz
    exact ⟨(domain_subset_base e U r hz).1, mem_univ _⟩
  obtain ⟨hFhol, hGhol, H, hH, hHinv⟩ := HolomorphicInverseLimit.exists_holomorphic_inverse_limit
    (isOpen_domain e hU r (fun i => (he i).continuousOn)) (hU.prod isOpen_univ)
    ((locallyUniform_fst (domain e U r)).prodMk hF)
    ((locallyUniform_fst (U ×ˢ univ)).prodMk hG)
    (fun n => differentiable_fst.differentiableOn.prodMk
      ((differentiableOn_product e n U (fun i _ => he i)).mono (domain_subset_base e U r)))
    (fun n => differentiable_fst.differentiableOn.prodMk
      (differentiableOn_product_symm e n U (fun i _ => heinv i)))
    hFbase hGdom
    (Eventually.of_forall (fun n z _ => by simp only [Homeomorph.symm_apply_apply]))
    (Eventually.of_forall (fun n z _ => by simp only [Homeomorph.apply_symm_apply]))
  exact ⟨F, hFhol, hGhol, H, hH, hHinv⟩

end AutomaticContinuity.NonautonomousBiholomorphism
