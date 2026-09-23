import AutomaticContinuity.ParameterFibreComposition
import AutomaticContinuity.EuclideanBallGeometry
import AutomaticContinuity.AdaptiveUniformLimit

set_option autoImplicit false

/-!
# Entry domains for successive fibre automorphisms

This module constructs the open increasing union associated to an actual
sequence of fibre homeomorphisms. The finite-stage estimates are hypotheses;
the domain properties and forward convergence are conclusions. Inverse-limit
containment is stated with the precise additional closed-ball bound it needs.
No inverse convergence or global parameter extension is asserted here.
-/

noncomputable section

namespace AutomaticContinuity.NonautonomousEntryDomains

open Set Filter ParameterFibreComposition
open scoped Topology

abbrev Pair := ℂ × ℂ

variable {P : Type*}

def entry (e : ℕ → P → Pair ≃ₜ Pair) (U : Set P) (r : ℕ → ℝ) (n : ℕ) :
    Set (P × Pair) :=
  {z | z.1 ∈ U ∧ euclideanPairNorm (product e n z.1 z.2) < r n}

def domain (e : ℕ → P → Pair ≃ₜ Pair) (U : Set P) (r : ℕ → ℝ) :
    Set (P × Pair) := ⋃ n, entry e U r n

theorem entry_subset_domain (e : ℕ → P → Pair ≃ₜ Pair) (U : Set P)
    (r : ℕ → ℝ) (n : ℕ) : entry e U r n ⊆ domain e U r :=
  subset_iUnion (fun n => entry e U r n) n

theorem domain_subset_base (e : ℕ → P → Pair ≃ₜ Pair) (U : Set P)
    (r : ℕ → ℝ) : domain e U r ⊆ U ×ˢ univ := by
  rintro z ⟨_, ⟨n, rfl⟩, hz⟩
  exact ⟨hz.1, mem_univ _⟩

/-- A radius gap absorbs one local near-identity error. -/
theorem entry_mono (e : ℕ → P → Pair ≃ₜ Pair) (U : Set P)
    (r a ε : ℕ → ℝ) (hra : ∀ n, r n ≤ a n)
    (hgap : ∀ n, r n + ε n ≤ r (n + 1))
    (hstep : ∀ n p, p ∈ U → ∀ w, euclideanPairNorm w ≤ a n →
      euclideanPairNorm (e n p w - w) ≤ ε n) :
    Monotone (entry e U r) := by
  apply monotone_nat_of_le_succ
  intro n z hz
  refine ⟨hz.1, ?_⟩
  have he := hstep n z.1 hz.1 (product e n z.1 z.2) (hz.2.le.trans (hra n))
  have htri := euclideanPairNorm_add_le
    (e n z.1 (product e n z.1 z.2) - product e n z.1 z.2)
    (product e n z.1 z.2)
  rw [sub_add_cancel] at htri
  have hr := hz.2
  change euclideanPairNorm (e n z.1 (product e n z.1 z.2)) < r (n + 1)
  linarith [hgap n]

theorem zero_mem_entry (e : ℕ → P → Pair ≃ₜ Pair) (U : Set P)
    (r : ℕ → ℝ) (n : ℕ) {p : P} (hp : p ∈ U) (hr : 0 < r n)
    (hzero : ∀ i < n, e i p 0 = 0) : (p, 0) ∈ entry e U r n := by
  refine ⟨hp, ?_⟩
  rw [product_origin e n p hzero, euclideanPairNorm_zero]
  exact hr

theorem disjoint_domain_of_escape (e : ℕ → P → Pair ≃ₜ Pair)
    (U : Set P) (r : ℕ → ℝ) (K : Set (P × Pair))
    (hescape : ∀ n z, z ∈ K → r n ≤ euclideanPairNorm (product e n z.1 z.2)) :
    Disjoint (domain e U r) K := by
  apply Set.disjoint_left.mpr
  intro z hz hK
  obtain ⟨n, hn⟩ := mem_iUnion.mp hz
  exact (not_lt_of_ge (hescape n z hK)) hn.2

/-- Geometrically decreasing errors give one forward limit, uniform on every
entry set. The quantitative tail bound uses the Euclidean pair norm. -/
theorem exists_forward_limit (e : ℕ → P → Pair ≃ₜ Pair) (U : Set P)
    (r a b : ℕ → ℝ) (hra : ∀ n, r n ≤ a n)
    (hgap : ∀ n, r n + b n / 4 ≤ r (n + 1))
    (hbpos : ∀ n, 0 < b n) (hb : ∀ n, b (n + 1) ≤ b n / 2)
    (hstep : ∀ n p, p ∈ U → ∀ w, euclideanPairNorm w ≤ a n →
      euclideanPairNorm (e n p w - w) ≤ b n / 4) :
    ∃ G : domain e U r → Pair,
      (∀ m, TendstoUniformlyOn
        (fun n (x : domain e U r) => product e n x.val.1 x.val.2) G atTop
        {x | x.val ∈ entry e U r m}) ∧
      ∀ m (x : domain e U r), x.val ∈ entry e U r m →
        euclideanPairNorm (G x - product e m x.val.1 x.val.2) ≤ b m := by
  let K : ℕ → Set (domain e U r) := fun m => {x | x.val ∈ entry e U r m}
  have hmono := entry_mono e U r a (fun n => b n / 4) hra hgap hstep
  have hK : Monotone K := fun i j hij x hx => hmono hij hx
  have hcover : ∀ x : domain e U r, ∃ n, x ∈ K n := by
    intro x
    obtain ⟨n, hn⟩ := mem_iUnion.mp x.property
    exact ⟨n, hn⟩
  have hinc : ∀ n (x : domain e U r), x ∈ K n →
      ‖product e (n + 1) x.val.1 x.val.2 - product e n x.val.1 x.val.2‖ ≤ b n / 4 := by
    intro n x hx
    exact (norm_le_euclideanPairNorm _).trans
      (hstep n x.val.1 hx.1 _ (hx.2.le.trans (hra n)))
  obtain ⟨G, hG, htail⟩ := AdaptiveUniformLimit.exists_limit K hK hcover
    (fun n (x : domain e U r) => product e n x.val.1 x.val.2) b hbpos hb hinc
  refine ⟨G, hG, ?_⟩
  intro m x hx
  exact (euclideanPairNorm_le_two_mul_norm _).trans (by linarith [htail m x hx])

section Topology

variable [TopologicalSpace P]

theorem isOpen_entry (e : ℕ → P → Pair ≃ₜ Pair) {U : Set P}
    (hU : IsOpen U) (r : ℕ → ℝ) (n : ℕ)
    (he : ∀ i < n, ContinuousOn (fun z : P × Pair => e i z.1 z.2) (U ×ˢ univ)) :
    IsOpen (entry e U r n) := by
  have hc := continuous_euclideanPairNorm.comp_continuousOn
    (continuousOn_product e n U he)
  have ho := hc.isOpen_inter_preimage (hU.prod isOpen_univ) (isOpen_Iio (a := r n))
  convert ho using 1
  ext z
  simp [entry]

theorem isOpen_domain (e : ℕ → P → Pair ≃ₜ Pair) {U : Set P}
    (hU : IsOpen U) (r : ℕ → ℝ)
    (he : ∀ i, ContinuousOn (fun z : P × Pair => e i z.1 z.2) (U ×ˢ univ)) :
    IsOpen (domain e U r) :=
  isOpen_iUnion (fun n => isOpen_entry e hU r n (fun i _ => he i))

omit [TopologicalSpace P] in
/-- A closed bound strictly inside one entry ball places an actual inverse
limit inside the domain. The bound must still be proved from inverse tails. -/
theorem inverse_limit_mem_entry (e : ℕ → P → Pair ≃ₜ Pair)
    (U : Set P) (r : ℕ → ℝ) (j : ℕ) {p : P} (hp : p ∈ U)
    (y w : Pair) {s : ℝ} (hs : s < r j)
    (hlim : Tendsto (fun n => (product e n p).symm y) atTop (𝓝 w))
    (hbound : ∀ᶠ n in atTop,
      euclideanPairNorm (product e j p ((product e n p).symm y)) ≤ s) :
    (p, w) ∈ entry e U r j := by
  refine ⟨hp, lt_of_le_of_lt ?_ hs⟩
  exact le_of_tendsto
    ((continuous_euclideanPairNorm.comp (product e j p).continuous).continuousAt.tendsto.comp hlim)
    hbound

end Topology

end AutomaticContinuity.NonautonomousEntryDomains
