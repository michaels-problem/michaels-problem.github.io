import AutomaticContinuity.FlagStrongMarginFamily

set_option autoImplicit false

/-!
# Actual additive gluing of flag-admissible holomorphic sections

The analytic splitting data are actual functions `a,b`, holomorphic on the
two specified open domains. Their overlap identity produces one holomorphic
section. Fixed Euclidean target margins prove admissibility after correction,
and the correction on the old domain is exactly the approximation error.
No additive Cousin operator or overlap approximation theorem is assumed to
have been constructed here.
-/

noncomputable section

namespace AutomaticContinuity.FlagAdditiveGluing

open Set FlagTotalSpace

abbrev Pair := ℂ × ℂ

def glue {X : Type*} (U : Set X) (f g a b : X → Pair) (z : X) : Pair := by
  classical
  exact if z ∈ U then f z + a z else g z + b z

theorem glue_eq_left {X : Type*} {U : Set X} (f g a b : X → Pair)
    {z : X} (hz : z ∈ U) : glue U f g a b z = f z + a z := by
  simp [glue, hz]

theorem glue_eq_right {X : Type*} {U V : Set X} (f g a b : X → Pair)
    (heq : ∀ z ∈ U ∩ V, f z + a z = g z + b z)
    {z : X} (hz : z ∈ V) : glue U f g a b z = g z + b z := by
  by_cases hu : z ∈ U
  · exact (glue_eq_left f g a b hu).trans (heq z ⟨hu, hz⟩)
  · simp [glue, hu]

theorem differentiableOn_glue {n : ℕ} {U V : Set (FinitePoint n)}
    (hU : IsOpen U) (hV : IsOpen V) (f g a b : FinitePoint n → Pair)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g V)
    (ha : DifferentiableOn ℂ a U) (hb : DifferentiableOn ℂ b V)
    (heq : ∀ z ∈ U ∩ V, f z + a z = g z + b z) :
    DifferentiableOn ℂ (glue U f g a b) (U ∪ V) := by
  have hleft : DifferentiableOn ℂ (glue U f g a b) U :=
    (hf.add ha).congr (fun z hz => glue_eq_left f g a b hz)
  have hright : DifferentiableOn ℂ (glue U f g a b) V :=
    (hg.add hb).congr (fun z hz => glue_eq_right f g a b heq hz)
  exact hleft.union_of_isOpen hright hU hV

theorem admissible_glue {n : ℕ} {U V : Set (FinitePoint n)}
    (f g a b : FinitePoint n → Pair) {δA δB : ℝ}
    (hA : ∀ z ∈ U, ∀ e : Pair, euclideanPairNorm e ≤ δA →
      (z, f z + e) ∈ totalSet n)
    (hB : ∀ z ∈ V, ∀ e : Pair, euclideanPairNorm e ≤ δB →
      (z, g z + e) ∈ totalSet n)
    (ha : ∀ z ∈ U, euclideanPairNorm (a z) ≤ δA)
    (hb : ∀ z ∈ V, euclideanPairNorm (b z) ≤ δB) :
    ∀ z ∈ U ∪ V, (z, glue U f g a b z) ∈ totalSet n := by
  intro z hz
  by_cases hu : z ∈ U
  · rw [glue_eq_left f g a b hu]
    exact hA z hu (a z) (ha z hu)
  · have hv : z ∈ V := hz.resolve_left hu
    simpa [glue, hu] using hB z hv (b z) (hb z hv)

theorem error_glue {X : Type*} {U K : Set X} (f g a b : X → Pair)
    (hKU : K ⊆ U) {ε : ℝ} (ha : ∀ z ∈ K, euclideanPairNorm (a z) < ε) :
    ∀ z ∈ K, euclideanPairNorm (glue U f g a b z - f z) < ε := by
  intro z hz
  rw [glue_eq_left f g a b (hKU hz), add_sub_cancel_left]
  exact ha z hz

/-- A genuine holomorphic section and its approximation estimate follow from
the actual additive splitting and the two uniform admissibility margins. -/
theorem exists_glued_section {n : ℕ} {U V K : Set (FinitePoint n)}
    (hU : IsOpen U) (hV : IsOpen V) (hKU : K ⊆ U)
    (f g a b : FinitePoint n → Pair)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g V)
    (ha : DifferentiableOn ℂ a U) (hb : DifferentiableOn ℂ b V)
    (hsplit : ∀ z ∈ U ∩ V, g z - f z = a z - b z)
    {δA δB ε : ℝ}
    (hA : ∀ z ∈ U, ∀ e : Pair, euclideanPairNorm e ≤ δA →
      (z, f z + e) ∈ totalSet n)
    (hB : ∀ z ∈ V, ∀ e : Pair, euclideanPairNorm e ≤ δB →
      (z, g z + e) ∈ totalSet n)
    (ha_bound : ∀ z ∈ U, euclideanPairNorm (a z) ≤ δA)
    (hb_bound : ∀ z ∈ V, euclideanPairNorm (b z) ≤ δB)
    (ha_error : ∀ z ∈ K, euclideanPairNorm (a z) < ε) :
    ∃ H : FinitePoint n → Pair, DifferentiableOn ℂ H (U ∪ V) ∧
      (∀ z ∈ U ∪ V, (z, H z) ∈ totalSet n) ∧
      (∀ z ∈ K, euclideanPairNorm (H z - f z) < ε) ∧
      EqOn H (fun z => f z + a z) U ∧ EqOn H (fun z => g z + b z) V := by
  have heq : ∀ z ∈ U ∩ V, f z + a z = g z + b z := by
    intro z hz
    have h := hsplit z hz
    linear_combination -h
  exact ⟨glue U f g a b,
    differentiableOn_glue hU hV f g a b hf hg ha hb heq,
    admissible_glue f g a b hA hB ha_bound hb_bound,
    error_glue f g a b hKU ha_error,
    fun _ hz => glue_eq_left f g a b hz,
    fun _ hz => glue_eq_right f g a b heq hz⟩

/-- Specialization to an actual entire-fibre family with a uniform margin.
The parameter map only needs to be holomorphic on the new base domain; its
size away from the overlap is unrestricted. -/
theorem exists_glued_section_of_family {n : ℕ} {U V K : Set (FinitePoint n)}
    (hU : IsOpen U) (hV : IsOpen V) (hKU : K ⊆ U)
    (f p a b : FinitePoint n → Pair) (G : FinitePoint n × Pair → Pair)
    (hf : DifferentiableOn ℂ f U) (hp : DifferentiableOn ℂ p V)
    (hG : DifferentiableOn ℂ G (V ×ˢ univ))
    (ha : DifferentiableOn ℂ a U) (hb : DifferentiableOn ℂ b V)
    (hsplit : ∀ z ∈ U ∩ V, G (z, p z) - f z = a z - b z)
    {δA δB ε : ℝ}
    (hA : ∀ z ∈ U, ∀ e : Pair, euclideanPairNorm e ≤ δA →
      (z, f z + e) ∈ totalSet n)
    (hB : ∀ z ∈ V, ∀ w e : Pair, euclideanPairNorm e ≤ δB →
      (z, G (z, w) + e) ∈ totalSet n)
    (ha_bound : ∀ z ∈ U, euclideanPairNorm (a z) ≤ δA)
    (hb_bound : ∀ z ∈ V, euclideanPairNorm (b z) ≤ δB)
    (ha_error : ∀ z ∈ K, euclideanPairNorm (a z) < ε) :
    ∃ H : FinitePoint n → Pair, DifferentiableOn ℂ H (U ∪ V) ∧
      (∀ z ∈ U ∪ V, (z, H z) ∈ totalSet n) ∧
      (∀ z ∈ K, euclideanPairNorm (H z - f z) < ε) ∧
      EqOn H (fun z => f z + a z) U ∧ EqOn H (fun z => G (z, p z) + b z) V := by
  apply exists_glued_section hU hV hKU f (fun z => G (z, p z)) a b hf
    (hG.comp (differentiableOn_id.prodMk hp) (fun z hz => ⟨hz, mem_univ _⟩))
    ha hb hsplit hA (fun z hz => hB z hz (p z)) ha_bound hb_bound ha_error

end AutomaticContinuity.FlagAdditiveGluing
