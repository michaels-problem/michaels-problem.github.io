import AutomaticContinuity.FlagSectionApproximation
import AutomaticContinuity.AdaptiveInverseControl

set_option autoImplicit false

/-!
# The concrete approximation-transfer assembly

A fixed whole-target section is glued to an entire-fibre family. The two
remaining analytic inputs are displayed separately: approximation of the
two parameter maps on the old compact and buffered overlap, and bounded
additive splitting on the specified open domains. The target margins are
fixed before any parameter polynomial is chosen. No bound on that polynomial
away from the two approximation sets is required.
-/

noncomputable section

namespace AutomaticContinuity.FlagApproximationTransfer

open Set FlagTotalSpace FlagSectionApproximation

abbrev Pair := ℂ × ℂ

/-- The scalar/vector approximation input. Actual polynomial approximation
is sufficient; only its proved entire holomorphy is needed in the assembly. -/
def ParameterApproximation {n : ℕ} (K C : Set (FinitePoint n))
    (φ θ : FinitePoint n → Pair) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ p : FinitePoint n → Pair, Differentiable ℂ p ∧
    (∀ z ∈ K, euclideanPairNorm (p z - φ z) ≤ δ) ∧
    (∀ z ∈ C, euclideanPairNorm (p z - θ z) ≤ δ)

/-- Bounded additive splitting with its input domain, fixed buffered error
set, output domains, and norm constant all explicit. This definition is an
input interface, not an asserted existence theorem for splitting operators. -/
def BoundedSplitting {n : ℕ} (A B W C : Set (FinitePoint n)) (M : ℝ) : Prop :=
  ∀ c : FinitePoint n → Pair, DifferentiableOn ℂ c W →
    ∀ η : ℝ, 0 < η → (∀ z ∈ C, euclideanPairNorm (c z) < η) →
    ∃ a b : FinitePoint n → Pair,
      DifferentiableOn ℂ a A ∧ DifferentiableOn ℂ b B ∧
      (∀ z ∈ A ∩ B, c z = a z - b z) ∧
      (∀ z ∈ A, euclideanPairNorm (a z) ≤ M * η) ∧
      (∀ z ∈ B, euclideanPairNorm (b z) ≤ M * η)

/-- The approximation transfer is a proved construction from the two precise
analytic inputs. The approximation compact lies on the family side of the
gluing, while the frozen extending section lies on the other side. -/
theorem approximable_of_transfer_data {n : ℕ}
    {K L C A B U V W : Set (FinitePoint n)}
    (hK : IsCompact K) (hC : IsCompact C)
    (hA : IsOpen A) (hB : IsOpen B) (hV : IsOpen V)
    (hLAB : L ⊆ A ∪ B) (hKB : K ⊆ B) (hAU : A ⊆ U) (hBV : B ⊆ V)
    (hCV : C ⊆ V) (hWU : W ⊆ U) (hWV : W ⊆ V)
    (g u φ θ : FinitePoint n → Pair) (G : FinitePoint n × Pair → Pair)
    (hg : DifferentiableOn ℂ g U) (hG : DifferentiableOn ℂ G (V ×ˢ univ))
    (hφ : ContinuousOn φ K) (hθ : ContinuousOn θ C)
    (hφeq : ∀ z ∈ K, G (z, φ z) = u z)
    (hθeq : ∀ z ∈ C, G (z, θ z) = g z)
    {δA δB M : ℝ} (hδA : 0 < δA) (hδB : 0 < δB) (hM : 0 < M)
    (hmarginA : ∀ z ∈ A, ∀ e : Pair, euclideanPairNorm e ≤ δA →
      (z, g z + e) ∈ totalSet n)
    (hmarginB : ∀ z ∈ B, ∀ t e : Pair, euclideanPairNorm e ≤ δB →
      (z, G (z, t) + e) ∈ totalSet n)
    (happrox : ParameterApproximation K C φ θ)
    (hsplit : BoundedSplitting A B W C M) : Approximable K L u := by
  intro ε hε
  let τ : ℝ := min δA (min δB (ε / 2))
  have hτ : 0 < τ := lt_min hδA (lt_min hδB (half_pos hε))
  let η : ℝ := τ / (2 * M)
  have hη : 0 < η := div_pos hτ (mul_pos (by norm_num) hM)
  have hMη : M * η = τ / 2 := by dsimp [η]; field_simp
  have hMηA : M * η ≤ δA := by rw [hMη]; exact (half_le_self hτ.le).trans (min_le_left _ _)
  have hMηB : M * η ≤ δB := by
    rw [hMη]
    exact (half_le_self hτ.le).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hMηε : M * η < ε / 2 := by
    rw [hMη]
    exact (half_lt_self hτ).trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hφgraph : IsCompact ((fun z => (z, φ z)) '' K) :=
    hK.image_of_continuousOn (continuousOn_id.prodMk hφ)
  have hθgraph : IsCompact ((fun z => (z, θ z)) '' C) :=
    hC.image_of_continuousOn (continuousOn_id.prodMk hθ)
  obtain ⟨dK, hdK, hcontrolK⟩ := AdaptiveInverseControl.exists_euclidean_fiber_control
    G hφgraph hV (by rintro _ ⟨z, hz, rfl⟩; exact ⟨hBV (hKB hz), mem_univ _⟩)
    hG.continuousOn (half_pos hε)
  obtain ⟨dC, hdC, hcontrolC⟩ := AdaptiveInverseControl.exists_euclidean_fiber_control
    G hθgraph hV (by rintro _ ⟨z, hz, rfl⟩; exact ⟨hCV hz, mem_univ _⟩)
    hG.continuousOn hη
  obtain ⟨p, hp, hpK, hpC⟩ := happrox (min dK dC) (lt_min hdK hdC)
  let gp : FinitePoint n → Pair := fun z => G (z, p z)
  have hgp : DifferentiableOn ℂ gp V :=
    hG.comp (differentiableOn_id.prodMk hp.differentiableOn) (fun z hz => ⟨hz, mem_univ _⟩)
  have herrorK : ∀ z ∈ K, euclideanPairNorm (gp z - u z) < ε / 2 := by
    intro z hz
    have he := hcontrolK (z, φ z) ⟨z, hz, rfl⟩ (p z) ((hpK z hz).trans (min_le_left _ _))
    simpa only [hφeq z hz] using he
  have herrorC : ∀ z ∈ C, euclideanPairNorm (gp z - g z) < η := by
    intro z hz
    have he := hcontrolC (z, θ z) ⟨z, hz, rfl⟩ (p z) ((hpC z hz).trans (min_le_right _ _))
    simpa only [hθeq z hz] using he
  obtain ⟨a, b, ha, hb, hab, habound, hbbound⟩ :=
    hsplit (fun z => gp z - g z) ((hgp.mono hWV).sub (hg.mono hWU)) η hη herrorC
  have heq : ∀ z ∈ A ∩ B, g z + a z = gp z + b z := by
    intro z hz
    have he := hab z hz
    linear_combination -he
  let H := FlagAdditiveGluing.glue A g gp a b
  have hHol : DifferentiableOn ℂ H (A ∪ B) :=
    FlagAdditiveGluing.differentiableOn_glue hA hB g gp a b
      (hg.mono hAU) (hgp.mono hBV) ha hb heq
  have hAdmissible : ∀ z ∈ A ∪ B, (z, H z) ∈ totalSet n :=
    FlagAdditiveGluing.admissible_glue g gp a b hmarginA
      (fun z hz => hmarginB z hz (p z))
      (fun z hz => (habound z hz).trans hMηA)
      (fun z hz => (hbbound z hz).trans hMηB)
  refine ⟨H, A ∪ B, hA.union hB, hLAB, hHol, hAdmissible, ?_⟩
  intro z hz
  have hright := FlagAdditiveGluing.glue_eq_right g gp a b heq (hKB hz)
  change euclideanPairNorm (FlagAdditiveGluing.glue A g gp a b z - u z) < ε
  rw [hright]
  have htri := euclideanPairNorm_add_le (gp z - u z) (b z)
  have heq' : gp z + b z - u z = (gp z - u z) + b z := by abel
  rw [heq']
  exact htri.trans_lt (by linarith [herrorK z hz, hbbound z (hKB hz)])

end AutomaticContinuity.FlagApproximationTransfer
