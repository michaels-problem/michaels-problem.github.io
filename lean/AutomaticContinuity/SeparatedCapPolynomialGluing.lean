import AutomaticContinuity.SeparatedCapPolynomialCutoff
import AutomaticContinuity.LocalFlagInterpolation
import AutomaticContinuity.EuclideanBallGeometry

set_option autoImplicit false

/-! # Combining polynomial approximations on two separated compact pieces

The local approximating polynomials are chosen first. A sup-norm bound on
their difference then determines the cutoff tolerance. Thus no size bound
on the chosen polynomials is hidden in the gluing argument.
-/

noncomputable section

namespace AutomaticContinuity.SeparatedCapPolynomialGluing

open Set PolynomialFunctionAlgebra

variable {σ : Type*}

theorem exists_polynomial_approx_of_cutoff
    {K₀ K₁ : Set (σ → ℂ)} (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁)
    (f₀ f₁ : (σ → ℂ) → ℂ)
    (happrox₀ : ∀ η : ℝ, 0 < η → ∃ p : MvPolynomial σ ℂ,
      ∀ x ∈ K₀, ‖MvPolynomial.eval x p-f₀ x‖ < η)
    (happrox₁ : ∀ η : ℝ, 0 < η → ∃ p : MvPolynomial σ ℂ,
      ∀ x ∈ K₁, ‖MvPolynomial.eval x p-f₁ x‖ < η)
    (hcutoff : ∀ η : ℝ, 0 < η → ∃ q : MvPolynomial σ ℂ,
      (∀ x ∈ K₀, ‖MvPolynomial.eval x q-1‖ < η) ∧
      (∀ x ∈ K₁, ‖MvPolynomial.eval x q‖ < η))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial σ ℂ,
      (∀ x ∈ K₀, ‖MvPolynomial.eval x p-f₀ x‖ < ε) ∧
      (∀ x ∈ K₁, ‖MvPolynomial.eval x p-f₁ x‖ < ε) := by
  let K := K₀ ∪ K₁
  let : CompactSpace K := isCompact_iff_compactSpace.mp (hK₀.union hK₁)
  obtain ⟨p₀,hp₀⟩ := happrox₀ (ε/2) (half_pos hε)
  obtain ⟨p₁,hp₁⟩ := happrox₁ (ε/2) (half_pos hε)
  let B : ℝ := ‖polynomial K (p₀-p₁)‖
  have hB : 0 ≤ B := norm_nonneg _
  have hcross (x : σ → ℂ) (hx : x ∈ K) :
      ‖MvPolynomial.eval x p₀-MvPolynomial.eval x p₁‖ ≤ B := by
    have h := ContinuousMap.norm_coe_le_norm (polynomial K (p₀-p₁)).val ⟨x,hx⟩
    have hval : (polynomial K (p₀-p₁)).val ⟨x,hx⟩ =
        MvPolynomial.eval x p₀-MvPolynomial.eval x p₁ := by rw [polynomial_apply,map_sub]
    rw [hval] at h
    exact h
  let η : ℝ := (ε/2)/(B+1)
  have hη : 0 < η := div_pos (half_pos hε) (by positivity)
  have hηB : η*B ≤ ε/2 := by
    calc
      _ ≤ η*(B+1) := mul_le_mul_of_nonneg_left (by linarith) hη.le
      _ = ε/2 := div_mul_cancel₀ _ (by positivity)
  obtain ⟨q,hq₀,hq₁⟩ := hcutoff η hη
  let p : MvPolynomial σ ℂ := q*p₀+(1-q)*p₁
  refine ⟨p,?_,?_⟩
  · intro x hx
    have hq := hq₀ x hx
    have hcrossx := hcross x (Or.inl hx)
    have herr : ‖(MvPolynomial.eval x q-1)*
        (MvPolynomial.eval x p₀-MvPolynomial.eval x p₁)‖ ≤ ε/2 := by
      rw [norm_mul]
      exact (mul_le_mul hq.le hcrossx (norm_nonneg _) hη.le).trans hηB
    have heq : MvPolynomial.eval x p-f₀ x = (MvPolynomial.eval x p₀-f₀ x)+
        (MvPolynomial.eval x q-1)*(MvPolynomial.eval x p₀-MvPolynomial.eval x p₁) := by
      simp only [p,map_add,map_mul,map_sub,map_one]
      ring
    rw [heq]
    exact (norm_add_le _ _).trans_lt (by linarith [hp₀ x hx])
  · intro x hx
    have hq := hq₁ x hx
    have hcrossx := hcross x (Or.inr hx)
    have herr : ‖MvPolynomial.eval x q*
        (MvPolynomial.eval x p₀-MvPolynomial.eval x p₁)‖ ≤ ε/2 := by
      rw [norm_mul]
      exact (mul_le_mul hq.le hcrossx (norm_nonneg _) hη.le).trans hηB
    have heq : MvPolynomial.eval x p-f₁ x = (MvPolynomial.eval x p₁-f₁ x)+
        MvPolynomial.eval x q*(MvPolynomial.eval x p₀-MvPolynomial.eval x p₁) := by
      simp only [p,map_add,map_mul,map_sub,map_one]
      ring
    rw [heq]
    exact (norm_add_le _ _).trans_lt (by linarith [hp₁ x hx])

/-- Applying the scalar construction to both components gives the requested
Euclidean pair estimate, with no assumption on the sizes of the polynomials. -/
theorem exists_pair_polynomial_approx_of_cutoff
    {K₀ K₁ : Set (σ → ℂ)} (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁)
    (f₀ f₁ : (σ → ℂ) → ℂ × ℂ)
    (happrox₀ : ∀ η : ℝ, 0 < η → ∃ p q : MvPolynomial σ ℂ,
      ∀ x ∈ K₀, euclideanPairNorm ((MvPolynomial.eval x p,MvPolynomial.eval x q)-f₀ x) < η)
    (happrox₁ : ∀ η : ℝ, 0 < η → ∃ p q : MvPolynomial σ ℂ,
      ∀ x ∈ K₁, euclideanPairNorm ((MvPolynomial.eval x p,MvPolynomial.eval x q)-f₁ x) < η)
    (hcutoff : ∀ η : ℝ, 0 < η → ∃ q : MvPolynomial σ ℂ,
      (∀ x ∈ K₀, ‖MvPolynomial.eval x q-1‖ < η) ∧
      (∀ x ∈ K₁, ‖MvPolynomial.eval x q‖ < η))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p q : MvPolynomial σ ℂ,
      (∀ x ∈ K₀, euclideanPairNorm ((MvPolynomial.eval x p,MvPolynomial.eval x q)-f₀ x) < ε) ∧
      (∀ x ∈ K₁, euclideanPairNorm ((MvPolynomial.eval x p,MvPolynomial.eval x q)-f₁ x) < ε) := by
  have hfst₀ : ∀ η : ℝ, 0 < η → ∃ p : MvPolynomial σ ℂ,
      ∀ x ∈ K₀, ‖MvPolynomial.eval x p-(f₀ x).1‖ < η := by
    intro η hη
    obtain ⟨p,q,hpq⟩ := happrox₀ η hη
    exact ⟨p,fun x hx ↦ (norm_fst_le_euclideanPairNorm _).trans_lt (hpq x hx)⟩
  have hsnd₀ : ∀ η : ℝ, 0 < η → ∃ q : MvPolynomial σ ℂ,
      ∀ x ∈ K₀, ‖MvPolynomial.eval x q-(f₀ x).2‖ < η := by
    intro η hη
    obtain ⟨p,q,hpq⟩ := happrox₀ η hη
    exact ⟨q,fun x hx ↦ (norm_snd_le_euclideanPairNorm _).trans_lt (hpq x hx)⟩
  have hfst₁ : ∀ η : ℝ, 0 < η → ∃ p : MvPolynomial σ ℂ,
      ∀ x ∈ K₁, ‖MvPolynomial.eval x p-(f₁ x).1‖ < η := by
    intro η hη
    obtain ⟨p,q,hpq⟩ := happrox₁ η hη
    exact ⟨p,fun x hx ↦ (norm_fst_le_euclideanPairNorm _).trans_lt (hpq x hx)⟩
  have hsnd₁ : ∀ η : ℝ, 0 < η → ∃ q : MvPolynomial σ ℂ,
      ∀ x ∈ K₁, ‖MvPolynomial.eval x q-(f₁ x).2‖ < η := by
    intro η hη
    obtain ⟨p,q,hpq⟩ := happrox₁ η hη
    exact ⟨q,fun x hx ↦ (norm_snd_le_euclideanPairNorm _).trans_lt (hpq x hx)⟩
  obtain ⟨p,hp₀,hp₁⟩ := exists_polynomial_approx_of_cutoff hK₀ hK₁
    (fun x ↦ (f₀ x).1) (fun x ↦ (f₁ x).1) hfst₀ hfst₁ hcutoff (half_pos hε)
  obtain ⟨q,hq₀,hq₁⟩ := exists_polynomial_approx_of_cutoff hK₀ hK₁
    (fun x ↦ (f₀ x).2) (fun x ↦ (f₁ x).2) hsnd₀ hsnd₁ hcutoff (half_pos hε)
  refine ⟨p,q,?_,?_⟩
  · intro x hx
    exact (euclideanPairNorm_le_sum _).trans_lt (by dsimp; linarith [hp₀ x hx,hq₀ x hx])
  · intro x hx
    exact (euclideanPairNorm_le_sum _).trans_lt (by dsimp; linarith [hp₁ x hx,hq₁ x hx])

end AutomaticContinuity.SeparatedCapPolynomialGluing
