import AutomaticContinuity.RadialPolynomialField
import AutomaticContinuity.RadialCutoffTubes
import AutomaticContinuity.PolynomialFamilyRegularity

set_option autoImplicit false

/-!
# The polynomial family used along the radial isotopy

Real isotopy time is a compact auxiliary parameter. Each member is an actual
pair of fibre polynomials, of one uniform finite degree. Its evaluation is
exactly the pulled-back cubic cutoff field used by the trajectory estimates.
-/

noncomputable section

namespace AutomaticContinuity.RadialPolynomialFamily

open MvPolynomial RadialCutoffTubes RadialPolynomialField

variable {P : Type*}

def value (q : P → Poly) (z : P × (ℂ × ℂ)) : ℂ := eval ![z.2.1, z.2.2] (q z.1)

def family (q : P → Poly) (c : ℝ) (m : ℕ) (z : UnitTime × P) : Poly × Poly :=
  fieldPolynomial (q z.2) ((scale c z.1 : ℂ)⁻¹) ((c / scale c z.1 : ℝ) : ℂ) m

theorem family_degree (q : P → Poly) (c : ℝ) (m : ℕ) (z : UnitTime × P)
    {D : ℕ} (hdegree : (q z.2).totalDegree ≤ D) :
    (family q c m z).1.totalDegree ≤ 3 ^ m * D + 1 ∧
      (family q c m z).2.totalDegree ≤ 3 ^ m * D + 1 := by
  obtain ⟨h1, h2⟩ := fieldPolynomial_degree (q z.2) _ _ m
  have hb := Nat.add_le_add_right (Nat.mul_le_mul_left (3 ^ m) hdegree) 1
  exact ⟨h1.trans hb, h2.trans hb⟩

theorem family_zero (q : P → Poly) (c : ℝ) (m : ℕ) (z : UnitTime × P) :
    eval (0 : Fin 2 → ℂ) (family q c m z).1 = 0 ∧
      eval (0 : Fin 2 → ℂ) (family q c m z).2 = 0 :=
  fieldPolynomial_zero (q z.2) _ _ m

theorem eval_inverse_real_smul (q : Poly) (r : ℝ) (w : ℂ × ℂ) :
    eval (fun i => (r : ℂ)⁻¹ * ![w.1, w.2] i) q =
      eval ![(r⁻¹ • w).1, (r⁻¹ • w).2] q := by
  apply congrArg (fun coords : Fin 2 → ℂ => eval coords q)
  funext i
  fin_cases i <;> simp [Complex.real_smul, Complex.ofReal_inv]

theorem evaluation_family (q : P → Poly) (c : ℝ) (m : ℕ)
    (t : UnitTime) (p : P) (w : ℂ × ℂ) :
    (eval ![w.1, w.2] (family q c m (t, p)).1,
      eval ![w.1, w.2] (family q c m (t, p)).2) =
      RadialCutoffField.field
        (fun z : P × (ℂ × ℂ) => value q (z.1, (scale c t)⁻¹ • z.2))
        m (c / scale c t) p w := by
  rw [family, eval_fieldPolynomial, eval_inverse_real_smul]
  rfl

section ContinuousParameters

variable [TopologicalSpace P]

/-- Real isotopy time is a continuous auxiliary parameter, uniformly on the
entire compact interval. The base coefficients need only be continuous on U. -/
theorem continuousCoefficientsOn_family (q : P → Poly) {c : ℝ} (hc : 0 ≤ c)
    (m : ℕ) {U : Set P} (hq : PolynomialFamilyRegularity.ContinuousCoefficientsOn q U) :
    PolynomialFamilyRegularity.ContinuousCoefficientsOn
      (fun z : UnitTime × P => (family q c m z).1) (Set.univ ×ˢ U) ∧
    PolynomialFamilyRegularity.ContinuousCoefficientsOn
      (fun z : UnitTime × P => (family q c m z).2) (Set.univ ×ˢ U) := by
  have hq' : PolynomialFamilyRegularity.ContinuousCoefficientsOn
      (fun z : UnitTime × P => q z.2) (Set.univ ×ˢ U) := by
    intro d
    exact (hq d).comp continuousOn_snd (fun z hz => hz.2)
  have hscale : Continuous (fun z : UnitTime × P => (scale c z.1 : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_scale c).comp continuous_fst)
  have hnonzero (z : UnitTime × P) : (scale c z.1 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (scale_pos hc z.1).ne'
  have hs : Continuous (fun z : UnitTime × P => (scale c z.1 : ℂ)⁻¹) :=
    hscale.inv₀ hnonzero
  have hr : Continuous (fun z : UnitTime × P => ((c / scale c z.1 : ℝ) : ℂ)) := by
    simp only [Complex.ofReal_div]
    exact continuous_const.div hscale hnonzero
  exact hq'.fieldPolynomial hs.continuousOn hr.continuousOn m

end ContinuousParameters

section HolomorphicParameters

variable [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- At every fixed real isotopy time the field coefficients are holomorphic
on the original open base domain, with no global extension hypothesis. -/
theorem holomorphicCoefficientsOn_family (q : P → Poly) (c : ℝ)
    (m : ℕ) (t : UnitTime) {U : Set P}
    (hq : PolynomialFamilyRegularity.HolomorphicCoefficientsOn q U) :
    PolynomialFamilyRegularity.HolomorphicCoefficientsOn
      (fun p : P => (family q c m (t, p)).1) U ∧
    PolynomialFamilyRegularity.HolomorphicCoefficientsOn
      (fun p : P => (family q c m (t, p)).2) U := by
  exact PolynomialFamilyRegularity.HolomorphicCoefficientsOn.fieldPolynomial
    (s := fun _ : P => (scale c t : ℂ)⁻¹)
    (rate := fun _ : P => ((c / scale c t : ℝ) : ℂ)) hq
    (differentiableOn_const _) (differentiableOn_const _) m

end HolomorphicParameters

end AutomaticContinuity.RadialPolynomialFamily
