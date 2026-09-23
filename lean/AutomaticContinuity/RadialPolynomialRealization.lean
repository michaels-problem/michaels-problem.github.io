import AutomaticContinuity.RadialPolynomialFamily
import AutomaticContinuity.PolynomialFieldRealization
import AutomaticContinuity.RadialCompactPush
import AutomaticContinuity.PolynomialFamilyRegularity

set_option autoImplicit false

/-!
# The radial realization premise is discharged for actual polynomial families

There is no automorphism-approximation premise here. The maps are the concrete
finite products of complete fields obtained from the polynomial coefficient
arrays. The time parameter is real and compact; base holomorphy is local.
-/

noncomputable section

namespace AutomaticContinuity.RadialPolynomialRealization

open RadialCutoffTubes RadialPolynomialField RadialPolynomialFamily
open PolynomialFieldRealization RadialCompactPush
open PolynomialFamilyRegularity (HolomorphicCoefficientsOn ContinuousCoefficientsOn)

variable {P : Type*}

/-- The actual finite product realizing the amplified radial field. -/
def map (q : P → Poly) (D : ℕ) (c : ℝ) (m : ℕ)
    (s : UnitTime) (t : ℂ) (p : P) : (ℂ × ℂ) ≃ₜ (ℂ × ℂ) :=
  polynomialAutomorphism (3 ^ m * D + 1)
    (fun z : UnitTime × P => (family q c m z).1)
    (fun z : UnitTime × P => (family q c m z).2) (s, p) t

theorem map_reparam (q : P → Poly) (D : ℕ) (c : ℝ) (m : ℕ)
    (s : UnitTime) (t : ℂ) (p : P) :
    map q D c m s t p = polynomialAutomorphism (3 ^ m * D + 1)
      (fun p : P => (family q c m (s, p)).1)
      (fun p : P => (family q c m (s, p)).2) p t := rfl

variable [NormedAddCommGroup P] [NormedSpace ℂ P]

private theorem differentiableOn_fixed_time
    {F : ℂ × (P × (ℂ × ℂ)) → (ℂ × ℂ)} {U : Set P}
    (hF : DifferentiableOn ℂ F {z | z.2.1 ∈ U}) (t : ℂ) :
    DifferentiableOn ℂ (fun z : P × (ℂ × ℂ) => F (t, z)) (U ×ˢ Set.univ) := by
  have hk : Differentiable ℂ (fun z : P × (ℂ × ℂ) => (t, z)) :=
    (differentiable_const t).prodMk differentiable_id
  exact hF.comp hk.differentiableOn (fun z hz => hz.1)

set_option maxHeartbeats 300000 in
/-- Every amplification degree has an actual local holomorphic realization,
uniformly on arbitrary compact sets of real-time, base and fibre parameters. -/
def realization (q : P → Poly) (D : ℕ) {c : ℝ} (hc : 0 ≤ c)
    {U : Set P} (hq : HolomorphicCoefficientsOn q U)
    (hdegree : ∀ p ∈ U, (q p).totalDegree ≤ D) (m : ℕ) :
    Realization (value q) c U m where
  map := map q D c m
  fixes_zero := by
    intro s t p
    exact polynomialAutomorphism_origin (3 ^ m * D + 1)
      (fun z : UnitTime × P => (family q c m z).1)
      (fun z : UnitTime × P => (family q c m z).2) (s, p) t
  holomorphic := by
    intro s t
    have hcoef := holomorphicCoefficientsOn_family q c m s (U := U) hq
    have hh := differentiableOn_joint_polynomialAutomorphism (3 ^ m * D + 1)
      (fun p : P => (family q c m (s, p)).1)
      (fun p : P => (family q c m (s, p)).2) hcoef.1 hcoef.2
    change DifferentiableOn ℂ (fun z : P × (ℂ × ℂ) => polynomialAutomorphism (3 ^ m * D + 1)
      (fun p : P => (family q c m (s, p)).1)
      (fun p : P => (family q c m (s, p)).2) z.1 t z.2) (U ×ˢ Set.univ)
    exact differentiableOn_fixed_time hh t
  inverse_holomorphic := by
    intro s t
    have hcoef := holomorphicCoefficientsOn_family q c m s hq
    have hh := differentiableOn_joint_polynomialAutomorphism_symm (3 ^ m * D + 1)
      (fun p : P => (family q c m (s, p)).1)
      (fun p : P => (family q c m (s, p)).2) hcoef.1 hcoef.2
    change DifferentiableOn ℂ (fun z : P × (ℂ × ℂ) => (polynomialAutomorphism (3 ^ m * D + 1)
      (fun p : P => (family q c m (s, p)).1)
      (fun p : P => (family q c m (s, p)).2) z.1 t).symm z.2) (U ×ˢ Set.univ)
    exact differentiableOn_fixed_time hh t
  uniform_step := by
    intro C hC hCU η hη
    let reassociate : UnitTime × (P × (ℂ × ℂ)) → (UnitTime × P) × (ℂ × ℂ) :=
      fun z => ((z.1, z.2.1), z.2.2)
    have hassoc : Continuous reassociate := by unfold reassociate; fun_prop
    have hcoef := continuousCoefficientsOn_family q hc m
      (show ContinuousCoefficientsOn q U from fun d => (hq d).continuousOn)
    obtain ⟨τ, hτ, hτbound⟩ := exists_polynomial_uniform_euclidean_first_order_step
      (3 ^ m * D + 1)
      (fun z : UnitTime × P => (family q c m z).1)
      (fun z : UnitTime × P => (family q c m z).2) hcoef.1 hcoef.2
      (fun z hz => family_degree q c m z (hdegree z.2 hz.2))
      (fun z _ => family_zero q c m z) (hC.image hassoc)
      (show ∀ z ∈ reassociate '' C, z.1 ∈ Set.univ ×ˢ U from by
        rintro _ ⟨z, hz, rfl⟩
        exact ⟨Set.mem_univ _, (hCU hz).2.1⟩) hη
    refine ⟨τ, hτ, ?_⟩
    intro z hz t ht htτ
    have hb := hτbound (reassociate z) (Set.mem_image_of_mem _ hz) t ht htτ
    have he : HomogeneousFieldDecomposition.evaluation z.2.2 (family q c m (z.1, z.2.1)) =
        localizedField (value q) c m z.1 z.2.1 z.2.2 :=
      evaluation_family q c m z.1 z.2.1 z.2.2
    change euclideanPairNorm (map q D c m z.1 t z.2.1 z.2.2 - z.2.2 -
          t • HomogeneousFieldDecomposition.evaluation z.2.2 (family q c m (z.1, z.2.1))) < η * ‖t‖ ∧
      euclideanPairNorm ((map q D c m z.1 t z.2.1).symm z.2.2 - z.2.2 +
          t • HomogeneousFieldDecomposition.evaluation z.2.2 (family q c m (z.1, z.2.1))) < η * ‖t‖ at hb
    simpa only [he] using hb

end AutomaticContinuity.RadialPolynomialRealization
