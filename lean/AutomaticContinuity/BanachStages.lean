import AutomaticContinuity.CoefficientTopology
import Mathlib.Analysis.Normed.Module.Completion

set_option autoImplicit false

/-!
# Single coefficient-norm Banach completions

The auxiliary type synonyms isolate the individual norm topologies from the
original locally convex topology on `CoefficientSeries`.
-/

noncomputable section

namespace AutomaticContinuity
namespace BanachStages

open CoefficientSeries UniformSpace

/-- The coefficient algebra with the norm at radius `n + 1`. -/
def PreStage (_n : ℕ) := CoefficientSeries

instance (n : ℕ) : CommRing (PreStage n) := inferInstanceAs (CommRing CoefficientSeries)
instance (n : ℕ) : Algebra ℂ (PreStage n) := inferInstanceAs (Algebra ℂ CoefficientSeries)
instance (n : ℕ) : Nontrivial (PreStage n) := inferInstanceAs (Nontrivial CoefficientSeries)

/-- Only the algebraic structure is identified here, not the topology. -/
def preStageEquiv (n : ℕ) : PreStage n ≃ₐ[ℂ] CoefficientSeries := AlgEquiv.refl

def preStageAddGroupNorm (n : ℕ) : AddGroupNorm (PreStage n) where
  toFun f := q (n + 1) (preStageEquiv n f)
  map_zero' := q_zero (n + 1)
  add_le' f g := q_add_le (n + 1) f g
  neg' f := q_neg (n + 1) f
  eq_zero_of_map_eq_zero' f h := (q_eq_zero_iff (Nat.succ_pos n) f).mp h

instance (n : ℕ) : NormedAddCommGroup (PreStage n) :=
  (preStageAddGroupNorm n).toNormedAddCommGroup

instance (n : ℕ) : NormedCommRing (PreStage n) where
  dist_eq _ _ := rfl
  norm_mul_le f g := q_mul_le (n + 1) f g

instance (n : ℕ) : NormedAlgebra ℂ (PreStage n) where
  norm_smul_le c f := le_of_eq (q_smul (n + 1) c f)

@[simp] theorem norm_preStage (n : ℕ) (f : PreStage n) :
    ‖f‖ = q (n + 1) (preStageEquiv n f) := rfl

instance (n : ℕ) : NormOneClass (PreStage n) where
  norm_one := by
    change q (n + 1) (1 : CoefficientSeries) = 1
    have hc : (1 : CoefficientSeries) = constant 1 := by
      apply Subtype.ext
      exact (map_one MvPowerSeries.C).symm
    rw [hc, q_constant, norm_one]

/-- The Banach algebra completion for one coefficient norm. -/
abbrev Stage (n : ℕ) := Completion (PreStage n)

instance (n : ℕ) : NormOneClass (Stage n) where
  norm_one := by rw [← Completion.coe_one (PreStage n), Completion.norm_coe, norm_one]

instance (n : ℕ) : Nontrivial (Stage n) where
  exists_pair_ne := ⟨0, 1, by
    intro h
    have hnorm := congrArg norm h
    simp at hnorm⟩

/-- The canonical map from the full coefficient algebra into a Banach stage. -/
def inclusion (n : ℕ) : CoefficientSeries →ₐ[ℂ] Stage n where
  toRingHom := Completion.coeRingHom.comp (preStageEquiv n).symm.toRingHom
  commutes' _c := rfl

@[simp] theorem norm_inclusion (n : ℕ) (f : CoefficientSeries) :
    ‖inclusion n f‖ = q (n + 1) f := Completion.norm_coe _

theorem continuous_inclusion (n : ℕ) : Continuous (inclusion n) := by
  apply withSeminorms.continuous_normedSpace_rng (Stage n) (inclusion n).toLinearMap
  refine ⟨{n}, 1, ?_⟩
  simp only [Finset.sup_singleton, one_smul]
  intro f
  exact le_of_eq (norm_inclusion n f)

theorem denseRange_inclusion (n : ℕ) : DenseRange (inclusion n) := by
  exact (Completion.denseRange_coe : DenseRange ((↑) : PreStage n → Stage n)).comp
    (preStageEquiv n).symm.surjective.denseRange (Completion.continuous_coe _)

/-- Identity on coefficients decreases the radius and hence the norm. -/
def preBond (n : ℕ) : PreStage (n + 1) →ₐ[ℂ] PreStage n :=
  (preStageEquiv n).symm.toAlgHom.comp (preStageEquiv (n + 1)).toAlgHom

theorem lipschitzWith_preBond (n : ℕ) : LipschitzWith 1 (preBond n) := by
  simpa only [Real.toNNReal_one] using
    (AddMonoidHomClass.lipschitz_of_bound (preBond n) 1 fun f => by
      change q (n + 1) f ≤ 1 * q (n + 1 + 1) f
      simpa only [one_mul] using q_mono (by omega : n + 1 ≤ n + 1 + 1) f)

/-- The contractive bonding algebra homomorphism between adjacent completions. -/
def bond (n : ℕ) : Stage (n + 1) →ₐ[ℂ] Stage n where
  toRingHom := Completion.mapRingHom (preBond n).toRingHom (lipschitzWith_preBond n).continuous
  commutes' c := by
    change Completion.mapRingHom (preBond n).toRingHom
      (lipschitzWith_preBond n).continuous
      ((algebraMap ℂ (PreStage (n + 1)) c : PreStage (n + 1)) : Stage (n + 1)) = _
    rw [Completion.mapRingHom_coe]
    rfl

@[simp] theorem bond_inclusion (n : ℕ) (f : CoefficientSeries) :
    bond n (inclusion (n + 1) f) = inclusion n f := by
  exact Completion.mapRingHom_coe (lipschitzWith_preBond n).continuous _

theorem lipschitzWith_bond (n : ℕ) : LipschitzWith 1 (bond n) :=
  (lipschitzWith_preBond n).completion_map

theorem continuous_bond (n : ℕ) : Continuous (bond n) :=
  (lipschitzWith_bond n).continuous

theorem denseRange_bond (n : ℕ) : DenseRange (bond n) := by
  apply (denseRange_inclusion n).mono
  rintro _ ⟨f, rfl⟩
  exact ⟨inclusion (n + 1) f, bond_inclusion n f⟩

end BanachStages
end AutomaticContinuity
