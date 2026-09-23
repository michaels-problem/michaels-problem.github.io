import AutomaticContinuity.PolynomialFieldArrays
import AutomaticContinuity.HomogeneousFieldEvaluation
import AutomaticContinuity.DirectionalFlowComposition

set_option autoImplicit false

/-!
# One fixed finite complete-field decomposition for a polynomial family

The degree bound determines the entire finite list of factors. Coefficients
are fixed continuous complex-linear functionals of the finite monomial
arrays, so continuous time and holomorphic base dependence are preserved.
-/

noncomputable section

namespace AutomaticContinuity.PolynomialFieldFamily

open PolynomialFieldArrays HomogeneousFieldCoefficientSelection
open HomogeneousFieldDecomposition DirectionalFactors
open scoped BigOperators

abbrev Index (N : ℕ) := Σ m : Fin N, Fin (m.val + 1) ⊕ Fin (m.val + 3)

def count (N : ℕ) : ℕ := Fintype.card (Index N)

def enumeration (N : ℕ) : Fin (count N) ≃ Index N := (Fintype.equivFin (Index N)).symm

def indexedFactor {N : ℕ} : Index N → Factor
  | ⟨m, .inl j⟩ => .overshear (j.val : ℂ) m.val
  | ⟨m, .inr j⟩ => .shear (j.val : ℂ) m.val

def indexedCoefficient {N : ℕ} (i : Index N) : Arrays N →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap {
    toFun a := match i with
      | ⟨m, .inl j⟩ => (coefficients m.val (a m)).1 j
      | ⟨m, .inr j⟩ => (coefficients m.val (a m)).2 j
    map_add' a b := by
      rcases i with ⟨m, j | j⟩ <;> simp only [Pi.add_apply, map_add, Prod.fst_add,
        Prod.snd_add]
    map_smul' c a := by
      rcases i with ⟨m, j | j⟩ <;> simp only [Pi.smul_apply, map_smul, Prod.smul_fst,
        Prod.smul_snd, RingHom.id_apply] }

@[simp] theorem indexedCoefficient_inl (N : ℕ) (a : Arrays N)
    (m : Fin N) (j : Fin (m.val + 1)) :
    indexedCoefficient ⟨m, .inl j⟩ a = (coefficients m.val (a m)).1 j := rfl

@[simp] theorem indexedCoefficient_inr (N : ℕ) (a : Arrays N)
    (m : Fin N) (j : Fin (m.val + 3)) :
    indexedCoefficient ⟨m, .inr j⟩ a = (coefficients m.val (a m)).2 j := rfl

def factor (N : ℕ) (i : ℕ) : Factor :=
  if hi : i < count N then indexedFactor (enumeration N ⟨i, hi⟩) else .shear 0 0

def coefficient (N : ℕ) (i : ℕ) : Arrays N →L[ℂ] ℂ :=
  if hi : i < count N then indexedCoefficient (enumeration N ⟨i, hi⟩) else 0

@[simp] theorem factor_of_lt (N i : ℕ) (hi : i < count N) :
    factor N i = indexedFactor (enumeration N ⟨i, hi⟩) := dite_eq_left hi

@[simp] theorem coefficient_of_lt (N i : ℕ) (hi : i < count N) :
    coefficient N i = indexedCoefficient (enumeration N ⟨i, hi⟩) := dite_eq_left hi

theorem indexed_fieldSum (N : ℕ) (a : Arrays N) (w : ℂ × ℂ) :
    ∑ i : Index N, (indexedFactor i).field (indexedCoefficient i a) w =
      evaluation w (polynomial N a) := by
  rw [Fintype.sum_sigma]
  unfold polynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [Fintype.sum_sum_type]
  have heq := congrArg (evaluation w) (decomposition_of_array m.val (a m))
  simpa only [map_add, map_sum, evaluation_apply, evaluation_shear,
    evaluation_overshear, indexedFactor, indexedCoefficient_inl,
    indexedCoefficient_inr, Factor.field] using heq.symm

/-- The finite prefix used by the actual flow product equals the prescribed
polynomial vector field exactly, for every parameter and every fibre point. -/
theorem fieldSum_eq {P : Type*} (N : ℕ) (a : P → Arrays N) (p : P) (w : ℂ × ℂ) :
    DirectionalFlowComposition.fieldSum (factor N)
      (fun i p => coefficient N i (a p)) (count N) (p, w) =
        evaluation w (polynomial N (a p)) := by
  unfold DirectionalFlowComposition.fieldSum
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [factor_of_lt N _ (Fin.isLt _), coefficient_of_lt N _ (Fin.isLt _)]
  change (∑ i : Fin (count N), (indexedFactor (enumeration N i)).field
    (indexedCoefficient (enumeration N i) (a p)) w) = _
  rw [(enumeration N).sum_comp (fun i : Index N => (indexedFactor i).field
    (indexedCoefficient i (a p)) w)]
  exact indexed_fieldSum N (a p) w

theorem norm_coefficient_le (N i : ℕ) (a : Arrays N) :
    ‖coefficient N i a‖ ≤ ‖coefficient N i‖ * ‖a‖ :=
  (coefficient N i).le_opNorm a

theorem continuousOn_coefficient {P : Type*} [TopologicalSpace P]
    (N i : ℕ) {U : Set P} {a : P → Arrays N} (ha : ContinuousOn a U) :
    ContinuousOn (fun p => coefficient N i (a p)) U :=
  (coefficient N i).continuous.comp_continuousOn ha

theorem differentiableOn_coefficient {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    (N i : ℕ) {U : Set P} {a : P → Arrays N} (ha : DifferentiableOn ℂ a U) :
    DifferentiableOn ℂ (fun p => coefficient N i (a p)) U :=
  (coefficient N i).differentiable.comp_differentiableOn ha

end AutomaticContinuity.PolynomialFieldFamily
