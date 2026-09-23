import AutomaticContinuity.HomogeneousFieldEvaluation

set_option autoImplicit false

/-!
# All polynomial vector fields vanishing at zero are finite sums of complete fields

The degree bound fixes one finite index set for the decomposition. Constant
terms are excluded by actual evaluation at zero, so every resulting shear
and overshear fixes the origin.
-/

noncomputable section

namespace AutomaticContinuity.HomogeneousFieldDecomposition

open MvPolynomial HomogeneousPowerBasis
open scoped BigOperators

theorem sum_positive_homogeneousComponents (N : ℕ) (p : Poly)
    (hp : p.totalDegree ≤ N) (hzero : p.coeff 0 = 0) :
    ∑ m : Fin N, homogeneousComponent (m.val + 1) p = p := by
  have heq : (∑ i ∈ Finset.range (p.totalDegree + 1), homogeneousComponent i p) =
      ∑ i ∈ Finset.range (N + 1), homogeneousComponent i p := by
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hp))
    intro i hi hnot
    exact homogeneousComponent_eq_zero i p (by
      simp only [Finset.mem_range] at hnot
      omega)
  rw [sum_homogeneousComponent] at heq
  rw [Finset.sum_range_succ'] at heq
  have hs : (∑ k ∈ Finset.range N, homogeneousComponent (k + 1) p) = p := by
    simpa only [homogeneousComponent_zero, hzero, map_zero, add_zero] using heq.symm
  rw [← Fin.sum_univ_eq_sum_range] at hs
  exact hs

/-- A degree bound yields a common finite decomposition, also when the
field is zero or the bound is zero. -/
theorem exists_polynomial_decomposition (N : ℕ) (P Q : Poly)
    (hP : P.totalDegree ≤ N) (hQ : Q.totalDegree ≤ N)
    (hPzero : eval (0 : Fin 2 → ℂ) P = 0) (hQzero : eval (0 : Fin 2 → ℂ) Q = 0) :
    ∃ c : (m : Fin N) → Fin (m.val + 1) → ℂ,
      ∃ b : (m : Fin N) → Fin (m.val + 3) → ℂ,
      (P, Q) = (∑ m : Fin N, ∑ j : Fin (m.val + 1),
        c m j • overshear (j.val : ℂ) m.val) +
        ∑ m : Fin N, ∑ j : Fin (m.val + 3), b m j • shear (j.val : ℂ) (m.val + 1) := by
  classical
  have hcomp (m : Fin N) := exists_decomposition m.val
    (homogeneousComponent (m.val + 1) P) (homogeneousComponent (m.val + 1) Q)
    (homogeneousComponent_isHomogeneous _ _) (homogeneousComponent_isHomogeneous _ _)
  choose c b hcb using hcomp
  refine ⟨c, b, ?_⟩
  have hPs : ∑ m : Fin N, homogeneousComponent (m.val + 1) P = P :=
    sum_positive_homogeneousComponents N P hP (by
      simpa only [eval_zero, constantCoeff_eq] using hPzero)
  have hQs : ∑ m : Fin N, homogeneousComponent (m.val + 1) Q = Q :=
    sum_positive_homogeneousComponents N Q hQ (by
      simpa only [eval_zero, constantCoeff_eq] using hQzero)
  calc
    (P, Q) = ∑ m : Fin N,
        (homogeneousComponent (m.val + 1) P, homogeneousComponent (m.val + 1) Q) := by
      apply Prod.ext <;> simp only [Prod.fst_sum, Prod.snd_sum, hPs, hQs]
    _ = _ := by simp only [hcb, Finset.sum_add_distrib]

/-- The finite polynomial identity is exactly a sum of the explicit vector
fields with complete origin-fixing flows, at every point of `ℂ²`. -/
theorem exists_polynomial_evaluated_decomposition (N : ℕ) (P Q : Poly)
    (hP : P.totalDegree ≤ N) (hQ : Q.totalDegree ≤ N)
    (hPzero : eval (0 : Fin 2 → ℂ) P = 0) (hQzero : eval (0 : Fin 2 → ℂ) Q = 0) :
    ∃ c : (m : Fin N) → Fin (m.val + 1) → ℂ,
      ∃ b : (m : Fin N) → Fin (m.val + 3) → ℂ,
      ∀ w : ℂ × ℂ, (eval ![w.1, w.2] P, eval ![w.1, w.2] Q) =
        (∑ m : Fin N, ∑ j : Fin (m.val + 1),
          DirectionalCompleteFlows.overshearField (j.val : ℂ) m.val (c m j) w) +
        ∑ m : Fin N, ∑ j : Fin (m.val + 3),
          DirectionalCompleteFlows.shearField (j.val : ℂ) (m.val + 1) (b m j) w := by
  obtain ⟨c, b, hb⟩ := exists_polynomial_decomposition N P Q hP hQ hPzero hQzero
  refine ⟨c, b, fun w => ?_⟩
  have heq := congrArg (evaluation w) hb
  simpa only [map_add, map_sum, evaluation_apply, evaluation_shear,
    evaluation_overshear] using heq

end AutomaticContinuity.HomogeneousFieldDecomposition
