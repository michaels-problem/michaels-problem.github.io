import AutomaticContinuity.ArensAssembly
import AutomaticContinuity.ArensBanach
import AutomaticContinuity.ProofObligations

set_option autoImplicit false

/-!
# Arens finite interpolation for the concrete coefficient algebra

If no continuous character matches a finite tuple, every Banach-stage Bézout
equation for the translated tuple has a solution. The compatible-solution and
reconstruction theorems produce a solution in the coefficient algebra itself.
Applying the original algebraic character then contradicts `0 ≠ 1`.
No continuity of the original character is used.
-/

noncomputable section

namespace AutomaticContinuity

open CoefficientSeries BanachStages

/-- Any algebraic character on the coefficient algebra agrees on each finite
set with some continuous character. -/
theorem arensInterpolation : ArensInterpolationStatement := by
  classical
  intro φ s
  by_contra hno
  let a : s → CoefficientSeries := fun i =>
    i.val - algebraMap ℂ CoefficientSeries (φ i.val)
  have hSol (n : ℕ) : Nonempty (Bezout.Solution (fun i : s => inclusion n (a i))) := by
    rcases Arens.solution_or_character (fun i : s => inclusion n (a i)) with
      hSol | ⟨η, hη, hzero⟩
    · exact hSol
    · exfalso
      apply hno
      refine ⟨η.comp (inclusion n), hη.comp (continuous_inclusion n), ?_⟩
      intro f hf
      have hvalue : (η.comp (inclusion n)) f - φ f = 0 := by
        simpa [a] using hzero ⟨f, hf⟩
      exact sub_eq_zero.mp hvalue
  obtain ⟨y⟩ := Arens.solution_of_stageSolutions a hSol
  have ha : ∀ i : s, φ (a i) = 0 := by
    intro i
    simp [a]
  have hcontradiction : (0 : ℂ) = 1 := by
    calc
      0 = φ (Bezout.pairing a y.val) := by simp [Bezout.pairing, ha]
      _ = 1 := by rw [y.property, map_one]
  exact zero_ne_one hcontradiction

end AutomaticContinuity
