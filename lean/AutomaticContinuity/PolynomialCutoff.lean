import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# An explicit polynomial cutoff from two small value discs

Iterating `H(z) = 3z² - 2z³` contracts the closed radius-`1/8` discs around
zero and one toward their respective centers. Substituting an existing
multivariate polynomial in these iterates gives arbitrarily accurate polynomial
cutoffs on any two sets where that polynomial lies in the respective discs.
No compactness, Runge theorem, or polynomial separation theorem is assumed.
-/

noncomputable section

namespace AutomaticContinuity.PolynomialCutoff

open Set

universe u

/-- The cubic polynomial with attracting fixed points zero and one. -/
def smoothStep (z : ℂ) : ℂ := 3 * z ^ 2 - 2 * z ^ 3

@[simp] theorem smoothStep_zero : smoothStep 0 = 0 := by norm_num [smoothStep]

@[simp] theorem smoothStep_one : smoothStep 1 = 1 := by norm_num [smoothStep]

theorem smoothStep_one_sub (z : ℂ) : smoothStep (1 - z) = 1 - smoothStep z := by
  dsimp [smoothStep]
  ring

theorem norm_smoothStep_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 8) :
    ‖smoothStep z‖ ≤ (1 / 2 : ℝ) * ‖z‖ := by
  have hz0 := norm_nonneg z
  have hsq : ‖z‖ ^ 2 ≤ ‖z‖ / 8 := by nlinarith
  have hcube : ‖z‖ ^ 3 ≤ ‖z‖ / 64 := by
    have := mul_le_mul_of_nonneg_left hsq hz0
    nlinarith
  calc
    ‖smoothStep z‖ ≤ ‖(3 : ℂ) * z ^ 2‖ + ‖(2 : ℂ) * z ^ 3‖ := norm_sub_le _ _
    _ = 3 * ‖z‖ ^ 2 + 2 * ‖z‖ ^ 3 := by norm_num [norm_mul, norm_pow]
    _ ≤ (1 / 2 : ℝ) * ‖z‖ := by nlinarith

theorem norm_smoothStep_sub_one_le {z : ℂ} (hz : ‖z - 1‖ ≤ 1 / 8) :
    ‖smoothStep z - 1‖ ≤ (1 / 2 : ℝ) * ‖z - 1‖ := by
  have h := norm_smoothStep_le (z := 1 - z) (by simpa only [norm_sub_rev] using hz)
  simpa only [smoothStep_one_sub, norm_sub_rev] using h

/-- Polynomial substitution by the cubic cutoff, iterated `n` times. -/
def iterate {ι : Type u} (q : MvPolynomial ι ℂ) : ℕ → MvPolynomial ι ℂ
  | 0 => q
  | n + 1 => 3 * iterate q n ^ 2 - 2 * iterate q n ^ 3

@[simp] theorem eval_iterate_zero {ι : Type u} (q : MvPolynomial ι ℂ) (x : ι → ℂ) :
    MvPolynomial.eval x (iterate q 0) = MvPolynomial.eval x q := rfl

theorem eval_iterate_succ {ι : Type u} (q : MvPolynomial ι ℂ) (x : ι → ℂ) (n : ℕ) :
    MvPolynomial.eval x (iterate q (n + 1)) =
      smoothStep (MvPolynomial.eval x (iterate q n)) := by
  simp only [iterate, smoothStep, map_sub, map_mul, map_pow, map_ofNat]

/-- The cutoff is an actual multivariate polynomial, and its evaluation equals
iteration of the scalar cubic on the original polynomial value. -/
theorem eval_iterate {ι : Type u} (q : MvPolynomial ι ℂ) (x : ι → ℂ) (n : ℕ) :
    MvPolynomial.eval x (iterate q n) = smoothStep^[n] (MvPolynomial.eval x q) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [eval_iterate_succ, Function.iterate_succ_apply', ih]

theorem norm_eval_iterate_le {ι : Type u} (q : MvPolynomial ι ℂ) (x : ι → ℂ)
    (hx : ‖MvPolynomial.eval x q‖ ≤ 1 / 8) (n : ℕ) :
    ‖MvPolynomial.eval x (iterate q n)‖ ≤ (1 / 2 : ℝ) ^ n / 8 := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      have hpow : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hsmall : ‖MvPolynomial.eval x (iterate q n)‖ ≤ 1 / 8 := by linarith
      rw [eval_iterate_succ]
      calc
        ‖smoothStep (MvPolynomial.eval x (iterate q n))‖ ≤
            (1 / 2 : ℝ) * ‖MvPolynomial.eval x (iterate q n)‖ := norm_smoothStep_le hsmall
        _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ n / 8) := by linarith
        _ = (1 / 2 : ℝ) ^ (n + 1) / 8 := by rw [pow_succ]; ring

theorem norm_eval_iterate_sub_one_le {ι : Type u} (q : MvPolynomial ι ℂ) (x : ι → ℂ)
    (hx : ‖MvPolynomial.eval x q - 1‖ ≤ 1 / 8) (n : ℕ) :
    ‖MvPolynomial.eval x (iterate q n) - 1‖ ≤ (1 / 2 : ℝ) ^ n / 8 := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      have hpow : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hsmall : ‖MvPolynomial.eval x (iterate q n) - 1‖ ≤ 1 / 8 := by linarith
      rw [eval_iterate_succ]
      calc
        ‖smoothStep (MvPolynomial.eval x (iterate q n)) - 1‖ ≤
            (1 / 2 : ℝ) * ‖MvPolynomial.eval x (iterate q n) - 1‖ :=
          norm_smoothStep_sub_one_le hsmall
        _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ n / 8) := by linarith
        _ = (1 / 2 : ℝ) ^ (n + 1) / 8 := by rw [pow_succ]; ring

theorem eval_iterate_eq_zero {ι : Type u} (q : MvPolynomial ι ℂ) (x : ι → ℂ)
    (hx : MvPolynomial.eval x q = 0) (n : ℕ) :
    MvPolynomial.eval x (iterate q n) = 0 := by
  induction n with
  | zero => exact hx
  | succ n ih => simp only [eval_iterate_succ, ih, smoothStep_zero]

theorem eval_iterate_eq_one {ι : Type u} (q : MvPolynomial ι ℂ) (x : ι → ℂ)
    (hx : MvPolynomial.eval x q = 1) (n : ℕ) :
    MvPolynomial.eval x (iterate q n) = 1 := by
  induction n with
  | zero => exact hx
  | succ n ih => simp only [eval_iterate_succ, ih, smoothStep_one]

/-- Once a polynomial sends the two sets into the small discs around zero and
one, cubic iteration produces an arbitrarily accurate actual polynomial cutoff.
The values on its exact zero and one fibres are preserved as well. -/
theorem exists_polynomial_cutoff {ι : Type u} (K L : Set (ι → ℂ))
    (q : MvPolynomial ι ℂ)
    (hK : ∀ x ∈ K, ‖MvPolynomial.eval x q‖ ≤ 1 / 8)
    (hL : ∀ x ∈ L, ‖MvPolynomial.eval x q - 1‖ ≤ 1 / 8)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial ι ℂ,
      (∀ x ∈ K, ‖MvPolynomial.eval x p‖ < ε) ∧
      (∀ x ∈ L, ‖MvPolynomial.eval x p - 1‖ < ε) ∧
      (∀ x, MvPolynomial.eval x q = 0 → MvPolynomial.eval x p = 0) ∧
      (∀ x, MvPolynomial.eval x q = 1 → MvPolynomial.eval x p = 1) := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < 8 * ε)
    (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨iterate q n, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (norm_eval_iterate_le q x (hK x hx) n).trans_lt (by linarith)
  · intro x hx
    exact (norm_eval_iterate_sub_one_le q x (hL x hx) n).trans_lt (by linarith)
  · intro x hx
    exact eval_iterate_eq_zero q x hx n
  · intro x hx
    exact eval_iterate_eq_one q x hx n

end AutomaticContinuity.PolynomialCutoff
