import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-!
# Coefficient algebra foundations

This file implements the coefficient model in Section 2, equation
`eq:coefficient-algebra`, of `automatic_continuity_characters.tex` (22 September 2026).
Lean variable `j : ℕ` corresponds to the manuscript's variable `j + 1`.

The ambient formal series use Mathlib's finite-antidiagonal convolution. The
condition below is absolute summability at every positive integral radius.
No completeness, density, or topological algebra assertion is built into the
definition. Those assertions require separate proofs.
-/

noncomputable section

namespace AutomaticContinuity

/-- Finitely supported nonnegative integer exponents, indexed from zero. -/
abbrev MultiIndex := ℕ →₀ ℕ

/-- The total degree of a monomial. -/
def totalDegree (α : MultiIndex) : ℕ := Finsupp.degree α

@[simp] theorem totalDegree_zero : totalDegree 0 = 0 := by
  exact map_zero Finsupp.degree

@[simp] theorem totalDegree_add (α β : MultiIndex) :
    totalDegree (α + β) = totalDegree α + totalDegree β := by
  exact map_add Finsupp.degree α β

@[simp] theorem totalDegree_single (j n : ℕ) :
    totalDegree (Finsupp.single j n) = n := by
  exact Finsupp.degree_single j n

/-- All complex coefficient families, with formal power-series multiplication. -/
abbrev FormalSeries := MvPowerSeries ℕ ℂ

/-- The nonnegative summand in the coefficient norm at integral radius `r`. -/
def weightedTerm (r : ℕ) (f : FormalSeries) (α : MultiIndex) : ℝ :=
  ‖MvPowerSeries.coeff α f‖ * (r : ℝ) ^ totalDegree α

theorem weightedTerm_nonneg (r : ℕ) (f : FormalSeries) (α : MultiIndex) :
    0 ≤ weightedTerm r f α := by
  exact mul_nonneg (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg r) _)

theorem weightedTerm_mono {r s : ℕ} (hrs : r ≤ s) (f : FormalSeries) (α : MultiIndex) :
    weightedTerm r f α ≤ weightedTerm s f α := by
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Nat.cast_nonneg r) (Nat.cast_le.mpr hrs) _) (norm_nonneg _)

/-- Membership in the manuscript's coefficient algebra: absolute summability
for each positive integer radius. -/
def HasFiniteCoefficientNorms (f : FormalSeries) : Prop :=
  ∀ r : ℕ, 0 < r → Summable (weightedTerm r f)

theorem weightedTerm_add_le (r : ℕ) (f g : FormalSeries) (α : MultiIndex) :
    weightedTerm r (f + g) α ≤ weightedTerm r f α + weightedTerm r g α := by
  simp only [weightedTerm, map_add]
  exact (mul_le_mul_of_nonneg_right (norm_add_le _ _)
    (pow_nonneg (Nat.cast_nonneg r) _)).trans_eq (add_mul _ _ _)

@[simp] theorem weightedTerm_smul (r : ℕ) (c : ℂ) (f : FormalSeries) (α : MultiIndex) :
    weightedTerm r (c • f) α = ‖c‖ * weightedTerm r f α := by
  simp [weightedTerm, mul_assoc]

theorem hasFiniteCoefficientNorms_zero : HasFiniteCoefficientNorms 0 := by
  intro r hr
  change Summable (fun α => weightedTerm r 0 α)
  simp [weightedTerm]

theorem HasFiniteCoefficientNorms.add {f g : FormalSeries}
    (hf : HasFiniteCoefficientNorms f) (hg : HasFiniteCoefficientNorms g) :
    HasFiniteCoefficientNorms (f + g) := by
  intro r hr
  exact Summable.of_nonneg_of_le (weightedTerm_nonneg r (f + g))
    (weightedTerm_add_le r f g) ((hf r hr).add (hg r hr))

theorem HasFiniteCoefficientNorms.smul {f : FormalSeries}
    (hf : HasFiniteCoefficientNorms f) (c : ℂ) :
    HasFiniteCoefficientNorms (c • f) := by
  intro r hr
  change Summable (fun α => weightedTerm r (c • f) α)
  simpa only [weightedTerm_smul] using (hf r hr).mul_left ‖c‖

theorem hasFiniteCoefficientNorms_monomial (α : MultiIndex) (c : ℂ) :
    HasFiniteCoefficientNorms (MvPowerSeries.monomial α c) := by
  intro r hr
  classical
  apply summable_of_ne_finset_zero (s := {α})
  intro β hβ
  have hβα : β ≠ α := by simpa using hβ
  simp [weightedTerm, MvPowerSeries.coeff_monomial_ne hβα]

theorem hasFiniteCoefficientNorms_constant (c : ℂ) :
    HasFiniteCoefficientNorms (MvPowerSeries.C c) := by
  simpa only [MvPowerSeries.monomial_zero_eq_C_apply] using
    hasFiniteCoefficientNorms_monomial 0 c

theorem hasFiniteCoefficientNorms_polynomial (p : MvPolynomial ℕ ℂ) :
    HasFiniteCoefficientNorms (p : FormalSeries) := by
  intro r hr
  apply summable_of_ne_finset_zero (s := p.support)
  intro α hα
  have hc : p.coeff α = 0 := by
    simpa only [MvPolynomial.mem_support_iff, not_not] using hα
  simp [weightedTerm, hc]

/-- The elementary estimate behind absolute convergence of coefficient convolution. -/
theorem weightedTerm_mul_le (r : ℕ) (f g : FormalSeries) (α : MultiIndex) :
    weightedTerm r (f * g) α ≤
      ∑ p ∈ Finset.antidiagonal α, weightedTerm r f p.1 * weightedTerm r g p.2 := by
  classical
  unfold weightedTerm
  rw [MvPowerSeries.coeff_mul]
  calc
    ‖∑ p ∈ Finset.antidiagonal α,
        MvPowerSeries.coeff p.1 f * MvPowerSeries.coeff p.2 g‖ *
          (r : ℝ) ^ totalDegree α ≤
        (∑ p ∈ Finset.antidiagonal α,
          ‖MvPowerSeries.coeff p.1 f * MvPowerSeries.coeff p.2 g‖) *
            (r : ℝ) ^ totalDegree α :=
      mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg (Nat.cast_nonneg r) _)
    _ = ∑ p ∈ Finset.antidiagonal α,
        ‖MvPowerSeries.coeff p.1 f‖ * (r : ℝ) ^ totalDegree p.1 *
          (‖MvPowerSeries.coeff p.2 g‖ * (r : ℝ) ^ totalDegree p.2) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      have hsum : p.1 + p.2 = α := Finset.mem_antidiagonal.mp hp
      rw [← hsum, totalDegree_add, pow_add, norm_mul]
      ring

theorem HasFiniteCoefficientNorms.mul {f g : FormalSeries}
    (hf : HasFiniteCoefficientNorms f) (hg : HasFiniteCoefficientNorms g) :
    HasFiniteCoefficientNorms (f * g) := by
  intro r hr
  have hprod := (hf r hr).mul_of_nonneg (hg r hr)
    (weightedTerm_nonneg r f) (weightedTerm_nonneg r g)
  exact Summable.of_nonneg_of_le (weightedTerm_nonneg r (f * g))
    (weightedTerm_mul_le r f g)
    (summable_sum_mul_antidiagonal_of_summable_mul hprod)

/-- The concrete subalgebra of absolutely summable coefficient families. -/
def coefficientSubalgebra : Subalgebra ℂ FormalSeries where
  carrier := {f | HasFiniteCoefficientNorms f}
  mul_mem' := HasFiniteCoefficientNorms.mul
  add_mem' := HasFiniteCoefficientNorms.add
  algebraMap_mem' := hasFiniteCoefficientNorms_constant

/-- The coefficient algebra `𝓔` of the manuscript. -/
abbrev CoefficientSeries : Type := coefficientSubalgebra

namespace CoefficientSeries

open scoped Topology
open Filter

/-- Underlying coefficient at a given multi-index. -/
def coeff (f : CoefficientSeries) (α : MultiIndex) : ℂ :=
  MvPowerSeries.coeff α (f : FormalSeries)

@[simp] theorem coeff_zero (α : MultiIndex) : coeff 0 α = 0 := rfl

@[simp] theorem coeff_add (f g : CoefficientSeries) (α : MultiIndex) :
    coeff (f + g) α = coeff f α + coeff g α := rfl

@[simp] theorem coeff_sub (f g : CoefficientSeries) (α : MultiIndex) :
    coeff (f - g) α = coeff f α - coeff g α := rfl

@[ext] theorem ext {f g : CoefficientSeries} (h : ∀ α, coeff f α = coeff g α) : f = g :=
  Subtype.ext (MvPowerSeries.ext h)

/-- The coefficient norm at radius `r`. For the defining family, use `r > 0`. -/
def q (r : ℕ) (f : CoefficientSeries) : ℝ :=
  ∑' α, weightedTerm r (f : FormalSeries) α

theorem summable (f : CoefficientSeries) {r : ℕ} (hr : 0 < r) :
    Summable (weightedTerm r (f : FormalSeries)) := f.property r hr

/-- Radius zero also gives a summable family, by comparison with radius one. -/
theorem summable_all (f : CoefficientSeries) (r : ℕ) :
    Summable (weightedTerm r (f : FormalSeries)) := by
  by_cases hr : 0 < r
  · exact f.summable hr
  · have hr0 : r = 0 := Nat.eq_zero_of_not_pos hr
    subst r
    exact Summable.of_nonneg_of_le (weightedTerm_nonneg 0 f)
      (weightedTerm_mono (Nat.zero_le 1) f) (f.summable Nat.one_pos)

theorem q_nonneg (r : ℕ) (f : CoefficientSeries) : 0 ≤ q r f :=
  tsum_nonneg (weightedTerm_nonneg r f)

@[simp] theorem q_zero (r : ℕ) : q r 0 = 0 := by
  simp [q, weightedTerm]

theorem q_add_le (r : ℕ) (f g : CoefficientSeries) : q r (f + g) ≤ q r f + q r g := by
  calc
    q r (f + g) ≤ ∑' α, (weightedTerm r (f : FormalSeries) α +
        weightedTerm r (g : FormalSeries) α) :=
      Summable.tsum_le_tsum (weightedTerm_add_le r f g)
        ((f + g).summable_all r) ((f.summable_all r).add (g.summable_all r))
    _ = q r f + q r g := (f.summable_all r).tsum_add (g.summable_all r)

@[simp] theorem q_smul (r : ℕ) (c : ℂ) (f : CoefficientSeries) :
    q r (c • f) = ‖c‖ * q r f := by
  change (∑' α, weightedTerm r (c • (f : FormalSeries)) α) = ‖c‖ * q r f
  simp only [weightedTerm_smul, tsum_mul_left, q]

@[simp] theorem q_neg (r : ℕ) (f : CoefficientSeries) : q r (-f) = q r f := by
  simpa using q_smul r (-1) f

theorem q_mono {r s : ℕ} (hrs : r ≤ s) (f : CoefficientSeries) : q r f ≤ q s f :=
  Summable.tsum_le_tsum (weightedTerm_mono hrs f) (f.summable_all r) (f.summable_all s)

theorem q_mul_le (r : ℕ) (f g : CoefficientSeries) : q r (f * g) ≤ q r f * q r g := by
  have hprod := (f.summable_all r).mul_of_nonneg (g.summable_all r)
    (weightedTerm_nonneg r f) (weightedTerm_nonneg r g)
  calc
    q r (f * g) ≤ ∑' α, ∑ p ∈ Finset.antidiagonal α,
        weightedTerm r (f : FormalSeries) p.1 * weightedTerm r (g : FormalSeries) p.2 :=
      Summable.tsum_le_tsum (weightedTerm_mul_le r f g) ((f * g).summable_all r)
        (summable_sum_mul_antidiagonal_of_summable_mul hprod)
    _ = q r f * q r g :=
      ((f.summable_all r).tsum_mul_tsum_eq_tsum_sum_antidiagonal
        (g.summable_all r) hprod).symm

/-- The coefficient norm as a bundled complex seminorm. It is a norm when `r > 0`. -/
def qSeminorm (r : ℕ) : Seminorm ℂ CoefficientSeries where
  toFun := q r
  map_zero' := q_zero r
  add_le' := q_add_le r
  neg' := q_neg r
  smul' := q_smul r

@[simp] theorem qSeminorm_apply (r : ℕ) (f : CoefficientSeries) :
    qSeminorm r f = q r f := rfl

theorem weightedTerm_le_q (r : ℕ) (f : CoefficientSeries) (α : MultiIndex) :
    weightedTerm r (f : FormalSeries) α ≤ q r f :=
  (f.summable_all r).le_tsum α (fun β _ => weightedTerm_nonneg r f β)

theorem norm_coeff_le_q_one (f : CoefficientSeries) (α : MultiIndex) :
    ‖coeff f α‖ ≤ q 1 f := by
  simpa [weightedTerm, coeff] using weightedTerm_le_q 1 f α

theorem q_eq_zero_iff {r : ℕ} (hr : 0 < r) (f : CoefficientSeries) :
    q r f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    apply ext
    intro α
    have hbound := (norm_coeff_le_q_one f α).trans (q_mono hr f)
    rw [hf] at hbound
    have hcoeff : coeff f α = 0 := norm_le_zero_iff.mp hbound
    simpa [coeff] using hcoeff
  · rintro rfl
    exact q_zero r

/-- A single monomial with coefficient `c`. -/
def monomial (α : MultiIndex) (c : ℂ) : CoefficientSeries :=
  ⟨MvPowerSeries.monomial α c, hasFiniteCoefficientNorms_monomial α c⟩

/-- A constant coefficient series. -/
def constant (c : ℂ) : CoefficientSeries :=
  ⟨MvPowerSeries.C c, hasFiniteCoefficientNorms_constant c⟩

/-- Coordinate `j`, corresponding to `z_(j+1)` in the manuscript. -/
def coordinate (j : ℕ) : CoefficientSeries := monomial (Finsupp.single j 1) 1

@[simp] theorem coeff_monomial (α β : MultiIndex) (c : ℂ) :
    coeff (monomial α c) β = if β = α then c else 0 := by
  classical
  exact MvPowerSeries.coeff_monomial β α c

@[simp] theorem q_monomial (r : ℕ) (α : MultiIndex) (c : ℂ) :
    q r (monomial α c) = ‖c‖ * (r : ℝ) ^ totalDegree α := by
  classical
  unfold q
  rw [tsum_eq_single α]
  · simp [weightedTerm, monomial]
  · intro β hβα
    simp [weightedTerm, monomial, MvPowerSeries.coeff_monomial_ne hβα]

@[simp] theorem q_constant (r : ℕ) (c : ℂ) : q r (constant c) = ‖c‖ := by
  change q r (monomial 0 c) = ‖c‖
  simp

@[simp] theorem q_coordinate (r j : ℕ) : q r (coordinate j) = r := by
  simp [coordinate]

/-- The canonical inclusion of finite polynomials into the coefficient algebra. -/
def ofPolynomial (p : MvPolynomial ℕ ℂ) : CoefficientSeries :=
  ⟨(p : FormalSeries), hasFiniteCoefficientNorms_polynomial p⟩

@[simp] theorem coeff_ofPolynomial (p : MvPolynomial ℕ ℂ) (α : MultiIndex) :
    coeff (ofPolynomial p) α = p.coeff α := rfl

theorem ofPolynomial_injective : Function.Injective ofPolynomial := by
  intro p q hpq
  exact MvPolynomial.coe_injective ℕ ℂ (congrArg Subtype.val hpq)

/-- Polynomial inclusion preserves the complex algebra structure. -/
def polynomialHom : MvPolynomial ℕ ℂ →ₐ[ℂ] CoefficientSeries where
  toFun := ofPolynomial
  map_zero' := Subtype.ext MvPolynomial.coe_zero
  map_one' := Subtype.ext MvPolynomial.coe_one
  map_add' p q := Subtype.ext (MvPolynomial.coe_add p q)
  map_mul' p q := Subtype.ext (MvPolynomial.coe_mul p q)
  commutes' c := Subtype.ext (MvPolynomial.coe_C c)

@[simp] theorem polynomialHom_apply (p : MvPolynomial ℕ ℂ) :
    polynomialHom p = ofPolynomial p := rfl

@[simp] theorem polynomialHom_X (j : ℕ) :
    polynomialHom (MvPolynomial.X j) = coordinate j := by
  apply Subtype.ext
  exact MvPolynomial.coe_X j

@[simp] theorem polynomialHom_C (c : ℂ) :
    polynomialHom (MvPolynomial.C c) = constant c := by
  apply Subtype.ext
  exact MvPolynomial.coe_C c

/-- The polynomial retaining exactly the coefficients in the finite set `s`. -/
def truncationPolynomial (s : Finset MultiIndex) (f : CoefficientSeries) : MvPolynomial ℕ ℂ :=
  ∑ α ∈ s, MvPolynomial.monomial α (coeff f α)

/-- Finite coefficient truncation, as an element of the coefficient algebra. -/
def truncate (s : Finset MultiIndex) (f : CoefficientSeries) : CoefficientSeries :=
  ofPolynomial (truncationPolynomial s f)

@[simp] theorem coeff_truncate (s : Finset MultiIndex) (f : CoefficientSeries)
    (α : MultiIndex) : coeff (truncate s f) α = if α ∈ s then coeff f α else 0 := by
  classical
  simp [truncate, truncationPolynomial, MvPolynomial.coeff_monomial]

theorem q_truncate (r : ℕ) (s : Finset MultiIndex) (f : CoefficientSeries) :
    q r (truncate s f) = ∑ α ∈ s, weightedTerm r (f : FormalSeries) α := by
  classical
  unfold q
  rw [tsum_eq_sum (s := s)]
  · apply Finset.sum_congr rfl
    intro α hα
    change ‖coeff (truncate s f) α‖ * _ = ‖coeff f α‖ * _
    simp [coeff_truncate, hα]
  · intro α hα
    change ‖coeff (truncate s f) α‖ * _ = 0
    simp [coeff_truncate, hα]

theorem q_sub_truncate_add (r : ℕ) (s : Finset MultiIndex) (f : CoefficientSeries) :
    q r (f - truncate s f) + q r (truncate s f) = q r f := by
  classical
  unfold q
  rw [← (summable_all (f - truncate s f) r).tsum_add (summable_all (truncate s f) r)]
  apply tsum_congr
  intro α
  change ‖coeff (f - truncate s f) α‖ * _ + ‖coeff (truncate s f) α‖ * _ =
    ‖coeff f α‖ * _
  simp only [coeff_sub, coeff_truncate]
  split_ifs <;> simp

/-- The coefficient norm of the omitted tail is the total norm minus the finite partial sum. -/
theorem q_sub_truncate (r : ℕ) (s : Finset MultiIndex) (f : CoefficientSeries) :
    q r (f - truncate s f) = q r f - ∑ α ∈ s, weightedTerm r (f : FormalSeries) α := by
  have h := q_sub_truncate_add r s f
  rw [q_truncate] at h
  linarith

/-- Truncations converge in every coefficient norm. The filter indexes all finite
sets of monomials by inclusion, so no enumeration choice is hidden in this statement. -/
theorem tendsto_q_sub_truncate (r : ℕ) (f : CoefficientSeries) :
    Tendsto (fun s : Finset MultiIndex => q r (f - truncate s f)) atTop (𝓝 0) := by
  simp_rw [q_sub_truncate]
  simpa only [q, sub_self, SummationFilter.unconditional_filter] using
    (tendsto_const_nhds (x := q r f)).sub (summable_all f r).hasSum

theorem tendsto_q_truncate_sub (r : ℕ) (f : CoefficientSeries) :
    Tendsto (fun s : Finset MultiIndex => q r (truncate s f - f)) atTop (𝓝 0) := by
  have heq (s : Finset MultiIndex) : q r (truncate s f - f) = q r (f - truncate s f) := by
    rw [← neg_sub (truncate s f) f, q_neg]
  simpa only [heq] using tendsto_q_sub_truncate r f

end CoefficientSeries

end AutomaticContinuity
