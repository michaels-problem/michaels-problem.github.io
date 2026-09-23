import AutomaticContinuity.FiniteGeometry
import AutomaticContinuity.PairLinearSeparation
import AutomaticContinuity.FlagCompactGraph
import AutomaticContinuity.PolynomialConvexity
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false

/-!
# Polynomial separation for compact forbidden flag graphs

The variables consist of the finite source coordinates and two target
coordinates. The separating polynomials below will supply the elementary
polynomial-convexity input for the variable-fibre Euclidean geometry. They do
not assert a holomorphic approximation or Oka theorem.
-/

noncomputable section

namespace AutomaticContinuity.FlagPolynomialSeparation

abbrev Variables (n : ℕ) := Fin n ⊕ Bool
abbrev Point (n : ℕ) := FinitePoint n × (ℂ × ℂ)
abbrev Polynomial (n : ℕ) := MvPolynomial (Variables n) ℂ

def coordinates {n : ℕ} (p : Point n) : Variables n → ℂ :=
  Sum.elim p.1 (fun b => if b then p.2.2 else p.2.1)

/-- These are all the ordinary complex coordinates, through a linear
equivalence rather than an arbitrary non-injective encoding. -/
def coordinatesLinearEquiv (n : ℕ) : Point n ≃ₗ[ℂ] (Variables n → ℂ) where
  toFun := coordinates
  invFun := fun f => ((fun j => f (Sum.inl j)), (f (Sum.inr false), f (Sum.inr true)))
  left_inv _ := rfl
  right_inv f := by
    funext i
    rcases i with j | b
    · rfl
    · cases b <;> rfl
  map_add' p q := by
    funext i
    rcases i with j | b
    · rfl
    · cases b <;> rfl
  map_smul' c p := by
    funext i
    rcases i with j | b
    · rfl
    · cases b <;> rfl

def evaluate {n : ℕ} (p : Point n) : Polynomial n →+* ℂ :=
  MvPolynomial.eval (coordinates p)

def targetLinearPolynomial (n : ℕ) (ℓ : (ℂ × ℂ) →ₗ[ℂ] ℂ) : Polynomial n :=
  MvPolynomial.C (ℓ (1, 0)) * MvPolynomial.X (Sum.inr false) +
    MvPolynomial.C (ℓ (0, 1)) * MvPolynomial.X (Sum.inr true)

@[simp] theorem evaluate_targetLinearPolynomial {n : ℕ}
    (ℓ : (ℂ × ℂ) →ₗ[ℂ] ℂ) (p : Point n) :
    evaluate p (targetLinearPolynomial n ℓ) = ℓ p.2 := by
  have hp : p.2 = p.2.1 • ((1, 0) : ℂ × ℂ) + p.2.2 • ((0, 1) : ℂ × ℂ) := by
    ext <;> simp
  conv_rhs => rw [hp, map_add, map_smul, map_smul]
  simp [evaluate, targetLinearPolynomial, coordinates, mul_comm]

theorem exists_power_separation {C a r s : ℝ} (hC : 0 ≤ C)
    (ha : 0 < a) (hr : 0 ≤ r) (hrs : r < s) :
    ∃ m : ℕ, C * r ^ m < a * s ^ m := by
  by_cases hC0 : C = 0
  · exact ⟨0, by simpa [hC0] using ha⟩
  have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
  have hsp : 0 < s := hr.trans_lt hrs
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos ha hCp)
    ((div_lt_one hsp).mpr hrs)
  rw [div_pow] at hm
  exact ⟨m, by simpa [mul_comm] using
    (div_lt_div_iff₀ (pow_pos hsp m) hCp).mp hm⟩

/-- A polynomial with a strict uniform modulus gap at the exterior point. -/
def Separates {n : ℕ} (K : Set (Point n)) (p : Point n) (P : Polynomial n) : Prop :=
  ∃ C : ℝ, (∀ q ∈ K, ‖evaluate q P‖ ≤ C) ∧ C < ‖evaluate p P‖

def sourceOffsetPolynomial {n : ℕ} (j : Fin n) : Polynomial n :=
  MvPolynomial.X (Sum.inl j) - MvPolynomial.C (prescribedCoordinate j.val)

@[simp] theorem evaluate_sourceOffsetPolynomial {n : ℕ} (j : Fin n) (p : Point n) :
    evaluate p (sourceOffsetPolynomial j) = p.1 j - prescribedCoordinate j.val := by
  simp [evaluate, sourceOffsetPolynomial, coordinates]

theorem separates_of_coordinate_gap {n : ℕ} {K : Set (Point n)} {p : Point n}
    (j : Fin n) (hp : p.1 j ≠ prescribedCoordinate j.val)
    (hK : ∀ q ∈ K, q.1 j = prescribedCoordinate j.val) :
    Separates K p (sourceOffsetPolynomial j) := by
  refine ⟨0, ?_, ?_⟩
  · intro q hq
    simp [hK q hq]
  · simpa using norm_pos_iff.mpr (sub_ne_zero.mpr hp)

/-- A power of the norming linear functional dominates the bounded coordinate
factor. The factor vanishes identically on all deeper flag components. -/
theorem exists_separator_of_flag_gap {n : ℕ} {K : Set (Point n)} {p : Point n}
    {R : ℝ} (hR : 0 ≤ R) (j : Fin n)
    (hpj : p.1 j ≠ prescribedCoordinate j.val)
    (hpy : (j.val : ℝ) < euclideanPairNorm p.2)
    (hK : ∀ q ∈ K, q.1 ∈ polydisc n R ∧
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ q.1 ∈ finiteFlag n k ∧
        euclideanPairNorm q.2 ≤ (k : ℝ)) :
    ∃ P : Polynomial n, Separates K p P := by
  have hpy0 : 0 < euclideanPairNorm p.2 := (Nat.cast_nonneg j.val).trans_lt hpy
  obtain ⟨ℓ, hℓ, hℓp⟩ := exists_pair_norming_functional p.2 hpy0
  let C : ℝ := R + ‖prescribedCoordinate j.val‖
  have hC : 0 ≤ C := add_nonneg hR (norm_nonneg _)
  have ha : 0 < ‖p.1 j - prescribedCoordinate j.val‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hpj)
  obtain ⟨m, hm⟩ := exists_power_separation hC ha (Nat.cast_nonneg j.val) hpy
  refine ⟨sourceOffsetPolynomial j * targetLinearPolynomial n ℓ ^ m,
    C * (j.val : ℝ) ^ m, ?_, ?_⟩
  · intro q hq
    obtain ⟨hqR, k, _hk, _hkn, hqflag, hqy⟩ := hK q hq
    simp only [map_mul, map_pow, evaluate_sourceOffsetPolynomial,
      evaluate_targetLinearPolynomial, norm_mul, norm_pow]
    by_cases hjk : j.val < k
    · rw [hqflag j hjk, sub_self, norm_zero, zero_mul]
      exact mul_nonneg hC (pow_nonneg (Nat.cast_nonneg j.val) m)
    · have hkj : (k : ℝ) ≤ j.val := Nat.cast_le.mpr (Nat.le_of_not_gt hjk)
      have hlin : ‖ℓ q.2‖ ≤ j.val := (hℓ q.2).trans (hqy.trans hkj)
      have hoff : ‖q.1 j - prescribedCoordinate j.val‖ ≤ C :=
        (norm_sub_le _ _).trans (add_le_add (hqR j) le_rfl)
      exact mul_le_mul hoff (pow_le_pow_left₀ (norm_nonneg _) hlin m)
        (pow_nonneg (norm_nonneg _) m) hC
  · simpa only [map_mul, map_pow, evaluate_sourceOffsetPolynomial,
      evaluate_targetLinearPolynomial, norm_mul, norm_pow, hℓp] using hm

/-- When there are no deeper coordinates, a single target linear functional
separates from every ball occurring in the finite graph. -/
theorem exists_separator_of_target_gap {n : ℕ} {K : Set (Point n)} {p : Point n}
    (hpy : (n : ℝ) < euclideanPairNorm p.2)
    (hK : ∀ q ∈ K, euclideanPairNorm q.2 ≤ (n : ℝ)) :
    ∃ P : Polynomial n, Separates K p P := by
  obtain ⟨ℓ, hℓ, hℓp⟩ := exists_pair_norming_functional p.2
    ((Nat.cast_nonneg n).trans_lt hpy)
  refine ⟨targetLinearPolynomial n ℓ, n, ?_, ?_⟩
  · intro q hq
    simpa only [evaluate_targetLinearPolynomial] using (hℓ q.2).trans (hK q hq)
  · simpa only [evaluate_targetLinearPolynomial, hℓp] using hpy

/-- The compact flag-graph membership description alone yields a genuine
polynomial separator at every exterior point. Dimension zero is included. -/
theorem exists_separator_of_membership {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (K : Set (Point n))
    (hK : ∀ q : Point n, q ∈ K ↔ q.1 ∈ polydisc n R ∧
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ q.1 ∈ finiteFlag n k ∧
        euclideanPairNorm q.2 ≤ (k : ℝ))
    (p : Point n) (hp : p ∉ K) :
    ∃ P : Polynomial n, Separates K p P := by
  classical
  by_cases hn : n = 0
  · refine ⟨1, 0, ?_, ?_⟩
    · intro q hq
      obtain ⟨_, k, hk, hkn, _⟩ := (hK q).mp hq
      omega
    · simp [evaluate]
  by_cases hpR : p.1 ∈ polydisc n R
  · by_cases hbad : ∃ j : Fin n, p.1 j ≠ prescribedCoordinate j.val
    · let bad : Finset (Fin n) := Finset.univ.filter
        (fun j => p.1 j ≠ prescribedCoordinate j.val)
      have hbadne : bad.Nonempty := by
        obtain ⟨j, hj⟩ := hbad
        exact ⟨j, by simp [bad, hj]⟩
      let j : Fin n := bad.min' hbadne
      have hjmem : j ∈ bad := Finset.min'_mem bad hbadne
      have hpj : p.1 j ≠ prescribedCoordinate j.val := (Finset.mem_filter.mp hjmem).2
      have hprefix : p.1 ∈ finiteFlag n j.val := by
        intro i hi
        by_contra hpi
        have himem : i ∈ bad := by simp [bad, hpi]
        have hji : j ≤ i := Finset.min'_le bad i himem
        exact (Nat.not_lt_of_ge hji) hi
      by_cases hj0 : j.val = 0
      · refine ⟨sourceOffsetPolynomial j, separates_of_coordinate_gap j hpj ?_⟩
        intro q hq
        obtain ⟨_, k, hk, _, hqflag, _⟩ := (hK q).mp hq
        exact hqflag j (by omega)
      · have hpy : (j.val : ℝ) < euclideanPairNorm p.2 := by
          by_contra hnot
          apply hp
          exact (hK p).mpr ⟨hpR, j.val, by omega, j.isLt.le, hprefix,
            le_of_not_gt hnot⟩
        exact exists_separator_of_flag_gap hR j hpj hpy (fun q hq => (hK q).mp hq)
    · have hprefix : p.1 ∈ finiteFlag n n := by
        intro j _hj
        exact not_not.mp (fun hj => hbad ⟨j, hj⟩)
      have hpy : (n : ℝ) < euclideanPairNorm p.2 := by
        by_contra hnot
        apply hp
        exact (hK p).mpr ⟨hpR, n, Nat.one_le_iff_ne_zero.mpr hn, le_rfl,
          hprefix, le_of_not_gt hnot⟩
      apply exists_separator_of_target_gap hpy
      intro q hq
      obtain ⟨_, k, _, hkn, _, hqy⟩ := (hK q).mp hq
      exact hqy.trans (Nat.cast_le.mpr hkn)
  · change ¬ ∀ j : Fin n, ‖p.1 j‖ ≤ R at hpR
    obtain ⟨j, hj⟩ := not_forall.mp hpR
    refine ⟨MvPolynomial.X (Sum.inl j), R, ?_, ?_⟩
    · intro q hq
      simpa [evaluate, coordinates] using ((hK q).mp hq).1 j
    · simpa [evaluate, coordinates] using lt_of_not_ge hj

/-- Every point outside the actual compact forbidden graph has a strict
polynomial separator in the complete source and target coordinates. -/
theorem exists_separator_compactForbiddenGraph (n : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (p : Point n) (hp : p ∉ FlagTotalSpace.compactForbiddenGraph n R) :
    ∃ P : Polynomial n, Separates (FlagTotalSpace.compactForbiddenGraph n R) p P :=
  exists_separator_of_membership hR _
    (fun _ => FlagTotalSpace.mem_compactForbiddenGraph_iff) p hp

/-- The compact forbidden graph is polynomially convex in its actual complex
coordinates. This is an elementary geometric input, not an Oka conclusion. -/
theorem isPolynomiallyConvex_compactForbiddenGraph (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    IsPolynomiallyConvexOf coordinates (FlagTotalSpace.compactForbiddenGraph n R) := by
  rw [isPolynomiallyConvexOf_iff_separation]
  intro p hp
  exact exists_separator_compactForbiddenGraph n hR p hp

end AutomaticContinuity.FlagPolynomialSeparation
