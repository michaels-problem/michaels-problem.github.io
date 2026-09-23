import AutomaticContinuity.RadialPolynomialPush
import AutomaticContinuity.RadialSeparatorPropagation

set_option autoImplicit false

/-! # Coherent radial push iteration on a fixed compact base

A transition retains the actual compact obstacle, its actual polynomial
separator, and local holomorphy over the original open parameter domain.
The chosen automorphism and its inverse are controlled on the protected
cylinder. No limiting domain or limiting biholomorphism is assumed.
-/

noncomputable section

namespace AutomaticContinuity.RadialPushIteration

open Set FlagTotalSpace PolynomialFamilyRegularity
open RadialSeparatorPropagation (nextPolynomial)

abbrev Pair := ℂ × ℂ
abbrev Poly := MvPolynomial (Fin 2) ℂ

def value {P : Type*} (q : P → Poly) (z : P × Pair) : ℂ :=
  MvPolynomial.eval ![z.2.1, z.2.2] (q z.1)

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- Exact data retained between two consecutive radial pushes. -/
structure State (L U : Set P) where
  radius : ℝ
  radius_pos : 0 < radius
  degree : ℕ
  obstacle : Set (P × Pair)
  compact_obstacle : IsCompact obstacle
  obstacle_base : obstacle ⊆ L ×ˢ univ
  polynomial : P → Poly
  holomorphic_coefficients : HolomorphicCoefficientsOn polynomial U
  degree_bound : ∀ p ∈ U, (polynomial p).totalDegree ≤ degree
  small_on_cylinder : ∀ z ∈ L ×ˢ closedEuclideanBall radius,
    ‖value polynomial z‖ ≤ 1 / 16
  near_one_on_obstacle : ∀ z ∈ obstacle, ‖value polynomial z - 1‖ ≤ 1 / 16

/-- One actual automorphism transition, including the precise new separator
and obstacle, not merely existence of some later compatible state. -/
structure Transition {L U : Set P} (S : State L U) (ε : ℝ) where
  next : State L U
  map : P → Pair ≃ₜ Pair
  fixes_zero : ∀ p, map p 0 = 0
  holomorphic : DifferentiableOn ℂ (fun z : P × Pair => map z.1 z.2) (U ×ˢ univ)
  inverse_holomorphic : DifferentiableOn ℂ (fun z : P × Pair => (map z.1).symm z.2) (U ×ˢ univ)
  next_radius : next.radius = 2 * S.radius
  next_degree : next.degree = 3 * S.degree
  next_polynomial : next.polynomial = fun p => nextPolynomial (S.polynomial p) 2
  next_obstacle : next.obstacle = (fun z : P × Pair => (z.1, map z.1 z.2)) '' S.obstacle
  protected_error : ∀ z ∈ L ×ˢ closedEuclideanBall S.radius,
    euclideanPairNorm (map z.1 z.2 - z.2) < ε ∧
    euclideanPairNorm ((map z.1).symm z.2 - z.2) < ε
  moving : ∀ z ∈ S.obstacle, euclideanPairNorm (map z.1 z.2 - (2 : ℝ) • z.2) < ε

/-- Every state admits the next actual push at every positive accuracy. The
separator perturbation tolerance is chosen before constructing the push. -/
theorem exists_transition [ProperSpace P] {L U : Set P}
    (hL : IsCompact L) (hU : IsOpen U) (hLU : L ⊆ U)
    (S : State L U) {ε : ℝ} (hε : 0 < ε) : Nonempty (Transition S ε) := by
  have hKU : S.obstacle ⊆ U ×ˢ univ := fun z hz =>
    ⟨hLU (S.obstacle_base hz).1, mem_univ _⟩
  obtain ⟨δ, hδ, hprop⟩ := RadialSeparatorPropagation.exists_polynomial_perturbation_radius
    S.degree S.polynomial S.compact_obstacle hU hKU (by norm_num : (0 : ℝ) < 2)
    S.degree_bound S.holomorphic_coefficients S.near_one_on_obstacle
  obtain ⟨Φ, hΦ0, hΦ, hΦinv, hprotected, hmoving⟩ :=
    RadialPolynomialPush.exists_compact_push S.polynomial S.degree
      hL S.compact_obstacle hU hLU S.obstacle_base (by norm_num : (0 : ℝ) ≤ 1)
      (lt_min hε hδ) S.holomorphic_coefficients S.degree_bound
      S.small_on_cylinder S.near_one_on_obstacle
  have hmove : ∀ z ∈ S.obstacle,
      euclideanPairNorm (Φ z.1 z.2 - (2 : ℝ) • z.2) < min ε δ := by
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using hmoving
  have hnear : ∀ z ∈ S.obstacle,
      ‖value (fun p => nextPolynomial (S.polynomial p) 2) (z.1, Φ z.1 z.2) - 1‖ < 1 / 16 :=
    hprop (fun z => Φ z.1 z.2) (fun z hz => (hmove z hz).trans_le (min_le_right _ _))
  let T : State L U := {
    radius := 2 * S.radius
    radius_pos := mul_pos (by norm_num) S.radius_pos
    degree := 3 * S.degree
    obstacle := (fun z : P × Pair => (z.1, Φ z.1 z.2)) '' S.obstacle
    compact_obstacle := RadialSeparatorPropagation.isCompact_image S.compact_obstacle
      (hΦ.continuousOn.mono hKU)
    obstacle_base := RadialSeparatorPropagation.image_subset_base S.obstacle_base _
    polynomial := fun p => nextPolynomial (S.polynomial p) 2
    holomorphic_coefficients :=
      RadialSeparatorPropagation.holomorphicCoefficientsOn_nextPolynomial 2 S.holomorphic_coefficients
    degree_bound := fun p hp =>
      (RadialSeparatorPropagation.nextPolynomial_degree (S.polynomial p) 2).trans
        (Nat.mul_le_mul_left 3 (S.degree_bound p hp))
    small_on_cylinder := fun z hz =>
      (RadialSeparatorPropagation.nextPolynomial_small (by norm_num : (0 : ℝ) < 2)
        S.small_on_cylinder z hz).trans (by norm_num)
    near_one_on_obstacle := by
      rintro _ ⟨z, hz, rfl⟩
      exact (hnear z hz).le }
  refine ⟨{
    next := T
    map := Φ
    fixes_zero := hΦ0
    holomorphic := hΦ
    inverse_holomorphic := hΦinv
    next_radius := rfl
    next_degree := rfl
    next_polynomial := rfl
    next_obstacle := rfl
    protected_error := ?_
    moving := ?_ }⟩
  · intro z hz
    exact ⟨((hprotected z hz).1).trans_le (min_le_left _ _),
      ((hprotected z hz).2).trans_le (min_le_left _ _)⟩
  · intro z hz
    exact (hmove z hz).trans_le (min_le_left _ _)

/-- The separator conditions imply that the actual obstacle is outside the
protected ball, even when some or all base fibres are empty. -/
theorem State.radius_lt_norm_of_mem {L U : Set P} (S : State L U)
    {z : P × Pair} (hz : z ∈ S.obstacle) : S.radius < euclideanPairNorm z.2 := by
  by_contra h
  have hnorm : euclideanPairNorm z.2 ≤ S.radius := le_of_not_gt h
  have hzero := S.small_on_cylinder z ⟨(S.obstacle_base hz).1, hnorm⟩
  have hone := S.near_one_on_obstacle z hz
  have ht := norm_sub_le (value S.polynomial z) (value S.polynomial z - 1)
  have heq : value S.polynomial z - (value S.polynomial z - 1) = 1 := by ring
  rw [heq, norm_one] at ht
  linarith

/-- One coherent infinite sequence; consecutive states are linked by the
same actual chosen transition. This is stronger than separate finite-history
existence assertions. -/
structure Iteration {L U : Set P} (S₀ : State L U) (ε : ℕ → ℝ) where
  state : ℕ → State L U
  step : ∀ n, Transition (state n) (ε n)
  initial : state 0 = S₀
  successor : ∀ n, state (n + 1) = (step n).next

theorem exists_iteration [ProperSpace P] {L U : Set P}
    (hL : IsCompact L) (hU : IsOpen U) (hLU : L ⊆ U)
    (S₀ : State L U) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    Nonempty (Iteration S₀ ε) := by
  let chooseStep (n : ℕ) (S : State L U) : Transition S (ε n) :=
    Classical.choice (exists_transition hL hU hLU S (hε n))
  let states : ℕ → State L U := Nat.rec S₀ (fun n S => (chooseStep n S).next)
  exact ⟨{
    state := states
    step := fun n => chooseStep n (states n)
    initial := rfl
    successor := fun _ => rfl }⟩

namespace Iteration

variable {L U : Set P} {S₀ : State L U} {ε : ℕ → ℝ} (I : Iteration S₀ ε)

def map (n : ℕ) : P → Pair ≃ₜ Pair := (I.step n).map

def cumulative (n : ℕ) (p : P) : Pair ≃ₜ Pair :=
  ParameterFibreComposition.product I.map n p

theorem radius (n : ℕ) : (I.state n).radius = (2 : ℝ) ^ n * S₀.radius := by
  induction n with
  | zero => simp only [I.initial, pow_zero, one_mul]
  | succ n ih =>
      rw [I.successor n, (I.step n).next_radius, ih, pow_succ]
      ring

theorem degree (n : ℕ) : (I.state n).degree = 3 ^ n * S₀.degree := by
  induction n with
  | zero => simp only [I.initial, pow_zero, one_mul]
  | succ n ih =>
      rw [I.successor n, (I.step n).next_degree, ih, pow_succ]
      ring

theorem polynomial_succ (n : ℕ) :
    (I.state (n + 1)).polynomial = fun p => nextPolynomial ((I.state n).polynomial p) 2 := by
  rw [I.successor n, (I.step n).next_polynomial]

theorem obstacle_eq_image_cumulative (n : ℕ) :
    (I.state n).obstacle =
      (fun z : P × Pair => (z.1, I.cumulative n z.1 z.2)) '' S₀.obstacle := by
  induction n with
  | zero =>
      rw [I.initial]
      change S₀.obstacle = (fun z => z) '' S₀.obstacle
      exact (Set.image_id _).symm
  | succ n ih =>
      rw [I.successor n, (I.step n).next_obstacle, ih, Set.image_image]
      rfl

theorem cumulative_fixes_zero (n : ℕ) (p : P) : I.cumulative n p 0 = 0 :=
  ParameterFibreComposition.product_origin I.map n p (fun i _ => (I.step i).fixes_zero p)

theorem cumulative_holomorphic (n : ℕ) :
    DifferentiableOn ℂ (fun z : P × Pair => I.cumulative n z.1 z.2) (U ×ˢ univ) :=
  ParameterFibreComposition.differentiableOn_product I.map n U
    (fun i _ => (I.step i).holomorphic)

theorem cumulative_inverse_holomorphic (n : ℕ) :
    DifferentiableOn ℂ (fun z : P × Pair => (I.cumulative n z.1).symm z.2) (U ×ˢ univ) :=
  ParameterFibreComposition.differentiableOn_product_symm I.map n U
    (fun i _ => (I.step i).inverse_holomorphic)

/-- Every original obstacle point is moved beyond the growing protected
radius by this single coherent sequence of cumulative automorphisms. -/
theorem cumulative_obstacle_escapes (n : ℕ) {z : P × Pair} (hz : z ∈ S₀.obstacle) :
    (2 : ℝ) ^ n * S₀.radius < euclideanPairNorm (I.cumulative n z.1 z.2) := by
  have hmem : (z.1, I.cumulative n z.1 z.2) ∈ (I.state n).obstacle := by
    rw [I.obstacle_eq_image_cumulative n]
    exact ⟨z, hz, rfl⟩
  have hh := (I.state n).radius_lt_norm_of_mem hmem
  rwa [I.radius n] at hh

end Iteration

/-- Data available when selecting an adaptive error budget. In particular,
the controller sees the actual cumulative inverse and its joint regularity. -/
structure Prefix (L U : Set P) where
  state : State L U
  cumulative : P → Pair ≃ₜ Pair
  fixes_zero : ∀ p, cumulative p 0 = 0
  holomorphic : DifferentiableOn ℂ
    (fun z : P × Pair => cumulative z.1 z.2) (U ×ˢ univ)
  inverse_holomorphic : DifferentiableOn ℂ
    (fun z : P × Pair => (cumulative z.1).symm z.2) (U ×ˢ univ)

namespace Prefix

variable {L U : Set P}

def initial (S₀ : State L U) : Prefix L U where
  state := S₀
  cumulative := fun _ => Homeomorph.refl Pair
  fixes_zero := fun _ => rfl
  holomorphic := differentiable_snd.differentiableOn
  inverse_holomorphic := differentiable_snd.differentiableOn

def extend (A : Prefix L U) {ε : ℝ} (T : Transition A.state ε) : Prefix L U where
  state := T.next
  cumulative := fun p => (A.cumulative p).trans (T.map p)
  fixes_zero := fun p => by
    change T.map p (A.cumulative p 0) = 0
    rw [A.fixes_zero p, T.fixes_zero p]
  holomorphic := T.holomorphic.comp
    (differentiable_fst.differentiableOn.prodMk A.holomorphic)
    (fun _ hz => ⟨hz.1, mem_univ _⟩)
  inverse_holomorphic := A.inverse_holomorphic.comp
    (differentiable_fst.differentiableOn.prodMk T.inverse_holomorphic)
    (fun _ hz => ⟨hz.1, mem_univ _⟩)

end Prefix

/-- One infinite sequence with genuinely history-dependent error choices.
The controller is evaluated before each next automorphism is selected. -/
structure ControlledIteration {L U : Set P} (S₀ : State L U)
    (budget : ℕ → Prefix L U → ℝ) where
  history : ℕ → Prefix L U
  step : ∀ n, Transition (history n).state (budget n (history n))
  initial : history 0 = Prefix.initial S₀
  successor : ∀ n, history (n + 1) = Prefix.extend (history n) (step n)

theorem exists_controlled_iteration [ProperSpace P] {L U : Set P}
    (hL : IsCompact L) (hU : IsOpen U) (hLU : L ⊆ U)
    (S₀ : State L U) (budget : ℕ → Prefix L U → ℝ)
    (hbudget : ∀ n A, 0 < budget n A) : Nonempty (ControlledIteration S₀ budget) := by
  let chooseStep (n : ℕ) (A : Prefix L U) : Transition A.state (budget n A) :=
    Classical.choice (exists_transition hL hU hLU A.state (hbudget n A))
  let prefixes : ℕ → Prefix L U :=
    Nat.rec (Prefix.initial S₀) (fun n A => Prefix.extend A (chooseStep n A))
  exact ⟨{
    history := prefixes
    step := fun n => chooseStep n (prefixes n)
    initial := rfl
    successor := fun _ => rfl }⟩

namespace ControlledIteration

variable {L U : Set P} {S₀ : State L U} {budget : ℕ → Prefix L U → ℝ}
  (I : ControlledIteration S₀ budget)

def toIteration : Iteration S₀ (fun n => budget n (I.history n)) where
  state := fun n => (I.history n).state
  step := I.step
  initial := congrArg Prefix.state I.initial
  successor := fun n => congrArg Prefix.state (I.successor n)

/-- The cumulative homeomorphism supplied to the budget controller equals
the actual finite product of all preceding chosen maps. -/
theorem cumulative_eq (n : ℕ) : I.toIteration.cumulative n = (I.history n).cumulative := by
  induction n with
  | zero =>
      rw [I.initial]
      rfl
  | succ n ih =>
      rw [I.successor n]
      change (fun p => (I.toIteration.cumulative n p).trans ((I.step n).map p)) =
        (fun p => ((I.history n).cumulative p).trans ((I.step n).map p))
      rw [ih]

theorem obstacle_eq_image_cumulative (n : ℕ) :
    (I.history n).state.obstacle =
      (fun z : P × Pair => (z.1, (I.history n).cumulative z.1 z.2)) '' S₀.obstacle := by
  have hh := I.toIteration.obstacle_eq_image_cumulative n
  rw [I.cumulative_eq n] at hh
  exact hh

theorem cumulative_obstacle_escapes (n : ℕ) {z : P × Pair} (hz : z ∈ S₀.obstacle) :
    (2 : ℝ) ^ n * S₀.radius < euclideanPairNorm ((I.history n).cumulative z.1 z.2) := by
  have hh := I.toIteration.cumulative_obstacle_escapes n hz
  rwa [I.cumulative_eq n] at hh

end ControlledIteration

end AutomaticContinuity.RadialPushIteration
