import AutomaticContinuity.FiniteHalfspaceExhaustion

set_option autoImplicit false

/-!
# Concrete polygon products around polydiscs

The outer set is a product of closed planar squares. Finitely many closed
coordinate halfspaces give a smaller product of convex planar polygons,
strictly surrounding the original polydisc and contained in any prescribed
open neighbourhood. Removing those cuts gives a finite compact convex chain.
This file proves source geometry only, not complex approximation on it.
-/

noncomputable section

namespace AutomaticContinuity.FiniteHalfspaceExhaustion

open Set

def closedBox (n : ℕ) (S : ℝ) : Set (FinitePoint n) :=
  {z | ∀ j : Fin n, |(z j).re| ≤ S ∧ |(z j).im| ≤ S}

theorem isClosed_closedBox (n : ℕ) (S : ℝ) : IsClosed (closedBox n S) := by
  have heq : closedBox n S = ⋂ j : Fin n,
      {z : FinitePoint n | |(z j).re| ≤ S} ∩ {z | |(z j).im| ≤ S} := by
    ext z
    simp [closedBox]
  rw [heq]
  exact isClosed_iInter fun j =>
    (isClosed_le ((Complex.continuous_re.comp (continuous_apply j)).abs) continuous_const).inter
      (isClosed_le ((Complex.continuous_im.comp (continuous_apply j)).abs) continuous_const)

theorem closedBox_subset_polydisc (n : ℕ) (S : ℝ) :
    closedBox n S ⊆ polydisc n (2 * S) := by
  intro z hz j
  exact (Complex.norm_le_abs_re_add_abs_im (z j)).trans (by linarith [(hz j).1, (hz j).2])

theorem isCompact_closedBox (n : ℕ) {S : ℝ} (hS : 0 ≤ S) :
    IsCompact (closedBox n S) :=
  (isCompact_polydisc n (mul_nonneg (by norm_num) hS)).of_isClosed_subset
    (isClosed_closedBox n S) (closedBox_subset_polydisc n S)

private theorem abs_convexCombination_le {a b x y S : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : |x| ≤ S) (hy : |y| ≤ S) : |a*x+b*y| ≤ S := by
  calc
    |a*x+b*y| ≤ |a*x|+|b*y| := abs_add_le _ _
    _ = a*|x|+b*|y| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a*S+b*S := add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb)
    _ = S := by rw [← add_mul, hab, one_mul]

theorem convex_closedBox (n : ℕ) (S : ℝ) : Convex ℝ (closedBox n S) := by
  intro x hx y hy a b ha hb hab j
  change |(a • x j + b • y j).re| ≤ S ∧ |(a • x j + b • y j).im| ≤ S
  simpa [Complex.real_smul] using
    And.intro (abs_convexCombination_le ha hb hab (hx j).1 (hy j).1)
      (abs_convexCombination_le ha hb hab (hx j).2 (hy j).2)

theorem polydisc_subset_closedBox (n : ℕ) (S : ℝ) :
    polydisc n S ⊆ closedBox n S := by
  intro z hz j
  exact ⟨(Complex.abs_re_le_norm _).trans (hz j),
    (Complex.abs_im_le_norm _).trans (hz j)⟩

theorem polydisc_subset_interior_closedBox (n : ℕ) {R S : ℝ} (hRS : R < S) :
    polydisc n R ⊆ interior (closedBox n S) := by
  let V : Set (FinitePoint n) :=
    ⋂ j : Fin n, {z | |(z j).re| < S} ∩ {z | |(z j).im| < S}
  have hV : IsOpen V := isOpen_iInter_of_finite fun j =>
    (isOpen_lt ((Complex.continuous_re.comp (continuous_apply j)).abs) continuous_const).inter
      (isOpen_lt ((Complex.continuous_im.comp (continuous_apply j)).abs) continuous_const)
  have hVK : V ⊆ closedBox n S := by
    intro z hz j
    exact ⟨(mem_iInter.mp hz j).1.le, (mem_iInter.mp hz j).2.le⟩
  intro z hz
  apply interior_maximal hVK hV
  apply mem_iInter.mpr
  intro j
  exact ⟨((Complex.abs_re_le_norm _).trans (hz j)).trans_lt hRS,
    ((Complex.abs_im_le_norm _).trans (hz j)).trans_lt hRS⟩

theorem exists_finite_cutChain {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    {L U : Set (FinitePoint n)} (hL : IsCompact L) (hLc : Convex ℝ L)
    (hU : IsOpen U) (hKU : polydisc n R ⊆ U)
    (hKL : polydisc n R ⊆ interior L) :
    ∃ (N : ℕ) (q : Fin N → CoordinateCut n),
      polydisc n R ⊆ interior (cutChain L q 0) ∧
      cutChain L q 0 ⊆ U ∧
      cutChain L q N = L ∧
      Monotone (cutChain L q) ∧
      (∀ j, IsCompact (cutChain L q j) ∧ Convex ℝ (cutChain L q j)) ∧
      ∀ j : Fin N, cutChain L q j.val =
        cutChain L q (j.val + 1) ∩ (q j).halfspace := by
  classical
  obtain ⟨s, hsK, hsU⟩ := exists_finite_coordinate_cuts hR hL hU hKU
  let q : Fin s.card → CoordinateCut n := fun i => (s.equivFin.symm i).val
  have hqmem (i : Fin s.card) : q i ∈ s := (s.equivFin.symm i).property
  have hsurj : ∀ r ∈ s, ∃ i : Fin s.card, q i = r := by
    intro r hr
    exact ⟨s.equivFin ⟨r, hr⟩, congrArg Subtype.val (s.equivFin.symm_apply_apply ⟨r, hr⟩)⟩
  have hinitU : cutChain L q 0 ⊆ U := by
    intro z hz
    apply hsU
    refine ⟨hz.1, mem_iInter₂.mpr ?_⟩
    intro r hr
    obtain ⟨i, rfl⟩ := hsurj r hr
    exact mem_iInter₂.mp hz.2 i (Nat.zero_le _)
  have hinitK : polydisc n R ⊆ interior (cutChain L q 0) := by
    let V := interior L ∩ ⋂ i : Fin s.card, (q i).strictHalfspace
    have hV : IsOpen V := isOpen_interior.inter
      (isOpen_iInter_of_finite fun i => (q i).isOpen_strictHalfspace)
    have hVinit : V ⊆ cutChain L q 0 := by
      intro z hz
      refine ⟨interior_subset hz.1, mem_iInter₂.mpr ?_⟩
      intro i _
      exact (show (q i).value z < (q i).bound from mem_iInter.mp hz.2 i).le
    intro z hz
    apply interior_maximal hVinit hV
    exact ⟨hKL hz, mem_iInter.mpr (fun i => hsK (q i) (hqmem i) hz)⟩
  exact ⟨s.card, q, hinitK, hinitU, cutChain_final L q, cutChain_mono L q,
    fun j => ⟨isCompact_cutChain hL q j, convex_cutChain hLc q j⟩,
    cutChain_step L q⟩

/-- Concrete finite source geometry for a radius enlargement. The outer box
contains the entire requested larger polydisc. -/
theorem exists_polydisc_enlargement_chain {n : ℕ} {R S : ℝ}
    (hR : 0 ≤ R) (hRS : R < S) {U : Set (FinitePoint n)}
    (hU : IsOpen U) (hKU : polydisc n R ⊆ U) :
    ∃ (N : ℕ) (q : Fin N → CoordinateCut n),
      polydisc n R ⊆ interior (cutChain (closedBox n S) q 0) ∧
      cutChain (closedBox n S) q 0 ⊆ U ∧
      polydisc n S ⊆ cutChain (closedBox n S) q N ∧
      Monotone (cutChain (closedBox n S) q) ∧
      (∀ j, IsCompact (cutChain (closedBox n S) q j) ∧
        Convex ℝ (cutChain (closedBox n S) q j)) ∧
      ∀ j : Fin N, cutChain (closedBox n S) q j.val =
        cutChain (closedBox n S) q (j.val + 1) ∩ (q j).halfspace := by
  obtain ⟨N, q, hK, hU', hfinal, hmono, hgeom, hstep⟩ :=
    exists_finite_cutChain hR (isCompact_closedBox n (hR.trans hRS.le))
      (convex_closedBox n S) hU hKU (polydisc_subset_interior_closedBox n hRS)
  refine ⟨N, q, hK, hU', ?_, hmono, hgeom, hstep⟩
  rw [hfinal]
  exact polydisc_subset_closedBox n S

end AutomaticContinuity.FiniteHalfspaceExhaustion
