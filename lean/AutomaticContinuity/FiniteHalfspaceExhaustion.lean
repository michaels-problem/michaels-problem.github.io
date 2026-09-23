import AutomaticContinuity.FlagAffineContraction

set_option autoImplicit false

/-!
# A finite coordinate-halfspace enlargement

The cuts are genuine real affine halfspaces in individual complex source
coordinates. Compactness gives finitely many cuts surrounding a polydisc
inside any prescribed open neighbourhood, relative to a compact outer set.
Removing those cuts is a predetermined finite sequence; no adaptive bump
size or analytic approximation theorem is assumed in this geometry.
-/

noncomputable section

namespace AutomaticContinuity.FiniteHalfspaceExhaustion

open Set

structure CoordinateCut (n : ℕ) where
  coordinate : Fin n
  coefficient : ℂ
  bound : ℝ

namespace CoordinateCut

def value {n : ℕ} (q : CoordinateCut n) (z : FinitePoint n) : ℝ :=
  (q.coefficient * z q.coordinate).re

def halfspace {n : ℕ} (q : CoordinateCut n) : Set (FinitePoint n) :=
  {z | q.value z ≤ q.bound}

def strictHalfspace {n : ℕ} (q : CoordinateCut n) : Set (FinitePoint n) :=
  {z | q.value z < q.bound}

theorem continuous_value {n : ℕ} (q : CoordinateCut n) : Continuous q.value := by
  unfold value
  fun_prop

theorem isClosed_halfspace {n : ℕ} (q : CoordinateCut n) : IsClosed q.halfspace :=
  isClosed_le q.continuous_value continuous_const

theorem isOpen_strictHalfspace {n : ℕ} (q : CoordinateCut n) :
    IsOpen q.strictHalfspace := isOpen_lt q.continuous_value continuous_const

theorem convex_halfspace {n : ℕ} (q : CoordinateCut n) : Convex ℝ q.halfspace := by
  intro x hx y hy a b ha hb hab
  change (q.coefficient * (a • x q.coordinate + b • y q.coordinate)).re ≤ q.bound
  have heq : (q.coefficient * (a • x q.coordinate + b • y q.coordinate)).re =
      a * q.value x + b * q.value y := by
    simp [value, Complex.real_smul, mul_add, Complex.mul_re]
    ring
  rw [heq]
  have h := add_le_add (mul_le_mul_of_nonneg_left hx ha)
    (mul_le_mul_of_nonneg_left hy hb)
  calc
    a * q.value x + b * q.value y ≤ a * q.bound + b * q.bound := h
    _ = q.bound := by rw [← add_mul, hab, one_mul]

end CoordinateCut

theorem exists_strict_coordinate_separator {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    {z : FinitePoint n} (hz : z ∉ polydisc n R) :
    ∃ q : CoordinateCut n, polydisc n R ⊆ q.strictHalfspace ∧ z ∉ q.halfspace := by
  classical
  obtain ⟨j, hj⟩ := not_forall.mp hz
  have hjR : R < ‖z j‖ := lt_of_not_ge hj
  have hjpos : 0 < ‖z j‖ := hR.trans_lt hjR
  let q : CoordinateCut n :=
    ⟨j, star (z j), (‖z j‖ * R + ‖z j‖ ^ 2) / 2⟩
  have hself : q.value z = ‖z j‖ ^ 2 := by
    simp only [q, CoordinateCut.value, Complex.mul_re, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply]
  have hgap : ‖z j‖ * R < ‖z j‖ ^ 2 := by
    nlinarith [mul_lt_mul_of_pos_left hjR hjpos]
  refine ⟨q, ?_, ?_⟩
  · intro w hw
    have hv : q.value w ≤ ‖z j‖ * R := by
      calc
        q.value w ≤ ‖star (z j) * w j‖ := Complex.re_le_norm _
        _ = ‖z j‖ * ‖w j‖ := by simp
        _ ≤ ‖z j‖ * R := mul_le_mul_of_nonneg_left (hw j) (norm_nonneg _)
    change q.value w < (‖z j‖ * R + ‖z j‖ ^ 2) / 2
    linarith
  · change ¬ q.value z ≤ (‖z j‖ * R + ‖z j‖ ^ 2) / 2
    rw [hself]
    linarith

/-- Relative to any compact outer set, finitely many actual coordinate cuts
surround the old polydisc and lie inside its prescribed neighbourhood. -/
theorem exists_finite_coordinate_cuts {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    {L U : Set (FinitePoint n)} (hL : IsCompact L) (hU : IsOpen U)
    (hKU : polydisc n R ⊆ U) :
    ∃ s : Finset (CoordinateCut n),
      (∀ q ∈ s, polydisc n R ⊆ q.strictHalfspace) ∧
      L ∩ (⋂ q ∈ s, q.halfspace) ⊆ U := by
  classical
  let Q := {q : CoordinateCut n // polydisc n R ⊆ q.strictHalfspace}
  have hcover : L \ U ⊆ ⋃ q : Q, q.val.halfspaceᶜ := by
    intro z hz
    have hzK : z ∉ polydisc n R := fun h => hz.2 (hKU h)
    obtain ⟨q, hqK, hqz⟩ := exists_strict_coordinate_separator hR hzK
    exact mem_iUnion.mpr ⟨⟨q, hqK⟩, hqz⟩
  obtain ⟨s, hs⟩ := (hL.diff hU).elim_finite_subcover
    (fun q : Q => q.val.halfspaceᶜ)
    (fun q => q.val.isClosed_halfspace.isOpen_compl) hcover
  refine ⟨s.image Subtype.val, ?_, ?_⟩
  · intro q hq
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hq
    exact r.property
  · intro z hz
    by_contra hzU
    obtain ⟨q, hqs, hqz⟩ := mem_iUnion₂.mp (hs ⟨hz.1, hzU⟩)
    exact hqz (mem_iInter₂.mp hz.2 q.val (Finset.mem_image.mpr ⟨q, hqs, rfl⟩))

def cutChain {n N : ℕ} (L : Set (FinitePoint n))
    (q : Fin N → CoordinateCut n) (j : ℕ) : Set (FinitePoint n) :=
  L ∩ ⋂ i : Fin N, ⋂ (_ : j ≤ i.val), (q i).halfspace

theorem cutChain_mono {n N : ℕ} (L : Set (FinitePoint n))
    (q : Fin N → CoordinateCut n) : Monotone (cutChain L q) := by
  intro j k hjk z hz
  refine ⟨hz.1, mem_iInter₂.mpr ?_⟩
  intro i hki
  exact mem_iInter₂.mp hz.2 i (hjk.trans hki)

@[simp] theorem cutChain_final {n N : ℕ} (L : Set (FinitePoint n))
    (q : Fin N → CoordinateCut n) : cutChain L q N = L := by
  ext z
  constructor
  · exact fun hz => hz.1
  · intro hz
    refine ⟨hz, mem_iInter₂.mpr ?_⟩
    intro i hi
    exact (Nat.not_le.mpr i.isLt hi).elim

theorem cutChain_step {n N : ℕ} (L : Set (FinitePoint n))
    (q : Fin N → CoordinateCut n) (j : Fin N) :
    cutChain L q j.val = cutChain L q (j.val + 1) ∩ (q j).halfspace := by
  ext z
  constructor
  · intro hz
    exact ⟨cutChain_mono L q (Nat.le_succ _) hz, mem_iInter₂.mp hz.2 j le_rfl⟩
  · rintro ⟨hz, hj⟩
    refine ⟨hz.1, mem_iInter₂.mpr ?_⟩
    intro i hji
    by_cases heq : i = j
    · simpa [heq] using hj
    · exact mem_iInter₂.mp hz.2 i (by
        have hne : i.val ≠ j.val := fun h => heq (Fin.ext h)
        omega)

theorem isCompact_cutChain {n N : ℕ} {L : Set (FinitePoint n)}
    (hL : IsCompact L) (q : Fin N → CoordinateCut n) (j : ℕ) :
    IsCompact (cutChain L q j) :=
  hL.inter_right (isClosed_iInter fun i => isClosed_iInter fun _ =>
    (q i).isClosed_halfspace)

theorem convex_cutChain {n N : ℕ} {L : Set (FinitePoint n)}
    (hL : Convex ℝ L) (q : Fin N → CoordinateCut n) (j : ℕ) :
    Convex ℝ (cutChain L q j) :=
  hL.inter (convex_iInter fun i => convex_iInter fun _ => (q i).convex_halfspace)

end AutomaticContinuity.FiniteHalfspaceExhaustion
