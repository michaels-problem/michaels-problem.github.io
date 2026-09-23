import AutomaticContinuity.FlagTotalSpace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Data.Nat.Find

set_option autoImplicit false

/-!
# Affine contraction preserving the actual finite flags

A nonempty convex compact is not assumed to meet the deepest flag. We choose
a point in the deepest flag that it actually meets. Contraction toward this
point preserves every constraint occurring on the set. This is a geometric
ingredient for a future approximation argument, not a flag-extension theorem.
-/

noncomputable section

namespace AutomaticContinuity.FlagAffineContraction

open Set FlagTotalSpace

def contraction {n : ℕ} (c : FinitePoint n) (t : ℝ) (z : FinitePoint n) :
    FinitePoint n := (1 - t) • c + t • z

@[simp] theorem contraction_zero {n : ℕ} (c z : FinitePoint n) :
    contraction c 0 z = c := by simp [contraction]

@[simp] theorem contraction_one {n : ℕ} (c z : FinitePoint n) :
    contraction c 1 z = z := by simp [contraction]

theorem continuous_contraction {n : ℕ} (c : FinitePoint n) :
    Continuous (fun p : ℝ × FinitePoint n => contraction c p.1 p.2) := by
  unfold contraction
  fun_prop

theorem differentiable_contraction {n : ℕ} (c : FinitePoint n) (t : ℝ) :
    Differentiable ℂ (contraction c t) := by
  unfold contraction
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  fun_prop

theorem contraction_mem {n : ℕ} {K : Set (FinitePoint n)} (hK : Convex ℝ K)
    {c z : FinitePoint n} (hc : c ∈ K) (hz : z ∈ K)
    {t : ℝ} (ht : t ∈ Icc 0 1) : contraction c t z ∈ K := by
  exact hK hc hz (sub_nonneg.mpr ht.2) ht.1 (by ring)

theorem contraction_mem_flag {n k : ℕ} {c z : FinitePoint n}
    (hc : c ∈ finiteFlag n k) (hz : z ∈ finiteFlag n k) (t : ℝ) :
    contraction c t z ∈ finiteFlag n k := by
  intro j hj
  change (1 - t) • c j + t • z j = _
  rw [hc j hj, hz j hj, ← add_smul]
  simp

/-- The choice of the centre depends only on the set, not on the section. -/
theorem exists_deepest_center {n : ℕ} {K : Set (FinitePoint n)} (hK : K.Nonempty) :
    ∃ j : ℕ, j ≤ n ∧ ∃ c ∈ K, c ∈ finiteFlag n j ∧
      ∀ k : ℕ, k ≤ n → (K ∩ finiteFlag n k).Nonempty → k ≤ j := by
  classical
  let P : ℕ → Prop := fun k => (K ∩ finiteFlag n k).Nonempty
  have hP0 : P 0 := by simpa [P] using hK
  let j := Nat.findGreatest P n
  obtain ⟨c, hcK, hcj⟩ := Nat.findGreatest_spec (Nat.zero_le n) hP0
  exact ⟨j, Nat.findGreatest_le n, c, hcK, hcj,
    fun k hkn hk => Nat.le_findGreatest hkn hk⟩

theorem contraction_admissible {n j : ℕ} {K : Set (FinitePoint n)}
    (hK : Convex ℝ K) {c : FinitePoint n} (hcK : c ∈ K)
    (hcj : c ∈ finiteFlag n j)
    (hmax : ∀ k : ℕ, k ≤ n → (K ∩ finiteFlag n k).Nonempty → k ≤ j)
    {h : FinitePoint n → ℂ × ℂ}
    (hh : ∀ z ∈ K, (z, h z) ∈ totalSet n)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    ∀ z ∈ K, (z, h (contraction c t z)) ∈ totalSet n := by
  intro z hz
  apply mem_totalSet_iff.mpr
  intro k hk hkn hzk
  have hkj : k ≤ j := hmax k hkn ⟨z, hz, hzk⟩
  have hck := finiteFlag_antitone n hkj hcj
  have hctK := contraction_mem hK hcK hz ht
  have hctflag := contraction_mem_flag hck hzk t
  exact mem_totalSet_iff.mp (hh _ hctK) k hk hkn hctflag

theorem continuousOn_section_contraction {n : ℕ} {K : Set (FinitePoint n)}
    (hK : Convex ℝ K) {c : FinitePoint n} (hcK : c ∈ K)
    {h : FinitePoint n → ℂ × ℂ} (hh : ContinuousOn h K) :
    ContinuousOn (fun p : ℝ × FinitePoint n => h (contraction c p.1 p.2))
      (Icc 0 1 ×ˢ K) :=
  hh.comp (continuous_contraction c).continuousOn
    (fun _ hp => contraction_mem hK hcK hp.2 hp.1)

/-- Each time slice remains holomorphic on an actual open neighbourhood of K;
the neighbourhood is allowed to depend on the time slice. -/
theorem holomorphic_section_contraction {n : ℕ} {K U : Set (FinitePoint n)}
    (hK : Convex ℝ K) {c : FinitePoint n} (hcK : c ∈ K)
    (hU : IsOpen U) (hKU : K ⊆ U)
    {h : FinitePoint n → ℂ × ℂ} (hh : DifferentiableOn ℂ h U)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    ∃ V : Set (FinitePoint n), IsOpen V ∧ K ⊆ V ∧
      DifferentiableOn ℂ (fun z => h (contraction c t z)) V := by
  refine ⟨contraction c t ⁻¹' U,
    hU.preimage (differentiable_contraction c t).continuous, ?_, ?_⟩
  · intro z hz
    exact hKU (contraction_mem hK hcK hz ht)
  · exact hh.comp (differentiable_contraction c t).differentiableOn (fun _ hz => hz)

end AutomaticContinuity.FlagAffineContraction
