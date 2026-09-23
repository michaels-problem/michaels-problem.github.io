import AutomaticContinuity.Statement
import Mathlib.Tactic.Ring

/-! # Multiplication in a locally multiplicatively convex algebra

The defining seminorm inequalities force joint continuity of multiplication.
This verifies a topological-algebra property implicit in the reviewed definition.
-/

namespace AutomaticContinuity

open Filter
open scoped Topology

universe u

variable {A : Type u} [NonUnitalCommRing A] [Module ℂ A] [TopologicalSpace A]

omit [TopologicalSpace A] in
theorem IsSubmultiplicative.mul_sub_mul_le {p : Seminorm ℂ A}
    (hp : IsSubmultiplicative A p) (x y a b : A) :
    p (x * y - a * b) ≤ p (x - a) * p y + p a * p (y - b) := by
  have h : x * y - a * b = (x - a) * y + a * (y - b) := by
    rw [sub_mul, mul_sub, sub_add_sub_cancel]
  rw [h]
  exact (map_add_le_add p _ _).trans (add_le_add (hp _ _) (hp _ _))

/-- Every locally multiplicatively convex algebra has jointly continuous product. -/
theorem IsLocallyMultiplicativelyConvex.continuousMul
    (hA : IsLocallyMultiplicativelyConvex A) : ContinuousMul A := by
  obtain ⟨P, hmul, hP⟩ := hA
  let : IsTopologicalAddGroup A := hP.isTopologicalAddGroup
  constructor
  apply continuous_iff_continuousAt.mpr
  rintro ⟨a, b⟩
  apply (hP.tendsto_nhds (fun z : A × A => z.1 * z.2) (a * b)).mpr
  intro p ε hε
  have hc : Continuous (fun z : A × A =>
      p.val (z.1 - a) * p.val z.2 + p.val a * p.val (z.2 - b)) :=
    (((hP.continuous_seminorm p).comp (continuous_fst.sub continuous_const)).mul
      ((hP.continuous_seminorm p).comp continuous_snd)).add
        (continuous_const.mul
          ((hP.continuous_seminorm p).comp (continuous_snd.sub continuous_const)))
  have ht : Tendsto (fun z : A × A =>
      p.val (z.1 - a) * p.val z.2 + p.val a * p.val (z.2 - b))
      (𝓝 (a, b)) (𝓝 0) := by
    simpa using hc.continuousAt.tendsto (x := (a, b))
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with z hz
  exact ((hmul p.val p.property).mul_sub_mul_le z.1 z.2 a b).trans_lt hz

end AutomaticContinuity
