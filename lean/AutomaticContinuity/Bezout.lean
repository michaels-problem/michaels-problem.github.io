import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Finite Bézout solution spaces

The correction retraction below is the elementary algebraic ingredient in the
inverse-limit approach to Arens interpolation. A continuous dense ring map has
dense range on these solution spaces whenever a source solution exists.
This does not supply Banach-stage solutions or prove the Arens theorem.
-/

namespace AutomaticContinuity.Bezout

open scoped BigOperators

universe u v w

variable {ι : Type u} [Fintype ι]
variable {A : Type v} [CommRing A]
variable {B : Type w} [CommRing B]

def pairing (u v : ι → A) : A := ∑ i, u i * v i

/-- The affine set of solutions of one finite Bézout equation. -/
abbrev Solution (u : ι → A) := {v : ι → A // pairing u v = 1}

/-- Correction into the affine solution set using one fixed solution. -/
def correction (u : ι → A) (y : Solution u) (v : ι → A) : ι → A :=
  fun i => v i + y.val i - y.val i * pairing u v

theorem pairing_correction (u : ι → A) (y : Solution u) (v : ι → A) :
    pairing u (correction u y v) = 1 := by
  classical
  unfold pairing correction
  simp_rw [mul_sub, mul_add, ← mul_assoc]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
  change pairing u v + pairing u y.val - pairing u y.val * pairing u v = 1
  rw [y.property]
  ring

def retract (u : ι → A) (y : Solution u) (v : ι → A) : Solution u :=
  ⟨correction u y v, pairing_correction u y v⟩

@[simp] theorem retract_solution (u : ι → A) (y v : Solution u) :
    retract u y v.val = v := by
  apply Subtype.ext
  funext i
  simp [retract, correction, v.property]

theorem retract_surjective (u : ι → A) (y : Solution u) :
    Function.Surjective (retract u y) := fun v => ⟨v.val, retract_solution u y v⟩

theorem map_pairing (T : A →+* B) (u v : ι → A) :
    pairing (fun i => T (u i)) (fun i => T (v i)) = T (pairing u v) := by
  simp [pairing]

def mapSolution (T : A →+* B) (u : ι → A) (v : Solution u) :
    Solution (fun i => T (u i)) :=
  ⟨fun i => T (v.val i), by rw [map_pairing, v.property, map_one]⟩

theorem map_retract (T : A →+* B) (u : ι → A) (y : Solution u) (v : ι → A) :
    mapSolution T u (retract u y v) =
      retract (fun i => T (u i)) (mapSolution T u y) (fun i => T (v i)) := by
  apply Subtype.ext
  funext i
  simp [mapSolution, retract, correction, map_pairing]

section Topology

variable [TopologicalSpace A] [IsTopologicalRing A]
variable [TopologicalSpace B] [IsTopologicalRing B]

theorem continuous_pairing (u : ι → A) : Continuous (pairing u) := by
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)

theorem isClosed_solutions [T2Space A] (u : ι → A) :
    IsClosed {v : ι → A | pairing u v = 1} :=
  isClosed_eq (continuous_pairing u) continuous_const

theorem continuous_retract (u : ι → A) (y : Solution u) : Continuous (retract u y) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact ((continuous_apply i).add continuous_const).sub
    (continuous_const.mul (continuous_pairing u))

omit [IsTopologicalRing A] [IsTopologicalRing B] in
theorem continuous_mapSolution (T : A →+* B) (hT : Continuous T) (u : ι → A) :
    Continuous (mapSolution T u) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact hT.comp ((continuous_apply i).comp continuous_subtype_val)

omit [TopologicalSpace A] [IsTopologicalRing A] in
/-- Density on affine Bézout solution spaces follows from density on the rings
and a single source solution. No continuity of an algebraic character is used. -/
theorem denseRange_mapSolution (T : A →+* B) (hT : DenseRange T)
    (u : ι → A) (y : Solution u) : DenseRange (mapSolution T u) := by
  have hd : DenseRange (fun v : ι → A => fun i => T (v i)) :=
    DenseRange.piMap (fun _ : ι => hT)
  have hr := (retract_surjective (fun i => T (u i)) (mapSolution T u y)).denseRange
  have hc := hr.comp hd (continuous_retract (fun i => T (u i)) (mapSolution T u y))
  have heq : (fun v : ι → A =>
      retract (fun i => T (u i)) (mapSolution T u y) (fun i => T (v i))) =
      mapSolution T u ∘ retract u y := by
    funext v
    exact (map_retract T u y v).symm
  change DenseRange (fun v : ι → A =>
    retract (fun i => T (u i)) (mapSolution T u y) (fun i => T (v i))) at hc
  rw [heq] at hc
  exact hc.of_comp

end Topology

/-- Closedness makes the solution space complete for the inherited product
uniformity whenever the ambient ring is complete and Hausdorff. -/
instance solutionCompleteSpace [UniformSpace A] [IsTopologicalRing A]
    [T2Space A] [CompleteSpace A] (u : ι → A) : CompleteSpace (Solution u) :=
  (isClosed_solutions u).isComplete.completeSpace_coe

/-- Contracting ring maps remain contracting on finite solution vectors with
the inherited finite-product metric, as needed for the inverse-limit argument. -/
theorem lipschitzWith_mapSolution [PseudoMetricSpace A] [PseudoMetricSpace B]
    (T : A →+* B) (hT : LipschitzWith 1 T) (u : ι → A) :
    LipschitzWith 1 (mapSolution T u) := by
  apply LipschitzWith.of_edist_le
  intro x y
  change edist (fun i => T (x.val i)) (fun i => T (y.val i)) ≤ edist x.val y.val
  rw [edist_pi_def]
  apply Finset.sup_le
  intro i _hi
  have hi : edist (T (x.val i)) (T (y.val i)) ≤ edist (x.val i) (y.val i) := by
    simpa only [ENNReal.coe_one, one_mul] using hT (x.val i) (y.val i)
  exact hi.trans (edist_le_pi_edist x.val y.val i)

end AutomaticContinuity.Bezout
