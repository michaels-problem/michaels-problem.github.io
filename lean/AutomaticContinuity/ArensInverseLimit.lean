import AutomaticContinuity.Bezout
import AutomaticContinuity.DenseInverseLimit
import Mathlib.Analysis.Normed.Ring.Lemmas

set_option autoImplicit false

/-!
# The Banach-stage and inverse-limit steps in finite interpolation

Compatible finite Bézout equations over a countable system of Banach algebras
have compatible solutions if each stage has a solution. The source of those
solutions is supplied by `ArensBanach.lean`; their reconstruction in the
coefficient algebra is supplied by `BanachReconstruction.lean`.
-/

noncomputable section

namespace AutomaticContinuity.Arens

open scoped BigOperators

universe u v w

variable {ι : Type u} [Fintype ι]

section Transport

variable {A : Type v} [CommRing A] {B : Type w} [CommRing B]

/-- The coordinate map with the target row written explicitly. -/
def solutionMap (T : A →+* B) (a : ι → A) (b : ι → B)
    (h : (fun i => T (a i)) = b) (x : Bezout.Solution a) : Bezout.Solution b :=
  ⟨fun i => T (x.val i), by
    rw [← h, Bezout.map_pairing, x.property, map_one]⟩

theorem denseRange_solutionMap [TopologicalSpace B] [IsTopologicalRing B]
    (T : A →+* B) (hT : DenseRange T) (a : ι → A) (b : ι → B)
    (h : (fun i => T (a i)) = b) (y : Bezout.Solution a) :
    DenseRange (solutionMap T a b h) := by
  subst b
  exact Bezout.denseRange_mapSolution T hT a y

theorem lipschitzWith_solutionMap [PseudoMetricSpace A] [PseudoMetricSpace B]
    (T : A →+* B) (hT : LipschitzWith 1 T) (a : ι → A) (b : ι → B)
    (h : (fun i => T (a i)) = b) : LipschitzWith 1 (solutionMap T a b h) := by
  subst b
  exact Bezout.lipschitzWith_mapSolution T hT a

end Transport

section InverseLimit

variable {B : ℕ → Type v} [∀ n, NormedCommRing (B n)] [∀ n, CompleteSpace (B n)]

/-- Compatible finite equations have compatible solutions whenever each Banach
stage has one and the bonding maps are dense contractions. -/
theorem exists_compatible_solutions (T : (n : ℕ) → B (n + 1) →+* B n)
    (hLip : ∀ n, LipschitzWith 1 (T n)) (hDense : ∀ n, DenseRange (T n))
    (a : (n : ℕ) → ι → B n)
    (ha : ∀ n i, T n (a (n + 1) i) = a n i)
    (hSol : ∀ n, Nonempty (Bezout.Solution (a n))) :
    ∃ x : (n : ℕ) → Bezout.Solution (a n),
      ∀ n i, T n ((x (n + 1)).val i) = (x n).val i := by
  classical
  let S (n : ℕ) := Bezout.Solution (a n)
  let f (n : ℕ) : S (n + 1) → S n :=
    solutionMap (T n) (a (n + 1)) (a n) (funext (ha n))
  let (n : ℕ) : Nonempty (S n) := hSol n
  have hLf (n : ℕ) : LipschitzWith 1 (f n) :=
    lipschitzWith_solutionMap (T n) (hLip n) _ _ _
  have hDf (n : ℕ) : DenseRange (f n) :=
    denseRange_solutionMap (T n) (hDense n) _ _ _ (Classical.choice (hSol (n + 1)))
  obtain ⟨x, hx⟩ := DenseInverseLimit.exists_compatible f hLf hDf
  refine ⟨x, ?_⟩
  intro n i
  exact congrArg (fun y : S n => y.val i) (hx n)

end InverseLimit

end AutomaticContinuity.Arens
