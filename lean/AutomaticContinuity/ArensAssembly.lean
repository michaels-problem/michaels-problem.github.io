import AutomaticContinuity.ArensInverseLimit
import AutomaticContinuity.BanachReconstruction

set_option autoImplicit false

/-!
# Recovering finite Bézout solutions in the coefficient algebra

This assembles the complete Banach-stage solution spaces, dense contractions,
and reconstruction in the original coefficient topology.
-/

noncomputable section

namespace AutomaticContinuity.Arens

open CoefficientSeries BanachStages

universe u

variable {ι : Type u} [Fintype ι]

/-- Solvability in every single-norm completion implies solvability in the
coefficient algebra for a fixed finite equation. -/
theorem solution_of_stageSolutions (a : ι → CoefficientSeries)
    (hSol : ∀ n, Nonempty (Bezout.Solution (fun i => inclusion n (a i)))) :
    Nonempty (Bezout.Solution a) := by
  classical
  obtain ⟨x, hx⟩ := exists_compatible_solutions
    (fun n => (bond n).toRingHom) lipschitzWith_bond denseRange_bond
    (fun n i => inclusion n (a i)) (fun n i => bond_inclusion n (a i)) hSol
  have hreconstruct (i : ι) : ∃ y : CoefficientSeries,
      ∀ n, inclusion n y = (x n).val i :=
    BanachStages.exists_of_compatible (fun n => (x n).val i) (fun n => hx n i)
  choose y hy using hreconstruct
  refine ⟨⟨y, ?_⟩⟩
  apply inclusion_injective 0
  calc
    inclusion 0 (Bezout.pairing a y) =
        Bezout.pairing (fun i => inclusion 0 (a i)) (x 0).val := by
      simp only [Bezout.pairing, map_sum, map_mul, hy]
    _ = 1 := (x 0).property
    _ = inclusion 0 1 := (map_one (inclusion 0)).symm

end AutomaticContinuity.Arens
