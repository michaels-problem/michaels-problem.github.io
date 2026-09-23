import AutomaticContinuity.BanachStages
import AutomaticContinuity.CoherentReconstruction

set_option autoImplicit false

namespace AutomaticContinuity.BanachStages

open CoefficientSeries

/-- Every compatible sequence of the actual Banach completions comes from one
element of the original coefficient algebra. -/
theorem exists_of_compatible (b : (n : ℕ) → Stage n)
    (hb : ∀ n, bond n (b (n + 1)) = b n) :
    ∃ a : CoefficientSeries, ∀ n, inclusion n a = b n := by
  exact CoherentReconstruction.exists_of_compatible
    (fun n => (inclusion n).toAddMonoidHom) (fun n => bond n)
    norm_inclusion denseRange_inclusion lipschitzWith_bond bond_inclusion b hb

/-- A single positive coefficient norm separates points before completion. -/
theorem inclusion_injective (n : ℕ) : Function.Injective (inclusion n) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply (q_eq_zero_iff (Nat.succ_pos n) (a - b)).mp
  rw [← norm_inclusion, map_sub, hab, sub_self, norm_zero]

end AutomaticContinuity.BanachStages
