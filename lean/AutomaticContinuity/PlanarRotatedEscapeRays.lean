import AutomaticContinuity.PlanarEscapeRays

set_option autoImplicit false

/-! # Escape rays for arbitrary parallel complex-coordinate cuts -/

noncomputable section

namespace AutomaticContinuity.PlanarEscapeRays

open Set Complex

def rotatedCaps (C : Set ℂ) (a : ℂ) (c d : ℝ) : Set ℂ :=
  (C ∩ {z | (a*z).re ≤ c}) ∪ (C ∩ {z | d ≤ (a*z).re})

theorem ray_subset_rotatedCaps_compl {C : Set ℂ} {a z v : ℂ} {c d : ℝ}
    (hav : (a*v).re = 0) (hcz : c < (a*z).re) (hzd : (a*z).re < d) :
    ray z v ⊆ (rotatedCaps C a c d)ᶜ := by
  rintro x ⟨t,_,rfl⟩ hx
  have hre : (a*(z+t•v)).re = (a*z).re := by
    simp [mul_add]
    calc
      _ = t*(a*v).re := by simp only [mul_re]; ring
      _ = 0 := by rw [hav,mul_zero]
  rcases hx with hx | hx
  · have : (a*(z+t•v)).re ≤ c := hx.2
    rw [hre] at this
    linarith
  · have : d ≤ (a*(z+t•v)).re := hx.2
    rw [hre] at this
    linarith

/-- Parallel cuts in an arbitrary complex direction admit the same escape
construction. The degenerate coefficient `a=0` is included. -/
theorem exists_escape_rotatedCaps {C : Set ℂ} (hC : Convex ℝ C)
    (a : ℂ) {c d : ℝ} {z : ℂ} (hz : z ∉ rotatedCaps C a c d) :
    ∃ T : Set ℂ, IsPreconnected T ∧ z ∈ T ∧
      T ⊆ (rotatedCaps C a c d)ᶜ ∧ ¬ Bornology.IsBounded T := by
  by_cases hzC : z ∈ C
  · have hcz : c < (a*z).re := lt_of_not_ge (fun h ↦ hz (Or.inl ⟨hzC,h⟩))
    have hzd : (a*z).re < d := lt_of_not_ge (fun h ↦ hz (Or.inr ⟨hzC,h⟩))
    by_cases ha : a = 0
    · exact ⟨ray z I,isPreconnected_ray z I,mem_ray z I,
        ray_subset_rotatedCaps_compl (by simp [ha]) hcz hzd,
        not_isBounded_ray z I_ne_zero⟩
    · have hv : I/a ≠ 0 := div_ne_zero I_ne_zero ha
      have hav : (a*(I/a)).re = 0 := by
        rw [mul_div_cancel₀ _ ha, I_re]
      exact ⟨ray z (I/a),isPreconnected_ray z (I/a),mem_ray z (I/a),
        ray_subset_rotatedCaps_compl hav hcz hzd,not_isBounded_ray z hv⟩
  · obtain ⟨T,hT,hzT,hTC,hTb⟩ := exists_escape_convex hC hzC
    refine ⟨T,hT,hzT,?_,hTb⟩
    intro x hx hxcap
    exact hTC hx (hxcap.elim And.left And.left)

end AutomaticContinuity.PlanarEscapeRays
