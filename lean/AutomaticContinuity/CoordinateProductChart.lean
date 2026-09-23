import AutomaticContinuity.CoordinateProductGeometry
import AutomaticContinuity.CoordinateCutConvexity

set_option autoImplicit false

/-! # Product compact sets in the actual affine cut chart -/

noncomputable section

namespace AutomaticContinuity.CoordinateCutChart

open Set FiniteHalfspaceExhaustion

def secondAffine {n : ℕ} (j : Fin n) (a : ℂ) (b : ℝ) :
    FinitePoint n →ᵃ[ℝ] ℂ where
  toFun z := a*z j-(b:ℂ)
  linear :=
    { toFun := fun z => a*z j
      map_add' := by intro z w; simp [mul_add]
      map_smul' := by intro s z; simp; ring }
  map_vadd' := by intro z w; change a*(w j+z j)-(b:ℂ)=a*w j+(a*z j-(b:ℂ)); ring

theorem exists_product_chart {n : ℕ} {L : Set (FinitePoint n)}
    (hL : IsCompactConvexProduct L) (j : Fin n) (a : ℂ) (ha : a ≠ 0) (b : ℝ) :
    ∃ (D : Set (Remaining j)) (C : Set ℂ),
      IsCompact D ∧ Convex ℝ D ∧ IsCompact C ∧ Convex ℝ C ∧
      L = (homeomorph j a ha b) ⁻¹' (D ×ˢ C) := by
  classical
  obtain ⟨Q, hQ, rfl⟩ := hL
  let L := Set.pi univ Q
  have hLc : IsCompact L := by
    convert isCompact_pi_infinite (fun i => (hQ i).1) using 1
    ext x
    simp [L, Set.mem_pi]
  have hLconv : Convex ℝ L := convex_pi (fun i _ => (hQ i).2)
  let d : FinitePoint n →ₗ[ℝ] Remaining j := LinearMap.pi (fun i => LinearMap.proj i.val)
  let D : Set (Remaining j) := d '' L
  let C : Set ℂ := secondAffine j a b '' L
  have hd : Continuous d := by change Continuous (fun z : FinitePoint n => fun i : {i // i ≠ j} => z i); fun_prop
  have hc : Continuous (secondAffine j a b) := by change Continuous (fun z : FinitePoint n => a*z j-(b:ℂ)); fun_prop
  refine ⟨D, C, hLc.image hd, hLconv.linear_image d, hLc.image hc,
    hLconv.affine_image (secondAffine j a b), ?_⟩
  ext z
  constructor
  · intro hz
    exact ⟨⟨z,hz,rfl⟩,⟨z,hz,rfl⟩⟩
  · rintro ⟨⟨x,hx,hxd⟩,⟨y,hy,hyc⟩⟩
    intro i _
    by_cases hij : i = j
    · subst i
      have hmul : a*y j = a*z j := by
        change a*y j-(b:ℂ)=a*z j-(b:ℂ) at hyc
        linear_combination hyc
      have hyz : y j = z j := mul_left_cancel₀ ha hmul
      simpa only [hyz] using hy j (mem_univ j)
    · have hxz : x i = z i := congrFun hxd ⟨i,hij⟩
      simpa only [hxz] using hx i (mem_univ i)

theorem halfspace_preimage {n : ℕ} (q : CoordinateCut n) (ha : q.coefficient ≠ 0)
    {L : Set (FinitePoint n)} {D : Set (Remaining q.coordinate)} {C : Set ℂ}
    (hL : L = (homeomorph q.coordinate q.coefficient ha q.bound) ⁻¹' (D ×ˢ C)) :
    L ∩ q.halfspace =
      (homeomorph q.coordinate q.coefficient ha q.bound) ⁻¹'
        (D ×ˢ (C ∩ {w : ℂ | w.re ≤ 0})) := by
  ext z
  rw [hL]
  change ((chart q.coordinate q.coefficient ha q.bound z).1 ∈ D ∧
      (chart q.coordinate q.coefficient ha q.bound z).2 ∈ C) ∧
      (q.coefficient*z q.coordinate).re ≤ q.bound ↔
    (chart q.coordinate q.coefficient ha q.bound z).1 ∈ D ∧
      (chart q.coordinate q.coefficient ha q.bound z).2 ∈ C ∧
      ((chart q.coordinate q.coefficient ha q.bound z).2).re ≤ 0
  rw [second_re]
  constructor <;> intro h
  · exact ⟨h.1.1,h.1.2,sub_nonpos.mpr h.2⟩
  · exact ⟨⟨h.1,h.2.1⟩,sub_nonpos.mp h.2.2⟩

end AutomaticContinuity.CoordinateCutChart
