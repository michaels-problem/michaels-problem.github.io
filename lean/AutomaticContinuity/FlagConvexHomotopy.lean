import AutomaticContinuity.FlagAffineContraction
import AutomaticContinuity.EuclideanExteriorPaths
import Mathlib.Topology.Homotopy.Basic

set_option autoImplicit false

/-!
# Admissible homotopies on a convex base

The affine contraction uses a point in the deepest flag actually meeting the
base. Its constant endpoints are joined outside that flag's Euclidean ball.
This constructs a continuous admissible homotopy; it asserts no holomorphic
approximation or holomorphicity of the intermediate sections.
-/

noncomputable section

namespace AutomaticContinuity.FlagConvexHomotopy

open Set FlagTotalSpace FlagAffineContraction
open scoped unitInterval

abbrev Pair := ℂ × ℂ

def Admissible {n : ℕ} (W : Set (FinitePoint n)) (f : C(W, Pair)) : Prop :=
  ∀ z : W, (z.val, f z) ∈ totalSet n

def sectionMap {n : ℕ} {W : Set (FinitePoint n)} (h : FinitePoint n → Pair)
    (hh : ContinuousOn h W) : C(W, Pair) := ⟨W.domRestrict h, hh.domRestrict⟩

def contractionHomotopy {n j : ℕ} {W : Set (FinitePoint n)}
    (hW : Convex ℝ W) {c : FinitePoint n} (hcW : c ∈ W)
    (hcj : c ∈ finiteFlag n j)
    (hmax : ∀ k : ℕ, k ≤ n → (W ∩ finiteFlag n k).Nonempty → k ≤ j)
    (h : FinitePoint n → Pair) (hh : ContinuousOn h W)
    (hadm : ∀ z ∈ W, (z, h z) ∈ totalSet n) :
    ContinuousMap.HomotopyWith (ContinuousMap.const W (h c)) (sectionMap h hh)
      (Admissible W) where
  toFun p := h (contraction c p.1 p.2)
  continuous_toFun := hh.comp_continuous
    ((continuous_contraction c).comp
      (show Continuous (fun p : unitInterval × W => ((p.1 : ℝ), (p.2 : FinitePoint n)))
        from (continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)))
    (fun p => contraction_mem hW hcW p.2.property p.1.property)
  map_zero_left z := by simp
  map_one_left z := by simp [sectionMap]
  prop' t z := contraction_admissible hW hcW hcj hmax hadm t.property z z.property

theorem exists_admissible_homotopy {n : ℕ} {W : Set (FinitePoint n)}
    (hW : Convex ℝ W) (hWne : W.Nonempty)
    (h g : FinitePoint n → Pair) (hh : ContinuousOn h W) (hg : ContinuousOn g W)
    (hadm : ∀ z ∈ W, (z, h z) ∈ totalSet n)
    (gadm : ∀ z ∈ W, (z, g z) ∈ totalSet n) :
    Nonempty (ContinuousMap.HomotopyWith (sectionMap h hh) (sectionMap g hg)
      (Admissible W)) := by
  classical
  obtain ⟨j, hjn, c, hcW, hcj, hmax⟩ := exists_deepest_center hWne
  have hpath : ∃ p : Path (h c) (g c), ∀ t : unitInterval,
      ∀ z ∈ W, (z, p t) ∈ totalSet n := by
    by_cases hj : j = 0
    · let p := (convex_univ : Convex ℝ (univ : Set Pair)).isPathConnected
        (by simp) |>.joinedIn (h c) (mem_univ _) (g c) (mem_univ _)
      refine ⟨p.somePath, ?_⟩
      intro t z hz
      apply mem_totalSet_iff.mpr
      intro k hk hkn hzk
      have := hmax k hkn ⟨z, hz, hzk⟩
      omega
    · have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
      have hhc := mem_totalSet_iff.mp (hadm c hcW) j hjpos hjn hcj
      have hgc := mem_totalSet_iff.mp (gadm c hcW) j hjpos hjn hcj
      have p := EuclideanExteriorPaths.joinedIn_exterior (Nat.cast_nonneg j) hhc hgc
      refine ⟨p.somePath, ?_⟩
      intro t z hz
      apply mem_totalSet_iff.mpr
      intro k hk hkn hzk
      have hkj := hmax k hkn ⟨z, hz, hzk⟩
      exact lt_of_le_of_lt (Nat.cast_le.mpr hkj) (p.somePath_mem t)
  obtain ⟨p, hp⟩ := hpath
  let mid : ContinuousMap.HomotopyWith (ContinuousMap.const W (h c))
      (ContinuousMap.const W (g c)) (Admissible W) :=
    { toFun := fun x => p x.1
      continuous_toFun := p.continuous.comp continuous_fst
      map_zero_left := fun _ => p.source
      map_one_left := fun _ => p.target
      prop' := fun t z => hp t z z.property }
  exact ⟨((contractionHomotopy hW hcW hcj hmax h hh hadm).symm.trans mid).trans
    (contractionHomotopy hW hcW hcj hmax g hg gadm)⟩

/-- The homotopy is supplied as an ambient function with regularity only on
the actual product domain, matching the global cutoff-patching interface. -/
theorem exists_ambient_homotopy {n : ℕ} {W : Set (FinitePoint n)}
    (hW : Convex ℝ W) (hWne : W.Nonempty)
    (h g : FinitePoint n → Pair) (hh : ContinuousOn h W) (hg : ContinuousOn g W)
    (hadm : ∀ z ∈ W, (z, h z) ∈ totalSet n)
    (gadm : ∀ z ∈ W, (z, g z) ∈ totalSet n) :
    ∃ H : ℝ × FinitePoint n → Pair, ContinuousOn H (Icc 0 1 ×ˢ W) ∧
      (∀ z ∈ W, H (0, z) = h z) ∧ (∀ z ∈ W, H (1, z) = g z) ∧
      ∀ t ∈ Icc 0 1, ∀ z ∈ W, (z, H (t, z)) ∈ totalSet n := by
  classical
  obtain ⟨F⟩ := exists_admissible_homotopy hW hWne h g hh hg hadm gadm
  let H : ℝ × FinitePoint n → Pair := fun p =>
    if ht : p.1 ∈ Icc 0 1 then
      if hz : p.2 ∈ W then F (⟨p.1, ht⟩, ⟨p.2, hz⟩) else 0
    else 0
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun p : Icc (0 : ℝ) 1 ×ˢ W =>
        (⟨p.val.1, p.property.1⟩, ⟨p.val.2, p.property.2⟩) :
          (Icc (0 : ℝ) 1 ×ˢ W) → unitInterval × W) := by fun_prop
    convert F.continuous.comp hc using 1
    funext p
    change H p.val = F (⟨p.val.1, p.property.1⟩, ⟨p.val.2, p.property.2⟩)
    simp only [H, dite_eq_left p.property.1, dite_eq_left p.property.2]
  · intro z hz
    simpa [H, hz, sectionMap] using F.apply_zero ⟨z, hz⟩
  · intro z hz
    simpa [H, hz, sectionMap] using F.apply_one ⟨z, hz⟩
  · intro t ht z hz
    simp only [H, dite_eq_left ht, dite_eq_left hz]
    exact F.prop ⟨t, ht⟩ ⟨z, hz⟩

end AutomaticContinuity.FlagConvexHomotopy
