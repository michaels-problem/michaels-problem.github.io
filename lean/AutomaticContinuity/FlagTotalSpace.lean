import AutomaticContinuity.FiniteGeometry
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.FunProp

set_option autoImplicit false

/-!
# The actual total space for finite flag constraints

The deleted set is the finite union of each prescribed affine flag times its
closed Euclidean target ball. Its open complement has exactly the required
section inequalities and explicit product descriptions over the finite strata.
No Oka, Stein, manifold, or holomorphic approximation theorem is asserted here.
-/

noncomputable section

namespace AutomaticContinuity.FlagTotalSpace

open Set

/-- Closed balls for the Euclidean target norm, not the product maximum norm. -/
def closedEuclideanBall (r : ℝ) : Set (ℂ × ℂ) := {v | euclideanPairNorm v ≤ r}

def exteriorEuclideanBall (r : ℝ) : Set (ℂ × ℂ) := {v | r < euclideanPairNorm v}

@[simp] theorem exteriorEuclideanBall_eq_compl (r : ℝ) :
    exteriorEuclideanBall r = (closedEuclideanBall r)ᶜ := by
  ext v
  simp [exteriorEuclideanBall, closedEuclideanBall]

theorem isClosed_closedEuclideanBall (r : ℝ) : IsClosed (closedEuclideanBall r) :=
  isClosed_le continuous_euclideanPairNorm continuous_const

theorem isOpen_exteriorEuclideanBall (r : ℝ) : IsOpen (exteriorEuclideanBall r) :=
  isOpen_lt continuous_const continuous_euclideanPairNorm

theorem closedEuclideanBall_mono {r s : ℝ} (hrs : r ≤ s) :
    closedEuclideanBall r ⊆ closedEuclideanBall s := fun _ hv => hv.trans hrs

theorem exteriorEuclideanBall_antitone {r s : ℝ} (hrs : r ≤ s) :
    exteriorEuclideanBall s ⊆ exteriorEuclideanBall r := fun _ hv => hrs.trans_lt hv

/-- The precise deleted finite union from the manuscript. -/
def forbiddenSet (n : ℕ) : Set (FinitePoint n × (ℂ × ℂ)) :=
  ⋃ k ∈ Finset.Icc 1 n, finiteFlag n k ×ˢ closedEuclideanBall (k : ℝ)

/-- The actual open total space, as a subset of the product coordinate space. -/
def totalSet (n : ℕ) : Set (FinitePoint n × (ℂ × ℂ)) := (forbiddenSet n)ᶜ

theorem mem_forbiddenSet_iff {n : ℕ} {p : FinitePoint n × (ℂ × ℂ)} :
    p ∈ forbiddenSet n ↔ ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
      p.1 ∈ finiteFlag n k ∧ euclideanPairNorm p.2 ≤ (k : ℝ) := by
  simp only [forbiddenSet, mem_iUnion, Finset.mem_Icc, mem_prod, closedEuclideanBall,
    mem_ofPred_eq]
  aesop

theorem isClosed_forbiddenSet (n : ℕ) : IsClosed (forbiddenSet n) := by
  apply isClosed_biUnion_finset
  intro k _hk
  exact (isClosed_finiteFlag n k).prod (isClosed_closedEuclideanBall k)

theorem isOpen_totalSet (n : ℕ) : IsOpen (totalSet n) :=
  (isClosed_forbiddenSet n).isOpen_compl

theorem forbiddenSet_subset_ball (n : ℕ) :
    forbiddenSet n ⊆ Set.univ ×ˢ closedEuclideanBall (n : ℝ) := by
  intro p hp
  obtain ⟨k, _hk, hkn, _hz, hv⟩ := mem_forbiddenSet_iff.mp hp
  exact ⟨trivial, hv.trans (Nat.cast_le.mpr hkn)⟩

/-- Graph membership is exactly the collection of strict flag inequalities. -/
theorem mem_totalSet_iff {n : ℕ} {z : FinitePoint n} {v : ℂ × ℂ} :
    (z, v) ∈ totalSet n ↔
      ∀ k : ℕ, 1 ≤ k → k ≤ n → z ∈ finiteFlag n k → (k : ℝ) < euclideanPairNorm v := by
  change ¬ (z, v) ∈ forbiddenSet n ↔ _
  rw [mem_forbiddenSet_iff]
  simp only [not_exists, not_and, not_le]

@[simp] theorem forbiddenSet_zero : forbiddenSet 0 = ∅ := by simp [forbiddenSet]
@[simp] theorem totalSet_zero : totalSet 0 = Set.univ := by simp [totalSet]

/-- The open total-space subtype carries its inherited topology. -/
abbrev TotalSpace (n : ℕ) := ↥(totalSet n)

def projection (n : ℕ) : TotalSpace n → FinitePoint n := fun p => p.val.1

theorem continuous_projection (n : ℕ) : Continuous (projection n) :=
  continuous_fst.comp continuous_subtype_val

theorem isOpenMap_projection (n : ℕ) : IsOpenMap (projection n) :=
  isOpenMap_fst.comp (isOpen_totalSet n).isOpenMap_subtype_val

theorem projection_surjective (n : ℕ) : Function.Surjective (projection n) := by
  intro z
  have hnorm : ((n + 1 : ℕ) : ℝ) ≤
      euclideanPairNorm (((n + 1 : ℕ) : ℂ), 0) := by
    simpa only [Complex.norm_natCast] using
      norm_fst_le_euclideanPairNorm (((n + 1 : ℕ) : ℂ), 0)
  refine ⟨⟨(z, (((n + 1 : ℕ) : ℂ), 0)), mem_totalSet_iff.mpr ?_⟩, rfl⟩
  intro k _hk hkn _hz
  apply lt_of_lt_of_le _ hnorm
  exact_mod_cast Nat.lt_succ_of_le hkn

/-- A map obeying the bounds gives an actual section into the open total space. -/
def sectionOfMap (n : ℕ) (h : FinitePoint n → ℂ × ℂ)
    (hb : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      ∀ z ∈ finiteFlag n k, (k : ℝ) < euclideanPairNorm (h z)) :
    FinitePoint n → TotalSpace n :=
  fun z => ⟨(z, h z), mem_totalSet_iff.mpr fun k hk hkn hz => hb k hk hkn z hz⟩

@[simp] theorem projection_sectionOfMap (n : ℕ) (h : FinitePoint n → ℂ × ℂ)
    (hb : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      ∀ z ∈ finiteFlag n k, (k : ℝ) < euclideanPairNorm (h z)) (z : FinitePoint n) :
    projection n (sectionOfMap n h hb z) = z := rfl

theorem continuous_sectionOfMap (n : ℕ) (h : FinitePoint n → ℂ × ℂ)
    (hb : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      ∀ z ∈ finiteFlag n k, (k : ℝ) < euclideanPairNorm (h z))
    (hh : Continuous h) : Continuous (sectionOfMap n h hb) :=
  (continuous_id.prodMk hh).subtype_mk _

theorem continuous_sectionOfMap_iff (n : ℕ) (h : FinitePoint n → ℂ × ℂ)
    (hb : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      ∀ z ∈ finiteFlag n k, (k : ℝ) < euclideanPairNorm (h z)) :
    Continuous (sectionOfMap n h hb) ↔ Continuous h := by
  constructor
  · intro hs
    exact continuous_snd.comp (continuous_subtype_val.comp hs)
  · exact continuous_sectionOfMap n h hb

/-- A section of the actual projection yields precisely the original bounds. -/
theorem bounds_of_section (n : ℕ) (s : FinitePoint n → TotalSpace n)
    (hs : ∀ z, projection n (s z) = z) :
    ∀ k : ℕ, 1 ≤ k → k ≤ n → ∀ z ∈ finiteFlag n k,
      (k : ℝ) < euclideanPairNorm (s z).val.2 := by
  intro k hk hkn z hz
  apply mem_totalSet_iff.mp (s z).property k hk hkn
  simpa only [show (s z).val.1 = z from hs z] using hz

/-- Level `n` is the last stratum; no nonexistent stricter flag is subtracted. -/
def stratum (n k : ℕ) : Set (FinitePoint n) :=
  {z | z ∈ finiteFlag n k ∧ (k < n → z ∉ finiteFlag n (k + 1))}

theorem stratum_eq_diff {n k : ℕ} (hk : k < n) :
    stratum n k = finiteFlag n k \ finiteFlag n (k + 1) := by
  ext z
  simp [stratum, hk]

@[simp] theorem stratum_last (n : ℕ) : stratum n n = finiteFlag n n := by
  ext z
  simp [stratum]

@[simp] theorem stratum_zero_zero : stratum 0 0 = Set.univ := by
  simp

theorem stratum_zero_of_pos {n : ℕ} (hn : 0 < n) :
    stratum n 0 = (finiteFlag n 1)ᶜ := by
  rw [stratum_eq_diff hn, finiteFlag_zero, zero_add]
  ext z
  simp

/-- The fibre model is unrestricted at level zero and the exact ball exterior
at every positive level. This includes the zero-dimensional base correctly. -/
def modelFiber (k : ℕ) : Set (ℂ × ℂ) :=
  if k = 0 then Set.univ else exteriorEuclideanBall (k : ℝ)

def fiber (n : ℕ) (z : FinitePoint n) : Set (ℂ × ℂ) :=
  {v | (z, v) ∈ totalSet n}

theorem mem_totalSet_iff_of_stratum {n k : ℕ} (hkn : k ≤ n)
    {z : FinitePoint n} (hz : z ∈ stratum n k) {v : ℂ × ℂ} :
    (z, v) ∈ totalSet n ↔ v ∈ modelFiber k := by
  rw [mem_totalSet_iff]
  by_cases hk : k = 0
  · subst k
    simp only [modelFiber, ↓reduceIte, mem_univ, iff_true]
    intro j hj hjn hzj
    exact False.elim (hz.2 (by omega) (finiteFlag_antitone n hj hzj))
  · simp only [modelFiber, hk, ↓reduceIte, exteriorEuclideanBall, mem_ofPred_eq]
    constructor
    · intro h
      exact h k (Nat.one_le_iff_ne_zero.mpr hk) hkn hz.1
    · intro hv j hj hjn hzj
      by_cases hjk : j ≤ k
      · exact (Nat.cast_le.mpr hjk).trans_lt hv
      · exact False.elim (hz.2 (by omega)
          (finiteFlag_antitone n (by omega : k + 1 ≤ j) hzj))

theorem fiber_eq_of_stratum {n k : ℕ} (hkn : k ≤ n)
    {z : FinitePoint n} (hz : z ∈ stratum n k) : fiber n z = modelFiber k := by
  ext v
  exact mem_totalSet_iff_of_stratum hkn hz

theorem fiber_eq_univ_of_not_mem {n : ℕ} {z : FinitePoint n}
    (hz : z ∉ finiteFlag n 1) : fiber n z = Set.univ := by
  ext v
  simp only [fiber, mem_ofPred_eq, mem_univ, iff_true, mem_totalSet_iff]
  intro k hk _hkn hzk
  exact False.elim (hz (finiteFlag_antitone n hk hzk))

@[simp] theorem fiber_zero (z : FinitePoint 0) : fiber 0 z = Set.univ := by
  simp [fiber]

/-- The fibre as a subset of the actual total-space subtype is homeomorphic to
the corresponding subset of the two target coordinates. -/
def fiberHomeomorph (n : ℕ) (z : FinitePoint n) :
    {p : TotalSpace n // projection n p = z} ≃ₜ fiber n z where
  toFun p := ⟨p.val.val.2, by
    change (z, p.val.val.2) ∈ totalSet n
    have hz : p.val.val.1 = z := p.property
    exact (congrArg (fun w : FinitePoint n => (w, p.val.val.2) ∈ totalSet n) hz).mp
      p.val.property⟩
  invFun v := ⟨⟨(z, v.val), v.property⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact p.property.symm
    · rfl
  right_inv v := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).snd.subtype_mk _
  continuous_invFun :=
    ((continuous_const.prodMk continuous_subtype_val).subtype_mk _).subtype_mk _

/-- The precise fibre model on every stratum, including the final point. -/
def fiberHomeomorphOfStratum {n k : ℕ} (hkn : k ≤ n)
    {z : FinitePoint n} (hz : z ∈ stratum n k) :
    {p : TotalSpace n // projection n p = z} ≃ₜ modelFiber k :=
  (fiberHomeomorph n z).trans (Homeomorph.setCongr (fiber_eq_of_stratum hkn hz))

/-- Off the first constrained flag the complete target plane is the fibre. -/
def fiberHomeomorphOutside {n : ℕ} {z : FinitePoint n} (hz : z ∉ finiteFlag n 1) :
    {p : TotalSpace n // projection n p = z} ≃ₜ (ℂ × ℂ) :=
  ((fiberHomeomorph n z).trans (Homeomorph.setCongr (fiber_eq_univ_of_not_mem hz))).trans
    (Homeomorph.Set.univ _)

/-- The restricted total space, still a subset of the original ambient product. -/
def restrictedTotalSet (n k : ℕ) : Set (FinitePoint n × (ℂ × ℂ)) :=
  {p | p.1 ∈ stratum n k ∧ p ∈ totalSet n}

theorem restrictedTotalSet_eq_prod {n k : ℕ} (hkn : k ≤ n) :
    restrictedTotalSet n k = stratum n k ×ˢ modelFiber k := by
  ext p
  change (p.1 ∈ stratum n k ∧ p ∈ totalSet n) ↔
    p.1 ∈ stratum n k ∧ p.2 ∈ modelFiber k
  by_cases hz : p.1 ∈ stratum n k
  · simp only [hz, true_and]
    exact mem_totalSet_iff_of_stratum hkn hz
  · simp only [hz, false_and]

/-- Each restriction is explicitly the product over its stratum. This is a
topological trivialisation; no holomorphic-bundle theorem is assumed. -/
def stratumTrivialization {n k : ℕ} (hkn : k ≤ n) :
    restrictedTotalSet n k ≃ₜ (stratum n k × modelFiber k) :=
  (Homeomorph.setCongr (restrictedTotalSet_eq_prod hkn)).trans
    (Homeomorph.Set.prod _ _)

@[simp] theorem stratumTrivialization_fst {n k : ℕ} (hkn : k ≤ n)
    (p : restrictedTotalSet n k) : (stratumTrivialization hkn p).1.val = p.val.1 := rfl

@[simp] theorem stratumTrivialization_snd {n k : ℕ} (hkn : k ≤ n)
    (p : restrictedTotalSet n k) : (stratumTrivialization hkn p).2.val = p.val.2 := rfl

theorem exists_stratum (n : ℕ) (z : FinitePoint n) :
    ∃ k : ℕ, k ≤ n ∧ z ∈ stratum n k := by
  classical
  let s : Finset ℕ := (Finset.range (n + 1)).filter fun k => z ∈ finiteFlag n k
  have hzero : 0 ∈ s := by simp [s]
  have hs : s.Nonempty := ⟨0, hzero⟩
  let k := s.max' hs
  have hkmem : k ∈ s := s.max'_mem hs
  obtain ⟨hkRange, hkFlag⟩ := Finset.mem_filter.mp hkmem
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkRange)
  refine ⟨k, hkn, hkFlag, ?_⟩
  intro hkn' hznext
  have hnext : k + 1 ∈ s :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hznext⟩
  have hmax : k + 1 ≤ k := s.le_max' _ hnext
  omega

theorem stratum_index_unique {n k l : ℕ} (hkn : k ≤ n) (hln : l ≤ n)
    {z : FinitePoint n} (hzk : z ∈ stratum n k) (hzl : z ∈ stratum n l) : k = l := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hzk.2 (hlt.trans_le hln) (finiteFlag_antitone n (Nat.succ_le_of_lt hlt) hzl.1)
  · exact hzl.2 (hgt.trans_le hkn) (finiteFlag_antitone n (Nat.succ_le_of_lt hgt) hzk.1)

theorem iUnion_stratum (n : ℕ) : (⋃ k : Fin (n + 1), stratum n k.val) = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro z
  obtain ⟨k, hkn, hz⟩ := exists_stratum n z
  exact Set.mem_iUnion.mpr ⟨⟨k, Nat.lt_succ_iff.mpr hkn⟩, hz⟩

theorem fiber_prescribedPoint {n : ℕ} (hn : 0 < n) :
    fiber n (prescribedPoint n) = exteriorEuclideanBall (n : ℝ) := by
  have hz : prescribedPoint n ∈ stratum n n := by
    rw [stratum_last]
    exact prescribedPoint_mem_finiteFlag n n
  rw [fiber_eq_of_stratum le_rfl hz]
  simp only [modelFiber, Nat.ne_of_gt hn, ↓reduceIte]

theorem isLocallyClosed_stratum {n k : ℕ} (hkn : k ≤ n) :
    IsLocallyClosed (stratum n k) := by
  by_cases hk : k < n
  · rw [stratum_eq_diff hk]
    refine ⟨(finiteFlag n (k + 1))ᶜ, finiteFlag n k,
      (isClosed_finiteFlag n (k + 1)).isOpen_compl, isClosed_finiteFlag n k, ?_⟩
    ext z
    simp only [mem_sdiff, mem_inter_iff, mem_compl_iff, and_comm]
  · have heq : k = n := by omega
    subst k
    rw [stratum_last]
    exact (isClosed_finiteFlag n n).isLocallyClosed

theorem stratum_nonempty {n k : ℕ} (hkn : k ≤ n) : (stratum n k).Nonempty := by
  by_cases hk : k < n
  · rw [stratum_eq_diff hk]
    exact Set.not_subset.mp (ssubset_iff_subset_not_subset.mp (finiteFlag_succ_ssubset hk)).2
  · have heq : k = n := by omega
    subst k
    rw [stratum_last]
    exact finiteFlag_nonempty n n

/-- The closed affine flag at level `k` is exactly the union of strata at that
level and all deeper levels, giving the finite closed filtration explicitly. -/
theorem flag_eq_union_strata {n k : ℕ} (hkn : k ≤ n) :
    finiteFlag n k = ⋃ l : Fin (n + 1), ⋃ (_hkl : k ≤ l.val), stratum n l.val := by
  ext z
  constructor
  · intro hz
    obtain ⟨l, hln, hzl⟩ := exists_stratum n z
    have hkl : k ≤ l := by
      by_contra h
      have hlk : l < k := Nat.lt_of_not_ge h
      exact hzl.2 (hlk.trans_le hkn)
        (finiteFlag_antitone n (Nat.succ_le_of_lt hlk) hz)
    exact Set.mem_iUnion.mpr ⟨⟨l, Nat.lt_succ_iff.mpr hln⟩, Set.mem_iUnion.mpr ⟨hkl, hzl⟩⟩
  · intro hz
    obtain ⟨l, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hkl, hz⟩ := Set.mem_iUnion.mp hz
    exact finiteFlag_antitone n hkl hz.1

/-- Positive strata have the exact closed-ball complement as their fibre. -/
def positiveFiberHomeomorph {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    {z : FinitePoint n} (hz : z ∈ stratum n k) :
    {p : TotalSpace n // projection n p = z} ≃ₜ exteriorEuclideanBall (k : ℝ) :=
  (fiberHomeomorphOfStratum hkn hz).trans (Homeomorph.setCongr (by
    simp only [modelFiber, Nat.ne_of_gt hk, ↓reduceIte]))

/-- At dimension zero there are no forbidden balls, including no artificial
radius-zero restriction. -/
def zeroDimensionalFiberHomeomorph (z : FinitePoint 0) :
    {p : TotalSpace 0 // projection 0 p = z} ≃ₜ (ℂ × ℂ) :=
  ((fiberHomeomorph 0 z).trans (Homeomorph.setCongr (fiber_zero z))).trans
    (Homeomorph.Set.univ _)

end AutomaticContinuity.FlagTotalSpace
