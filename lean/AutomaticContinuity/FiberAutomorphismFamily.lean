import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.ContinuousOn

set_option autoImplicit false

/-!
# An actual product homeomorphism from a continuous family of fibre automorphisms

The base domain is a subtype, and both joint continuity assumptions are made
only above that domain. No extension of coefficient functions outside the
domain is needed. Joint ambient holomorphy can be supplied separately by the
polynomial-flow construction.
-/

noncomputable section

namespace AutomaticContinuity.FiberAutomorphismFamily

variable {P E : Type*} [TopologicalSpace P] [TopologicalSpace E]

def homeomorphOn (φ : P → E ≃ₜ E) (U : Set P)
    (hf : ContinuousOn (fun z : P × E => φ z.1 z.2) (U ×ˢ Set.univ))
    (hi : ContinuousOn (fun z : P × E => (φ z.1).symm z.2) (U ×ˢ Set.univ)) :
    (U × E) ≃ₜ (U × E) where
  toFun z := (z.1, φ z.1.val z.2)
  invFun z := (z.1, (φ z.1.val).symm z.2)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := continuous_fst.prodMk
    (hf.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun z => ⟨z.1.property, Set.mem_univ _⟩))
  continuous_invFun := continuous_fst.prodMk
    (hi.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun z => ⟨z.1.property, Set.mem_univ _⟩))

@[simp] theorem homeomorphOn_base (φ : P → E ≃ₜ E) (U : Set P)
    (hf : ContinuousOn (fun z : P × E => φ z.1 z.2) (U ×ˢ Set.univ))
    (hi : ContinuousOn (fun z : P × E => (φ z.1).symm z.2) (U ×ˢ Set.univ))
    (z : U × E) : (homeomorphOn φ U hf hi z).1 = z.1 := rfl

@[simp] theorem homeomorphOn_fibre (φ : P → E ≃ₜ E) (U : Set P)
    (hf : ContinuousOn (fun z : P × E => φ z.1 z.2) (U ×ˢ Set.univ))
    (hi : ContinuousOn (fun z : P × E => (φ z.1).symm z.2) (U ×ˢ Set.univ))
    (z : U × E) : (homeomorphOn φ U hf hi z).2 = φ z.1.val z.2 := rfl

@[simp] theorem homeomorphOn_inverse_fibre (φ : P → E ≃ₜ E) (U : Set P)
    (hf : ContinuousOn (fun z : P × E => φ z.1 z.2) (U ×ˢ Set.univ))
    (hi : ContinuousOn (fun z : P × E => (φ z.1).symm z.2) (U ×ˢ Set.univ))
    (z : U × E) : ((homeomorphOn φ U hf hi).symm z).2 = (φ z.1.val).symm z.2 := rfl

end AutomaticContinuity.FiberAutomorphismFamily
