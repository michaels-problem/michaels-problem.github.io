import AutomaticContinuity.HomogeneousPowerBasis

set_option autoImplicit false

/-!
# Homogeneous polynomial vector fields as finite sums of complete directions

The fields are actual pairs of two-variable polynomials. Divergence is
removed by overshears; Euler's identity then supplies a Hamiltonian, whose
fixed linear-form expansion supplies shears. All slopes are fixed integers.
-/

noncomputable section

namespace AutomaticContinuity.HomogeneousFieldDecomposition

open MvPolynomial HomogeneousPowerBasis
open scoped BigOperators

abbrev Field := Poly × Poly

def shear (s : ℂ) (d : ℕ) : Field :=
  (-s • linearForm s ^ d, linearForm s ^ d)

def overshear (s : ℂ) (m : ℕ) : Field :=
  (-s • (linearForm s ^ m * X 1), linearForm s ^ m * X 1)

def divergence : Field →ₗ[ℂ] Poly where
  toFun F := pderiv 0 F.1 + pderiv 1 F.2
  map_add' F G := by simp only [Prod.fst_add, Prod.snd_add, map_add]; abel
  map_smul' c F := by simp only [Prod.smul_fst, Prod.smul_snd, Derivation.map_smul, smul_add]; rfl

def hamiltonian : Poly →ₗ[ℂ] Field where
  toFun p := (pderiv 1 p, -pderiv 0 p)
  map_add' p q := by simp only [map_add, neg_add]; rfl
  map_smul' c p := by simp [Derivation.map_smul, smul_neg]

@[simp] theorem pderiv_linearForm_zero (s : ℂ) : pderiv 0 (linearForm s) = 1 := by
  simp [linearForm]

@[simp] theorem pderiv_linearForm_one (s : ℂ) : pderiv 1 (linearForm s) = C s := by
  simp [linearForm]

theorem divergence_overshear (s : ℂ) (m : ℕ) :
    divergence (overshear s m) = linearForm s ^ m := by
  simp only [divergence, LinearMap.coe_mk, AddHom.coe_mk, overshear,
    pderiv_mul, pderiv_pow, pderiv_linearForm_zero, pderiv_C,
    pderiv_linearForm_one, pderiv_X_self, pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0),
    smul_eq_C_mul, map_neg]
  ring

theorem hamiltonian_linearForm_pow (s : ℂ) (d : ℕ) :
    hamiltonian (linearForm s ^ (d + 1)) = (-(d + 1 : ℂ)) • shear s d := by
  apply Prod.ext <;>
    simp only [hamiltonian, LinearMap.coe_mk, AddHom.coe_mk, shear,
      Prod.smul_fst, Prod.smul_snd, pderiv_pow, Nat.add_sub_cancel,
      pderiv_linearForm_zero, pderiv_linearForm_one, smul_eq_C_mul,
      map_neg, map_add, map_one, map_natCast, Nat.cast_add, Nat.cast_one] <;> ring

theorem euler_two {d : ℕ} {p : Poly} (hp : p.IsHomogeneous d) :
    X 0 * pderiv 0 p + X 1 * pderiv 1 p = (d : ℂ) • p := by
  simpa only [Fin.sum_univ_two, smul_eq_C_mul, map_natCast, nsmul_eq_mul] using
    hp.sum_X_mul_pderiv

/-- Euler's identity produces the actual Hamiltonian of a homogeneous
divergence-free vector field. -/
theorem hamiltonian_of_divergence_zero {d : ℕ} {P Q : Poly}
    (hP : P.IsHomogeneous d) (hQ : Q.IsHomogeneous d)
    (hdiv : divergence (P, Q) = 0) :
    hamiltonian (((d + 1 : ℂ)⁻¹) • (X 1 * P - X 0 * Q)) = (P, Q) := by
  have hd : (d + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
  change pderiv 0 P + pderiv 1 Q = 0 at hdiv
  have hy : pderiv 1 (X 1 * P - X 0 * Q) = (d + 1 : ℂ) • P := by
    simp only [map_sub, pderiv_mul, pderiv_X_self,
      pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1), one_mul, zero_mul, zero_add]
    calc
      P + X 1 * pderiv 1 P - X 0 * pderiv 1 Q =
          P + (X 0 * pderiv 0 P + X 1 * pderiv 1 P) -
            X 0 * (pderiv 0 P + pderiv 1 Q) := by ring
      _ = (d + 1 : ℂ) • P := by rw [hdiv, euler_two hP]; simp [add_smul, add_comm]
  have hx : -(pderiv 0 (X 1 * P - X 0 * Q)) = (d + 1 : ℂ) • Q := by
    simp only [map_sub, pderiv_mul, pderiv_X_self,
      pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0), one_mul, zero_mul, zero_add]
    calc
      -(X 1 * pderiv 0 P - (Q + X 0 * pderiv 0 Q)) =
          Q + (X 0 * pderiv 0 Q + X 1 * pderiv 1 Q) -
            X 1 * (pderiv 0 P + pderiv 1 Q) := by ring
      _ = (d + 1 : ℂ) • Q := by rw [hdiv, euler_two hQ]; simp [add_smul, add_comm]
  apply Prod.ext
  · change pderiv 1 ((d + 1 : ℂ)⁻¹ • _) = P
    rw [Derivation.map_smul, hy, smul_smul, inv_mul_cancel₀ hd, one_smul]
  · change -(pderiv 0 ((d + 1 : ℂ)⁻¹ • _)) = Q
    rw [Derivation.map_smul, ← smul_neg, hx, smul_smul, inv_mul_cancel₀ hd, one_smul]

theorem overshear_homogeneous (s : ℂ) (m : ℕ) :
    (overshear s m).1.IsHomogeneous (m + 1) ∧
      (overshear s m).2.IsHomogeneous (m + 1) := by
  have hh := (linearForm_pow_homogeneous s m).mul (isHomogeneous_X ℂ (1 : Fin 2))
  exact ⟨(homogeneousSubmodule (Fin 2) ℂ (m + 1)).smul_mem (-s) hh, hh⟩

theorem shear_homogeneous (s : ℂ) (d : ℕ) :
    (shear s d).1.IsHomogeneous d ∧ (shear s d).2.IsHomogeneous d := by
  have hh := linearForm_pow_homogeneous s d
  exact ⟨(homogeneousSubmodule (Fin 2) ℂ d).smul_mem (-s) hh, hh⟩

/-- Every actual degree-`m+1` homogeneous polynomial vector field is a sum
of `m+1` overshears and `m+3` shears in fixed integer directions. -/
theorem exists_decomposition (m : ℕ) (P Q : Poly)
    (hP : P.IsHomogeneous (m + 1)) (hQ : Q.IsHomogeneous (m + 1)) :
    ∃ c : Fin (m + 1) → ℂ, ∃ b : Fin (m + 3) → ℂ,
      (P, Q) = (∑ j, c j • overshear (j.val : ℂ) m) +
        ∑ j, b j • shear (j.val : ℂ) (m + 1) := by
  have hD : (divergence (P, Q)).IsHomogeneous m := by
    simpa only [divergence, LinearMap.coe_mk, AddHom.coe_mk, Nat.add_sub_cancel] using
      hP.pderiv.add hQ.pderiv
  obtain ⟨c, hc⟩ := HomogeneousPowerBasis.exists_expansion hD
  let O : Field := ∑ j : Fin (m + 1), c j • overshear (j.val : ℂ) m
  let R : Field := (P, Q) - O
  have hO : O.1.IsHomogeneous (m + 1) ∧ O.2.IsHomogeneous (m + 1) := by
    constructor
    · simp only [O, Prod.fst_sum, Prod.smul_fst]
      exact (homogeneousSubmodule (Fin 2) ℂ (m + 1)).sum_mem fun j _ =>
        (homogeneousSubmodule (Fin 2) ℂ (m + 1)).smul_mem _ (overshear_homogeneous _ _).1
    · simp only [O, Prod.snd_sum, Prod.smul_snd]
      exact (homogeneousSubmodule (Fin 2) ℂ (m + 1)).sum_mem fun j _ =>
        (homogeneousSubmodule (Fin 2) ℂ (m + 1)).smul_mem _ (overshear_homogeneous _ _).2
  have hR1 : R.1.IsHomogeneous (m + 1) := hP.sub hO.1
  have hR2 : R.2.IsHomogeneous (m + 1) := hQ.sub hO.2
  have hRdiv : divergence R = 0 := by
    simp only [R, O, map_sub, map_sum, map_smul, divergence_overshear]
    exact sub_eq_zero.mpr hc
  let H : Poly := (m + 2 : ℂ)⁻¹ • (X 1 * R.1 - X 0 * R.2)
  have hH : H.IsHomogeneous (m + 2) := by
    apply (homogeneousSubmodule (Fin 2) ℂ (m + 2)).smul_mem
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ((isHomogeneous_X ℂ (1 : Fin 2)).mul hR1).sub
        ((isHomogeneous_X ℂ (0 : Fin 2)).mul hR2)
  obtain ⟨b, hb⟩ := HomogeneousPowerBasis.exists_expansion hH
  have hHR : hamiltonian H = R := by
    simpa only [H, Nat.cast_add, Nat.cast_one, show (2 : ℂ) = 1 + 1 from by norm_num,
      add_assoc] using hamiltonian_of_divergence_zero hR1 hR2 hRdiv
  have hRsum : R = ∑ j : Fin (m + 3), (b j * (-(m + 2 : ℂ))) •
      shear (j.val : ℂ) (m + 1) := by
    rw [← hHR, hb, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul]
    have hh := hamiltonian_linearForm_pow (j.val : ℂ) (m + 1)
    convert congrArg (fun F : Field => b j • F) hh using 1
    simp only [smul_smul, Nat.cast_add, Nat.cast_one, add_assoc]
    norm_num
  refine ⟨c, fun j => b j * (-(m + 2 : ℂ)), ?_⟩
  change (P, Q) = O + _
  rw [← hRsum]
  dsimp only [R]
  abel

end AutomaticContinuity.HomogeneousFieldDecomposition
