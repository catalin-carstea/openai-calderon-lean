module

public import Proof.CalderonPatch.BoundaryRootDerivative

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open Matrix Filter
open scoped Topology

namespace CalderonPatch

open CalderonN (I X Mat metricPair metricPair_eq_dotProduct)

variable {m : ℕ}

/-- The principal root gives the metric norm of the raised
covector. This identifies the unit directions used in the
boundary determination argument. -/
theorem boundaryRoot_sq_eq_raised_norm {h : Mat m} (hp : h.PosDef) (ξ : X m) :
    boundaryRoot h ξ ^ 2 =
      metricPair (fun _ => h) 0 (raisedBoundaryCovector h ξ) (raisedBoundaryCovector h ξ) := by
  rw [boundaryRoot, Real.sq_sqrt (CalderonN.metricPair_nonneg_of_posDef hp.inv ξ),
    metricPair_eq_dotProduct, metricPair_eq_dotProduct]
  let ξ' : I m → ℝ := fun i => ξ i
  have hI : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hp.det_pos.ne')
  change ξ' ⬝ᵥ (h⁻¹ *ᵥ ξ') = (h⁻¹ *ᵥ ξ') ⬝ᵥ (h *ᵥ (h⁻¹ *ᵥ ξ'))
  rw [Matrix.mulVec_mulVec, hI, one_mulVec, dotProduct_comm]

/-- Every unit tangential vector is obtained by raising a covector
at principal root one. -/
theorem exists_unit_root_covector {h : Mat m} (hp : h.PosDef) {v : X m}
    (hv : metricPair (fun _ => h) 0 v v = 1) :
    ∃ ξ : X m, ξ ≠ 0 ∧ raisedBoundaryCovector h ξ = v ∧ boundaryRoot h ξ = 1 := by
  let ξ : X m := WithLp.toLp 2 (h *ᵥ fun i => v i)
  have hI : h⁻¹ * h = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hp.det_pos.ne')
  have hRaise : raisedBoundaryCovector h ξ = v := by
    apply WithLp.ofLp_injective
    change h⁻¹ *ᵥ (h *ᵥ fun i => v i) = _
    rw [Matrix.mulVec_mulVec,hI,one_mulVec]
  have hRoot := boundaryRoot_sq_eq_raised_norm hp ξ
  rw [hRaise,hv] at hRoot
  have hPos : 0 ≤ boundaryRoot h ξ := Real.sqrt_nonneg _
  have hRootOne : boundaryRoot h ξ = 1 := by nlinarith
  refine ⟨ξ,?_,hRaise,hRootOne⟩
  intro hc
  have h := hRootOne
  rw [hc] at h
  simp [boundaryRoot,metricPair] at h

/-- The highest normal jet term at the homogeneous degree
`1-k`, at an arbitrary nonzero covector. -/
def normalSymbolAtCovector (k : ℕ) (h A : Mat m) (ξ : X m) : ℝ :=
  boundaryFirstNormalSymbol h A ξ / (2 * boundaryRoot h ξ) ^ (k - 1)

theorem normalSymbolAtCovector_succ {k : ℕ} (hk : 0 < k) (h A : Mat m) (ξ : X m) :
    normalSymbolAtCovector (k + 1) h A ξ =
      normalSymbolAtCovector k h A ξ / (2 * boundaryRoot h ξ) := by
  unfold normalSymbolAtCovector
  rw [Nat.add_sub_cancel, div_div, ← pow_succ, Nat.sub_add_cancel (Nat.succ_le_of_lt hk)]

theorem normalSymbolAtCovector_at_unit (k : ℕ) {h A : Mat m} {ξ v : X m}
    (hRaise : raisedBoundaryCovector h ξ = v) (hRoot : boundaryRoot h ξ = 1) :
    normalSymbolAtCovector k h A ξ = highestNormalSymbolTerm k h A v := by
  simp only [normalSymbolAtCovector,boundaryFirstNormalSymbol,highestNormalSymbolTerm,
    hRaise,hRoot,mul_one,one_pow,div_one,div_div]

/-- Differentiating the preceding homogeneous coefficient raises
the order only in its linear application to the highest metric jet.
The derivative of the linear functional multiplies the preceding jet. -/
theorem normalSymbol_next_of_factorization_step {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {s ρ : ℝ} {C : ℝ → B →L[ℝ] ℝ} {C' : B →L[ℝ] ℝ}
    {A : ℝ → B} {A' : B} {R : ℝ → ℝ} {R' : ℝ}
    (hC : HasDerivAt C C' s) (hA : HasDerivAt A A' s) (hR : HasDerivAt R R' s)
    {bPrev : ℝ → ℝ} (hb : bPrev =ᶠ[𝓝 s] fun t => C t (A t) + R t)
    (hρ : 0 < ρ) {bNext lower : ℝ}
    (hEq : 2 * ρ * bNext = deriv bPrev s + lower) :
    bNext = C s A' / (2 * ρ) + (C' (A s) + R' + lower) / (2 * ρ) := by
  have hbD := ((hC.clm_apply hA).add hR).congr_of_eventuallyEq hb
  rw [hbD.deriv] at hEq
  apply (mul_left_cancel₀ (mul_ne_zero two_ne_zero hρ.ne'))
  rw [hEq]
  field_simp
  ring

end CalderonPatch
