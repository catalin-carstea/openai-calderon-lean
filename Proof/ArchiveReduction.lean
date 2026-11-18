import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/- Proof bodies from the selected ZIP, Proposition53/GeneralReduction.lean.
   Its Calderón import was narrowed to the mathlib modules used here. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace

namespace OAI.AnisotropicCalderon.Proposition53GeneralReduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def commutator (A B : E →ₗ[ℝ] E) : E →ₗ[ℝ] E := A * B - B * A

def errorOperator (T Td U Ud Z Zd : E →ₗ[ℝ] E) : E →ₗ[ℝ] E :=
  (2 : ℝ) • commutator Td U + (2 : ℝ) • commutator Ud T + commutator Ud U -
    (2 : ℝ) • (U * Z + Zd * Ud)

theorem squared_norm_comparison (T Td Tf U Ud Z Zd : E →ₗ[ℝ] E)
    (hT : ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, Td y⟫_ℝ)
    (hU : ∀ x y, ⟪U x, y⟫_ℝ = ⟪x, Ud y⟫_ℝ)
    (hZ : ∀ x y, ⟪Z x, y⟫_ℝ = ⟪x, Zd y⟫_ℝ)
    (hTf : Tf = Td + Z) (v : E) :
    ‖(2 : ℝ) • T v + U v‖^2 - ‖(2 : ℝ) • Tf v + Ud v‖^2 =
      4 * (‖T v‖^2 - ‖Tf v‖^2) + ⟪errorOperator T Td U Ud Z Zd v, v⟫_ℝ := by
  have hTd (x y : E) : ⟪Td x, y⟫_ℝ = ⟪x, T y⟫_ℝ := by
    rw [real_inner_comm, ← hT, real_inner_comm]
  have hUd (x y : E) : ⟪Ud x, y⟫_ℝ = ⟪x, U y⟫_ℝ := by
    rw [real_inner_comm, ← hU, real_inner_comm]
  have hZd (x y : E) : ⟪Zd x, y⟫_ℝ = ⟪x, Z y⟫_ℝ := by
    rw [real_inner_comm, ← hZ, real_inner_comm]
  have h1 : ⟪Td (U v), v⟫_ℝ = ⟪U v, T v⟫_ℝ := hTd _ _
  have h2 : ⟪U (Td v), v⟫_ℝ = ⟪Td v, Ud v⟫_ℝ := hU _ _
  have h3 : ⟪Ud (T v), v⟫_ℝ = ⟪T v, U v⟫_ℝ := hUd _ _
  have h4 : ⟪T (Ud v), v⟫_ℝ = ⟪Ud v, Td v⟫_ℝ := hT _ _
  have h5 : ⟪Ud (U v), v⟫_ℝ = ‖U v‖^2 := by rw [hUd, real_inner_self_eq_norm_sq]
  have h6 : ⟪U (Ud v), v⟫_ℝ = ‖Ud v‖^2 := by rw [hU, real_inner_self_eq_norm_sq]
  have h7 : ⟪U (Z v), v⟫_ℝ = ⟪Z v, Ud v⟫_ℝ := hU _ _
  have h8 : ⟪Zd (Ud v), v⟫_ℝ = ⟪Ud v, Z v⟫_ℝ := hZd _ _
  simp only [errorOperator, commutator, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.mul_apply, inner_sub_left, inner_add_left,
    real_inner_smul_left, h1, h2, h3, h4, h5, h6, h7, h8]
  have hNorm (a b : E) : ‖(2 : ℝ) • a + b‖^2 =
      4 * ‖a‖^2 + 4 * ⟪a, b⟫_ℝ + ‖b‖^2 := by
    rw [norm_add_sq_real, norm_smul, real_inner_smul_left]
    norm_num
    ring
  rw [hNorm, hNorm]
  have hPair : ⟪Tf v, Ud v⟫_ℝ = ⟪Td v, Ud v⟫_ℝ + ⟪Z v, Ud v⟫_ℝ := by
    rw [hTf]
    simp only [LinearMap.add_apply, inner_add_left]
  have hUT := real_inner_comm (U v) (T v)
  have hTdUd := real_inner_comm (Td v) (Ud v)
  have hZU := real_inner_comm (Z v) (Ud v)
  nlinarith

theorem coercivity_of_estimates (N c CE CJ beta eps : ℝ) (hc : 0 < c)
    (hCE : 0 ≤ CE) (_hCJ : 0 ≤ CJ) (hN : 0 ≤ N)
    (hbeta : max 1 (2 * CJ / Real.sqrt c) ≤ beta)
    (heps : 0 ≤ eps) (hepsSmall : eps ≤ c / (CE + 1))
    (T Tf U Ud J P : E) (err : ℝ)
    (hRaising : c * N^2 ≤ ‖T‖^2 - ‖Tf‖^2)
    (hComparison : ‖(2 : ℝ) • T + U‖^2 - ‖(2 : ℝ) • Tf + Ud‖^2 =
      4 * (‖T‖^2 - ‖Tf‖^2) + err)
    (hError : |err| ≤ CE * eps * N^2)
    (hJ : ‖J‖ ≤ CJ / beta * N)
    (hP : P = (2 : ℝ) • T + U + J) :
    N ≤ (2 / Real.sqrt c) * ‖P‖ := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hCE1 : 0 < CE + 1 := by linarith
  have hsmall : CE * eps ≤ c := by
    have hh := (le_div_iff₀ hCE1).mp hepsSmall
    nlinarith
  have herr : -c * N^2 ≤ err := by
    have hh := (abs_le.mp hError).1
    have hm := mul_le_mul_of_nonneg_right hsmall (sq_nonneg N)
    linarith
  have hPrincipal : c * N^2 ≤ ‖(2 : ℝ) • T + U‖^2 := by
    nlinarith [sq_nonneg ‖(2 : ℝ) • Tf + Ud‖]
  have hRoot : Real.sqrt c * N ≤ ‖(2 : ℝ) • T + U‖ := by
    apply (sq_le_sq₀ (mul_nonneg hs.le hN) (norm_nonneg _)).mp
    nlinarith [Real.sq_sqrt hc.le]
  have hb1 : 1 ≤ beta := (le_max_left _ _).trans hbeta
  have hb : 0 < beta := by linarith
  have hbFloor : 2 * CJ ≤ beta * Real.sqrt c :=
    (div_le_iff₀ hs).mp ((le_max_right _ _).trans hbeta)
  have hRatio : CJ / beta ≤ Real.sqrt c / 2 := by
    apply (div_le_iff₀ hb).mpr
    linarith
  have hJsmall : ‖J‖ ≤ Real.sqrt c / 2 * N :=
    hJ.trans (mul_le_mul_of_nonneg_right hRatio hN)
  have hTriangle : ‖(2 : ℝ) • T + U‖ ≤ ‖P‖ + ‖J‖ := by
    have h : (2 : ℝ) • T + U = P - J := by rw [hP]; abel
    rw [h]
    exact norm_sub_le _ _
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hs).mpr
  nlinarith

theorem uniform_coercivity_of_analytic_estimates
    {Parameter Test : Type*} (good : Parameter → Test → Prop)
    (N : Parameter → Test → ℝ) (T Tf U Ud J P : Parameter → Test → E)
    (err : Parameter → Test → ℝ) (beta eps : Parameter → ℝ)
    (c CE CJ : ℝ) (hc : 0 < c) (hCE : 0 ≤ CE) (hCJ : 0 ≤ CJ)
    (hN : ∀ a v, good a v → 0 ≤ N a v)
    (hRaising : ∀ a v, good a v → c * (N a v)^2 ≤ ‖T a v‖^2 - ‖Tf a v‖^2)
    (hComparison : ∀ a v, good a v →
      ‖(2 : ℝ) • T a v + U a v‖^2 - ‖(2 : ℝ) • Tf a v + Ud a v‖^2 =
        4 * (‖T a v‖^2 - ‖Tf a v‖^2) + err a v)
    (hError : ∀ a v, good a v → |err a v| ≤ CE * eps a * (N a v)^2)
    (hJ : ∀ a v, good a v → ‖J a v‖ ≤ CJ / beta a * N a v)
    (hP : ∀ a v, good a v → P a v = (2 : ℝ) • T a v + U a v + J a v) :
    ∃ beta0 eps0 C : ℝ, 0 < beta0 ∧ 0 < eps0 ∧ 0 < C ∧
      ∀ a, beta0 ≤ beta a → 0 ≤ eps a → eps a ≤ eps0 →
        ∀ v, good a v → N a v ≤ C * ‖P a v‖ := by
  refine ⟨max 1 (2 * CJ / Real.sqrt c), c / (CE + 1), 2 / Real.sqrt c,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), div_pos hc (by linarith),
    div_pos (by norm_num) (Real.sqrt_pos.mpr hc), ?_⟩
  intro a hb he heSmall v hv
  exact coercivity_of_estimates (N a v) c CE CJ (beta a) (eps a) hc hCE hCJ
    (hN a v hv) hb he heSmall (T a v) (Tf a v) (U a v) (Ud a v) (J a v) (P a v)
    (err a v) (hRaising a v hv) (hComparison a v hv) (hError a v hv) (hJ a v hv) (hP a v hv)

end OAI.AnisotropicCalderon.Proposition53GeneralReduction
