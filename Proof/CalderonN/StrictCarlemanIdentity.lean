module

public import Proof.CalderonN.CarlemanIdentity
public import Proof.CalderonN.CarlemanWeight
import Mathlib.Tactic

/-! Adapted from `Calderon/MixedKernelConstruction/MixedKernelConstructionC3SupportV015.lean`
at d6704c49395a38eb07e0249afeb8ea83d67971cc. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric Filter
open scoped ContDiff Topology

namespace CalderonN.Carleman.Strict

variable {d : ℕ}

section SavedSquares
variable {a : Fin d → Fin d → (CalderonN.X d) → ℝ} {X : Fin d → (CalderonN.X d) → ℝ} {q θ v : (CalderonN.X d) → ℝ}

/-- T1: the exact integrated commutator identity RETAINING the squares, for every real `κ`
and every (signed) smooth auxiliary `θ`:
`∫(S+B)² = ∫Qfun + ∫(B² + (1-κ)S² + κ(S+θv)²)`. -/
theorem integral_sq_saved_eq (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hX : ∀ j, ContDiff ℝ ∞ (X j)) (hq : ContDiff ℝ ∞ q) (hθ : ContDiff ℝ ∞ θ)
    (hv : ContDiff ℝ ∞ v) (hsymm : ∀ i k, a i k = a k i) (hvc : HasCompactSupport v) (κ : ℝ) :
    Integrable (Qfun a X q θ κ v) ∧
    Integrable (fun x => Bop X v x ^ 2 + (1 - κ) * Sop a q v x ^ 2 +
        κ * (Sop a q v x + θ x * v x) ^ 2) ∧
    ∫ x, (Sop a q v x + Bop X v x) ^ 2 = (∫ x, Qfun a X q θ κ v x) +
      ∫ x, (Bop X v x ^ 2 + (1 - κ) * Sop a q v x ^ 2 +
        κ * (Sop a q v x + θ x * v x) ^ 2) := by
  set G : Fin d → (CalderonN.X d) → ℝ := fun i x => F1 a X q v i x + κ * F2 a θ v i x with hG
  have hGs : ∀ i, ContDiff ℝ ∞ (G i) := fun i =>
    (contDiff_F1 ha hX hq hθ hv i).add (contDiff_const.mul (contDiff_F2 ha hX hq hθ hv i))
  have hGc : ∀ i, HasCompactSupport (G i) := hasCompactSupport_F ha hX hq hθ hv hvc κ
  set H : (CalderonN.X d) → ℝ := fun x => 2 * Sop a q v x * Bop X v x - 2 * κ * θ x * v x * Sop a q v x -
    κ * θ x ^ 2 * (v x * v x) with hH
  have hHQ : ∀ x, H x = Qfun a X q θ κ v x + ∑ i, pd i (G i) x := by
    intro x
    have e1 := identity1 ha hsymm hX hq hv x
    have e2 := identity2 ha hsymm hq hθ hv x
    have hpdG : ∀ i, pd i (G i) x = pd i (F1 a X q v i) x + κ * pd i (F2 a θ v i) x := by
      intro i
      simp only [hG]
      rw [pd_add (contDiff_F1 ha hX hq hθ hv i)
        (contDiff_const.mul (contDiff_F2 ha hX hq hθ hv i)),
        pd_const_mul _ (contDiff_F2 ha hX hq hθ hv i)]
    simp only [hpdG, Finset.sum_add_distrib, ← Finset.mul_sum, hH, Qfun]
    linear_combination e1 + κ * e2
  have hS := contDiff_Sop (q := q) ha hX hq hθ hv
  have hB := contDiff_Bop (a := a) (q := q) ha hX hq hθ hv
  have hHi : Integrable H := by
    apply integrable_of_vanish _ hvc
    · intro x hx
      simp [hH, Sop_vanish ha hX hq hθ hv hx, Bop_vanish ha hX hq hθ hv hx,
        image_eq_zero_of_notMem_tsupport hx]
    · simp only [hH]; fun_prop
  have hRi : Integrable (fun x => Bop X v x ^ 2 + (1 - κ) * Sop a q v x ^ 2 +
      κ * (Sop a q v x + θ x * v x) ^ 2) := by
    apply integrable_of_vanish _ hvc
    · intro x hx
      simp [Sop_vanish ha hX hq hθ hv hx, Bop_vanish ha hX hq hθ hv hx,
        image_eq_zero_of_notMem_tsupport hx]
    · fun_prop
  have hdi : ∀ i, Integrable (pd i (G i)) := fun i =>
    integrable_of_contDiff_hasCompactSupport (contDiff_pd (hGs i)) (hasCompactSupport_pd (hGc i))
  have hQeq : Qfun a X q θ κ v = fun x => H x - ∑ i, pd i (G i) x := by
    funext x; rw [hHQ x]; ring
  have hQi : Integrable (Qfun a X q θ κ v) := by
    rw [hQeq]; exact hHi.sub (integrable_finsetSum _ fun i _ => hdi i)
  have hint : ∫ x, H x = ∫ x, Qfun a X q θ κ v x := by
    have : ∫ x, ∑ i, pd i (G i) x = 0 := by
      rw [integral_finsetSum _ fun i _ => hdi i]
      simp [integral_pd_eq_zero (hGs _) (hGc _)]
    rw [hQeq, integral_sub hHi (integrable_finsetSum _ fun i _ => hdi i), this, sub_zero]
  refine ⟨hQi, hRi, ?_⟩
  have hpt : (fun x => (Sop a q v x + Bop X v x) ^ 2) = fun x => H x +
      (Bop X v x ^ 2 + (1 - κ) * Sop a q v x ^ 2 + κ * (Sop a q v x + θ x * v x) ^ 2) := by
    funext x; simp only [hH]; ring
  rw [hpt, integral_add hHi hRi, hint]

/-- T1 (retained `B²`): for `0 ≤ κ ≤ 1`, `∫(Qfun + B²) ≤ ∫(S+B)²`. -/
theorem integral_Qfun_add_Bop_sq_le (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hX : ∀ j, ContDiff ℝ ∞ (X j)) (hq : ContDiff ℝ ∞ q) (hθ : ContDiff ℝ ∞ θ)
    (hv : ContDiff ℝ ∞ v) (hsymm : ∀ i k, a i k = a k i) (hvc : HasCompactSupport v)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    Integrable (fun x => Qfun a X q θ κ v x + Bop X v x ^ 2) ∧
    ∫ x, (Qfun a X q θ κ v x + Bop X v x ^ 2) ≤ ∫ x, (Sop a q v x + Bop X v x) ^ 2 := by
  obtain ⟨hQi, hRi, heq⟩ := integral_sq_saved_eq ha hX hq hθ hv hsymm hvc κ
  have hB := contDiff_Bop (a := a) (q := q) ha hX hq hθ hv
  have hBi : Integrable (fun x => Bop X v x ^ 2) := by
    apply integrable_of_vanish _ hvc
    · intro x hx; simp [Bop_vanish ha hX hq hθ hv hx]
    · fun_prop
  refine ⟨hQi.add hBi, ?_⟩
  rw [heq, integral_add hQi hBi]
  have hmono : ∫ x, Bop X v x ^ 2 ≤ ∫ x, (Bop X v x ^ 2 + (1 - κ) * Sop a q v x ^ 2 +
      κ * (Sop a q v x + θ x * v x) ^ 2) := by
    apply integral_mono hBi hRi
    intro x
    have h1 : 0 ≤ (1 - κ) * Sop a q v x ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have h2 : 0 ≤ κ * (Sop a q v x + θ x * v x) ^ 2 := mul_nonneg hκ0 (sq_nonneg _)
    show Bop X v x ^ 2 ≤ Bop X v x ^ 2 + (1 - κ) * Sop a q v x ^ 2 +
      κ * (Sop a q v x + θ x * v x) ^ 2
    linarith
  linarith

end SavedSquares

end CalderonN.Carleman.Strict
