module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

import Proof.ReleasedAnalysis.TauCeti.Analysis.Calculus.BumpFunction.Cutoff
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

public section
noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Topology

namespace CalderonPatch

variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)

private theorem continuous_square_mul_of_tsupport {V : Set Y} (hV : IsOpen V)
    {q a : Y → ℝ} (hq : ContinuousOn q V) (ha : Continuous a) (hA : tsupport a ⊆ V) :
    Continuous (fun x => a x ^ 2 * q x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ V
  · exact (ha.continuousAt.pow 2).mul (hq.continuousAt (hV.mem_nhds hx))
  · apply (show ContinuousAt (fun _ : Y => (0 : ℝ)) x from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds (show x ∉ tsupport a from
      fun hxA => hx (hA hxA))] with y hy
    simp only [image_eq_zero_of_notMem_tsupport hy,zero_pow (by decide : (2 : ℕ) ≠ 0),zero_mul]

/-- Real squared test amplitudes determine a continuous coefficient
pointwise on the open portion of the measured face. -/
theorem eqOn_of_squared_test_pairings {V S : Set Y} (hV : IsOpen V) (hVS : V ⊆ S)
    {A B : Y → ℝ} (hA : ContinuousOn A V) (hB : ContinuousOn B V)
    (hEq : ∀ a : Y → ℝ, ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ V →
      (∫ x in S, a x ^ 2 * A x) = ∫ x in S, a x ^ 2 * B x) :
    EqOn A B V := by
  have hLe {P Q : Y → ℝ} (hp : ContinuousOn P V) (hq : ContinuousOn Q V)
      (hTest : ∀ a : Y → ℝ, ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ V →
        (∫ x in S, a x ^ 2 * P x) = ∫ x in S, a x ^ 2 * Q x)
      {x : Y} (hx : x ∈ V) : P x ≤ Q x := by
    by_contra! hlt
    let O := V ∩ {z | Q z < P z}
    have hO : IsOpen O := by
      have he : O = V ∩ (P - Q) ⁻¹' Ioi (0 : ℝ) := by
        ext z
        simp [O,sub_pos]
      rw [he]
      exact (hp.sub hq).isOpen_inter_preimage hV isOpen_Ioi
    have hKV : ({x} : Set Y) ⊆ O := singleton_subset_iff.mpr ⟨hx,hlt⟩
    obtain ⟨a,ha,_,ha₁,hac,has⟩ := isCompact_singleton.exists_contDiff_cutoff hO hKV
    have hAV := has.trans inter_subset_left
    have haX : a x = 1 := mem_singleton_iff.mp (show x ∈ a ⁻¹' {1} from interior_subset (ha₁ (mem_singleton x)))
    let F (z : Y) := a z ^ 2 * (P z - Q z)
    have hF := continuous_square_mul_of_tsupport hV (hp.sub hq) ha.continuous hAV
    have hCpt (g : Y → ℝ) : HasCompactSupport (fun z => a z ^ 2 * g z) :=
      hac.mono' (fun _ hz => subset_tsupport _ (fun h => hz (by simp [h])))
    have hpI : Integrable (fun z => a z ^ 2 * P z) volume := (continuous_square_mul_of_tsupport hV hp ha.continuous hAV).integrable_of_hasCompactSupport (hCpt P)
    have hqI : Integrable (fun z => a z ^ 2 * Q z) volume := (continuous_square_mul_of_tsupport hV hq ha.continuous hAV).integrable_of_hasCompactSupport (hCpt Q)
    have hI : Integrable F volume := hF.integrable_of_hasCompactSupport (hCpt (P-Q))
    have hF₀ : 0 ≤ F := by
      intro z
      by_cases hz : z ∈ tsupport a
      · exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (has hz).2.le)
      · simp [F,image_eq_zero_of_notMem_tsupport hz]
    have hFx : F x ≠ 0 := by simp [F,haX,ne_of_gt (sub_pos.mpr hlt)]
    have hPos := integral_pos_of_integrable_nonneg_nonzero hF hI hF₀ hFx
    have hZero (g : Y → ℝ) (z : Y) (hz : z ∉ S) : a z ^ 2 * g z = 0 := by
      have h := image_eq_zero_of_notMem_tsupport (fun hs => hz (hVS (hAV hs)))
      simp [h]
    have hE := hTest a ha hac hAV
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hZero P),
      setIntegral_eq_integral_of_forall_compl_eq_zero (hZero Q)] at hE
    have hZ : (∫ z, F z) = 0 := by
      simp only [F,mul_sub,integral_sub hpI hqI,hE,sub_self]
    exact (ne_of_gt hPos) hZ
  exact fun x hx => le_antisymm (hLe hA hB hEq hx)
    (hLe hB hA (fun a ha hC hS => (hEq a ha hC hS).symm) hx)

end CalderonPatch
