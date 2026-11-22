module

public import Proof.CalderonN.ClosedHalfSpaceExtension
public import Proof.CalderonN.Chart

import Proof.CalderonN.EllipticCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

set_option maxHeartbeats 1500000 in
/-- Extend a smooth closed-ball family across the boundary. In a collar,
`log ‖x‖` is the transverse coordinate, and the angular cutoff makes the
normal jets compactly supported in the variables along the boundary. -/
theorem exists_smooth_extension_prod_closedUnitBall
    {f : P × (X dim) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (univ ×ˢ closedBall (0 : (X dim)) 1))
    {K : Set P} (hK : IsCompact K) (hSupp : ∀ p ∉ K, ∀ z : (X dim), f (p,z) = 0) :
    ∃ F : P × (X dim) → ℝ, ContDiff ℝ ∞ F ∧ EqOn F f (univ ×ˢ closedBall (0 : (X dim)) 1) := by
  let C := closedBall (0 : (X dim)) 1
  let D := ({0} : Set (X dim))ᶜ
  let S := lowerHalfSpace (P × (X dim))
  have hD : IsOpen D := isClosed_singleton.isOpen_compl
  have hSphereD : sphere (0 : (X dim)) 1 ⊆ D := by
    intro z hz
    have hn : ‖z‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hz
    exact fun h => by have he : z = 0 := h; simp [he] at hn
  obtain ⟨χ,hχ,hχK,hχD,hχOne⟩ := CalderonN.Elliptic.exists_plateau_cutoff
    hD (isCompact_sphere (0 : (X dim)) 1) hSphereD
  let A (q : (P × (X dim)) × ℝ) : P × (X dim) := (q.1.1,(Real.exp q.2 / ‖q.1.2‖) • q.1.2)
  let H (q : (P × (X dim)) × ℝ) : ℝ := χ q.1.2 * f (A q)
  have hA (q : (P × (X dim)) × ℝ) (hq : q.1.2 ∈ D) : ContDiffAt ℝ ∞ A q := by
    have h0 : q.1.2 ≠ 0 := hq
    have hn : ContDiffAt ℝ ∞ (fun r : (P × (X dim)) × ℝ => ‖r.1.2‖) q :=
      (contDiffAt_norm ℝ h0).comp q contDiffAt_fst.snd
    exact contDiffAt_fst.fst.prodMk
      (((Real.contDiff_exp.contDiffAt.comp q contDiffAt_snd).div hn (norm_ne_zero_iff.mpr h0)).smul
        contDiffAt_fst.snd)
  have hMap : MapsTo A S (univ ×ˢ C) := by
    intro q hq
    refine ⟨mem_univ _,?_⟩
    apply mem_closedBall_zero_iff.mpr
    change ‖(Real.exp q.2 / ‖q.1.2‖) • q.1.2‖ ≤ 1
    by_cases h0 : q.1.2 = 0
    · simp [h0]
    · rw [norm_smul,Real.norm_of_nonneg (div_nonneg (Real.exp_pos _).le (norm_nonneg _)),
        div_mul_cancel₀ _ (norm_ne_zero_iff.mpr h0)]
      exact Real.exp_le_one_iff.mpr hq.2
  have hH : ContDiffOn ℝ ∞ H S := by
    intro q hq
    by_cases hqD : q.1.2 ∈ D
    · have hA' := (hA q hqD).contDiffWithinAt (s := S)
      exact ((hχ.contDiffAt.comp q contDiffAt_fst.snd).contDiffWithinAt).mul
        ((hf (A q) (hMap hq)).comp q hA' hMap)
    · have hN : ∀ᶠ z : (X dim) in 𝓝 q.1.2, z ∉ tsupport χ :=
        (isClosed_tsupport χ).isOpen_compl.mem_nhds (fun hz => hqD (hχD hz))
      have he : H =ᶠ[𝓝 q] fun _ => 0 := by
        filter_upwards [(continuous_fst.snd.tendsto q).eventually hN] with r hr
        simp [H,image_eq_zero_of_notMem_tsupport hr]
      exact ((contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq he).contDiffWithinAt
  have hJetSupp (k : ℕ) : HasCompactSupport (fun q : P × (X dim) =>
      iteratedFDerivWithin ℝ k H S (q,0) (fun _ => (0,1))) := by
    apply (hK.prod hχK.isCompact).of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (hK.isClosed.prod (isClosed_tsupport χ))
    intro q hq
    by_contra hOut
    have he : H =ᶠ[𝓝 (q,0)] 0 := by
      by_cases hqK : q.1 ∈ K
      · have hqX : q.2 ∉ tsupport χ := fun h => hOut ⟨hqK,h⟩
        have hn := (isClosed_tsupport χ).isOpen_compl.mem_nhds hqX
        filter_upwards [(continuous_fst.snd.tendsto (q,0)).eventually hn] with r hr
        simp only [H,image_eq_zero_of_notMem_tsupport hr,zero_mul,Pi.zero_apply]
      · have hn := hK.isClosed.isOpen_compl.mem_nhds hqK
        filter_upwards [(continuous_fst.fst.tendsto (q,0)).eventually hn] with r hr
        simp only [H,A,hSupp _ hr,mul_zero,Pi.zero_apply]
    have hw : (q,0) ∈ S := ⟨mem_univ _,le_rfl⟩
    have hz := ((he.filter_mono nhdsWithin_le_nhds).iteratedFDerivWithin ℝ k).eq_of_nhdsWithin hw
    apply hq
    change iteratedFDerivWithin ℝ k H S (q,0) (fun _ => (0,1)) = 0
    simp only [hz,iteratedFDerivWithin_zero,Pi.zero_apply,zero_apply]
  obtain ⟨G,hG,hEq⟩ := exists_contDiff_extension_lowerHalfSpace hH hJetSupp
  let R (q : P × (X dim)) : (P × (X dim)) × ℝ := (q,Real.log ‖q.2‖)
  have hR (q : P × (X dim)) (hq : q.2 ≠ 0) : ContDiffAt ℝ ∞ (G ∘ R) q :=
    hG.contDiffAt.comp q (contDiffAt_id.prodMk
      ((Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr hq)).comp q
        ((contDiffAt_norm ℝ hq).comp q contDiffAt_snd)))
  have hEqC (q : P × (X dim)) (hq : q.2 ∈ C) (hq0 : q.2 ≠ 0) :
      G (R q) = χ q.2 * f q := by
    have hn : ‖q.2‖ ≤ 1 := mem_closedBall_zero_iff.mp hq
    have hpos : 0 < ‖q.2‖ := norm_pos_iff.mpr hq0
    have hqS : R q ∈ S := ⟨mem_univ _,Real.log_nonpos hpos.le hn⟩
    rw [hEq hqS]
    change χ q.2 * f (q.1,(Real.exp (Real.log ‖q.2‖) / ‖q.2‖) • q.2) = _
    rw [Real.exp_log hpos,div_self hpos.ne',one_smul]
  classical
  let F : P × (X dim) → ℝ := (univ ×ˢ C).piecewise f (G ∘ R)
  refine ⟨F,contDiff_iff_contDiffAt.mpr (fun q => ?_),fun q hq => piecewise_eq_of_mem _ _ _ hq⟩
  rcases lt_trichotomy ‖q.2‖ 1 with h | h | h
  · have hn : univ ×ˢ ball (0 : (X dim)) 1 ∈ 𝓝 q :=
      (isOpen_univ.prod isOpen_ball).mem_nhds ⟨mem_univ _,mem_ball_zero_iff.mpr h⟩
    have hnc : univ ×ˢ C ∈ 𝓝 q := Filter.mem_of_superset hn (prod_mono_right ball_subset_closedBall)
    apply (hf.contDiffAt hnc).congr_of_eventuallyEq
    exact Filter.mem_of_superset hnc (fun z hz => piecewise_eq_of_mem _ _ _ hz)
  · have hz : q.2 ∈ sphere (0 : (X dim)) 1 := by simpa only [mem_sphere,dist_zero_right] using h
    have h0 : q.2 ≠ 0 := hSphereD hz
    apply (hR q h0).congr_of_eventuallyEq
    have hN : ∀ᶠ z : P × (X dim) in 𝓝 q, χ z.2 = 1 :=
      (continuous_snd.tendsto q).eventually (hχOne q.2 hz)
    filter_upwards [hN,(continuous_snd.tendsto q).eventually (hD.mem_nhds (hSphereD hz))]
      with z hzχ hz0
    by_cases hzc : z.2 ∈ C
    · rw [show F z = f z from piecewise_eq_of_mem _ _ _ ⟨mem_univ _,hzc⟩]
      change f z = G (R z)
      rw [hEqC z hzc hz0,hzχ,one_mul]
    · exact piecewise_eq_of_notMem _ _ _ (fun hz => hzc hz.2)
  · have hzC : q.2 ∉ C := fun hz => h.not_ge (mem_closedBall_zero_iff.mp hz)
    have h0 : q.2 ≠ 0 := fun hz => hzC (by simp [hz,C])
    apply (hR q h0).congr_of_eventuallyEq
    filter_upwards [(continuous_snd.tendsto q).eventually (isClosed_closedBall.isOpen_compl.mem_nhds hzC)]
      with z hz
    exact piecewise_eq_of_notMem _ _ _ (fun h => hz h.2)

end CalderonN
