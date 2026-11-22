module

public import Proof.CalderonN.Coercivity
import Proof.CalderonN.SobolevDilation

import Proof.CalderonN.EllipticCalculus
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic

public section

noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff ENNReal Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]



private theorem exists_smooth_compact_extension
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K U : Set (X dim)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : (X dim) → F} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ g : (X dim) → F, ContDiff ℝ ∞ g ∧ ∀ x ∈ K, g =ᶠ[𝓝 x] f := by
  obtain ⟨χ,hχ,_,hχU,hχK⟩ := CalderonN.Elliptic.exists_plateau_cutoff hU hK hKU
  let g (x : (X dim)) := χ x • f x
  refine ⟨g,contDiff_iff_contDiffAt.mpr (fun x => ?_),?_⟩
  · by_cases hx : x ∈ U
    · exact hχ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hx))
    · have hn : x ∈ (tsupport χ)ᶜ := fun h => hx (hχU h)
      apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hn] with z hz
      simp only [g,image_eq_zero_of_notMem_tsupport hz,zero_smul]
  · intro x hx
    exact (hχK x hx).mono (fun _ h => by simp [g,h])

theorem volume_restrict_closedUnitBall_eq :
    volume.restrict (closedBall (0 : (X dim)) 1) = volume.restrict (ball (0 : (X dim)) 1) := by
  apply Measure.restrict_congr_set
  have hμ : ∀ᵐ x ∂(volume : Measure (X dim)), x ∉ sphere (0 : (X dim)) 1 := by
    rw [ae_iff,show {x | ¬ x ∉ sphere (0 : (X dim)) 1} = sphere (0 : (X dim)) 1 by ext; simp,
      Measure.addHaar_sphere volume]
  filter_upwards [hμ] with x hx
  apply propext
  change x ∈ closedBall (0 : (X dim)) 1 ↔ x ∈ ball (0 : (X dim)) 1
  change dist x 0 ≠ 1 at hx
  exact ⟨fun ht => lt_of_le_of_ne (mem_closedBall.mp ht) hx,fun ht => ball_subset_closedBall ht⟩

/-- Inward dilations give genuine ambient smooth functions. On the
closed unit ball each jet is exactly the scaled interior jet. -/
theorem exists_smooth_inwardDilations
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : (X dim) → F} (hf : ContDiffOn ℝ ∞ f (ball (0 : (X dim)) 1))
    (r : ℕ → ℝ) (hr : ∀ n, r n ∈ Ioo (0 : ℝ) 1) :
    ∃ fₙ : ℕ → (X dim) → F, (∀ n, ContDiff ℝ ∞ (fₙ n)) ∧
      ∀ n k x, x ∈ closedBall (0 : (X dim)) 1 →
        iteratedFDeriv ℝ k (fₙ n) x = (r n)^k • iteratedFDeriv ℝ k f (r n • x) := by
  have hex (n : ℕ) : ∃ g : (X dim) → F, ContDiff ℝ ∞ g ∧
      ∀ x ∈ closedBall (0 : (X dim)) (r n), g =ᶠ[𝓝 x] f :=
    exists_smooth_compact_extension (isCompact_closedBall _ _) isOpen_ball
      (closedBall_subset_ball (hr n).2) hf
  choose g hG hEq using hex
  let L (n : ℕ) : (X dim) →L[ℝ] (X dim) := r n • ContinuousLinearMap.id ℝ (X dim)
  refine ⟨fun n => g n ∘ L n,fun n => (hG n).comp (L n).contDiff,?_⟩
  intro n k x hx
  have hN : r n • x ∈ closedBall (0 : (X dim)) (r n) := by
    rw [mem_closedBall_zero_iff,norm_smul,Real.norm_of_nonneg (hr n).1.le]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) (hr n).1.le).trans_eq (mul_one _)
  have he : g n =ᶠ[𝓝 (r n • x)] f := hEq n _ hN
  have hJ : iteratedFDeriv ℝ k (g n) (r n • x) = iteratedFDeriv ℝ k f (r n • x) := by
    rw [← iteratedFDerivWithin_univ,← iteratedFDerivWithin_univ]
    exact (he.filter_mono nhdsWithin_le_nhds).iteratedFDerivWithin_eq he.eq_of_nhds k
  rw [(L n).iteratedFDeriv_comp_right (hG n) x (by simp)]
  change (iteratedFDeriv ℝ k (g n) (r n • x)).compContinuousLinearMap (fun _ => L n) = _
  rw [hJ]
  ext v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,smul_apply]
  simpa only [L, smul_apply,ContinuousLinearMap.id_apply,Finset.prod_const,Finset.card_univ,
    Fintype.card_fin] using (iteratedFDeriv ℝ k f (r n • x)).map_smul_univ (fun _ => r n) v

set_option maxHeartbeats 1000000 in
/-- The scaled inward copies converge in (L^2) for any bulk jet. -/
theorem tendsto_eLpNorm_scaledInward_sub
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : (X dim) → F} (hu : MemLp u 2 (volume.restrict (ball (0 : (X dim)) 1)))
    {r : ℕ → ℝ} (hr : ∀ n, r n ∈ Ioo (0 : ℝ) 1) (hR : Tendsto r atTop (𝓝 1))
    (k : ℕ) :
    Tendsto (fun n => eLpNorm (fun z => (r n)^k • u (r n • z) - u z) 2
      (volume.restrict (ball (0 : (X dim)) 1))) atTop (𝓝 0) := by
  let B := ball (0 : (X dim)) 1
  let μ := (volume : Measure (X dim)).restrict B
  let U := B.indicator u
  have hU : MemLp U 2 volume := (memLp_indicator_iff_restrict measurableSet_ball.nullMeasurableSet).mpr hu
  have hL := tendsto_eLpNorm_comp_smul_sub (by norm_num : (2:ℝ≥0∞) ≠ ⊤) hU hR
  have hCoef : Tendsto (fun n => ENNReal.ofReal ‖(r n)^k - 1‖) atTop (𝓝 0) := by
    have hZ : Tendsto (fun n => ‖(r n)^k-1‖) atTop (𝓝 0) := by
      simpa using ((hR.pow k).sub_const 1).norm
    simpa only [Function.comp_def,ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hZ
  have hConst : Tendsto (fun n => ENNReal.ofReal ‖(r n)^k-1‖ * eLpNorm u 2 μ) atTop (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const (b := eLpNorm u 2 μ) hCoef (Or.inr hu.eLpNorm_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using hL.add hConst)
    (Eventually.of_forall (fun _ => zero_le)) (Eventually.of_forall fun n => ?_)
  have hn : (r n)^k ≤ 1 := pow_le_one₀ (hr n).1.le (hr n).2.le
  have hQ : ∀ᵐ z ∂μ, u (r n • z) - u z = U (r n • z) - U z := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hzr : r n • z ∈ B := by
      have hz' := mem_ball_zero_iff.mp hz
      rw [mem_ball_zero_iff,norm_smul,Real.norm_of_nonneg (hr n).1.le]
      exact (mul_lt_mul_of_pos_left hz' (hr n).1).trans_le (by simpa using (hr n).2.le)
    simp only [U,indicator_of_mem hzr,indicator_of_mem hz]
  have hA : (fun z => (r n)^k • u (r n • z) - u z) =
      (r n)^k • (fun z => u (r n • z) - u z) + ((r n)^k-1) • u := by
    funext z
    change (r n)^k • u (r n • z) - u z =
      (r n)^k • (u (r n • z)-u z) + ((r n)^k-1) • u z
    rw [smul_sub,sub_smul,one_smul]
    abel
  rw [hA]
  refine (eLpNorm_add_le (by norm_num : (1:ℝ≥0∞) ≤ 2)).trans ?_
  simp only [eLpNorm_const_smul]
  rw [← ofReal_norm ((r n)^k-1)]
  refine add_le_add ?_ le_rfl
  have hS : ‖(r n)^k‖ₑ ≤ 1 := by
    rw [← ofReal_norm,Real.norm_of_nonneg (pow_nonneg (hr n).1.le _),← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hn
  calc
    _ ≤ eLpNorm (fun z => u (r n • z)-u z) 2 μ := by
      exact (show _ ≤ (1:ℝ≥0∞) * _ by gcongr).trans_eq (one_mul _)
    _ = eLpNorm (fun z => U (r n • z)-U z) 2 μ := eLpNorm_congr_ae hQ
    _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self

end CalderonN
