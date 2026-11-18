import Proof.PhysicalPotentialCoreLp
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

theorem PhysicalPrincipalData.potentialCoreOperators_green
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (U V : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (h0U : ∀ x ∉ S,U x=0) (h0V : ∀ x ∉ S,V x=0) :
    IntegrableOn (fun y => metricDensity d.γ y*
      ⟪sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (U y),P.potentialQuadraticCoreSection W V y⟫_ℝ) Y ∧
    IntegrableOn (fun y => metricDensity d.γ y*
      ⟪sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (V y),P.potentialQuadraticAdjointCoreSection W U y⟫_ℝ) Y ∧
    (∫ y in Y,metricDensity d.γ y*
      ⟪sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (U y),P.potentialQuadraticCoreSection W V y⟫_ℝ)=
      (∫ y in Y,metricDensity d.γ y*
        ⟪sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (V y),P.potentialQuadraticAdjointCoreSection W U y⟫_ℝ) := by
  let U0 := fun y => sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (U y)
  let V0 := fun y => sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (V y)
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hUlp : MemLp U 2 (volume.restrict Y) :=
    hU.continuous.memLp_of_hasCompactSupport (HasCompactSupport.intro hS h0U)
  have hVlp : MemLp V 2 (volume.restrict Y) :=
    hV.continuous.memLp_of_hasCompactSupport (HasCompactSupport.intro hS h0V)
  have hU0lp := (sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num)).comp_memLp' hUlp
  have hV0lp := (sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num)).comp_memLp' hVlp
  refine ⟨integrableOn_local_weighted_inner_of_memLp hY.measurableSet hS hSY U0 _ hU0lp
    (P.potentialQuadraticCoreSection_memLp hY hSub hd hK W hCK V hV S hS hSY h0V 2)
    (fun y _ hs => by simp only [U0,h0U y hs,map_zero]) _ (hg.contDiffOn_density hK).continuousOn,
    integrableOn_local_weighted_inner_of_memLp hY.measurableSet hS hSY V0 _ hV0lp
      (P.potentialQuadraticAdjointCoreSection_memLp hY hSub hd hK W hCG hCK U hU S hS hSY h0U 2)
      (fun y _ hs => by simp only [V0,h0V y hs,map_zero]) _ (hg.contDiffOn_density hK).continuousOn,?_⟩
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
  apply congrArg (fun z => metricDensity d.γ y*z)
  simp only [PhysicalPrincipalData.potentialQuadraticCoreSection,
    PhysicalPrincipalData.potentialQuadraticAdjointCoreSection,dite_eq_left hy]
  exact (real_inner_comm _ _).trans (P.potentialQuadraticCoreL_pair hy (W y hy) (V y) (U y))

end ShrinkingSpheres
