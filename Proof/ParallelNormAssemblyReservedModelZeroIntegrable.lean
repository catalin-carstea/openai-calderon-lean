import Proof.ParallelNormAssemblyReservedModelCoreSplit
import Proof.CompactSupportedLpWeightedSquare

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

def modelZeroForwardCoarseAtL (d : Data) (y : X) : SphereSobolev 2 →L[ℝ] SphereSobolev 0 :=
  ∑ i : I,modelLogRadiusCoefficient d i y • (flatRaisingSobolevL 1 i).comp (sphereSobolevShiftedDegreeL 2)

def modelZeroAdjointCoarseAtL (d : Data) (y : X) : SphereSobolev 2 →L[ℝ] SphereSobolev 0 :=
  ∑ i : I,modelLogRadiusCoefficient d i y • (flatLoweringSobolevL 1 i).comp
    (sphereSobolevShiftedDegreeL 2-sphereSobolevInclusionL 2 1 (by norm_num))

/-- Qualitative integrability of the exact angular-zero pair is proved
using its actual coarse realization, BEFORE splitting its integral. -/
theorem model_potential_zero_density_integrable {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε CF CT CG CK : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (hU0 : ∀ x ∉ S,U x=0) :
    IntegrableOn (modelPotentialZeroCoreDensity P W U) Y := by
  let U2 := fiveHalfToTwoSection U
  let F := fun x => modelZeroForwardCoarseAtL d x (U2 x)
  let A := fun x => modelZeroAdjointCoarseAtL d x (U2 x)
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hlog := hd.2.2.2.2.1.1.log (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
  have hEll (i : I) : ContDiffOn ℝ ∞ (modelLogRadiusCoefficient d i) Y :=
    (hlog.fderiv_of_isOpen hY (by simp)).clm_apply (he i)
  have hFS : ContDiffOn ℝ ∞ (modelZeroForwardCoarseAtL d) Y :=
    ContDiffOn.sum (fun i _ => (hEll i).smul contDiffOn_const)
  have hAS : ContDiffOn ℝ ∞ (modelZeroAdjointCoarseAtL d) Y :=
    ContDiffOn.sum (fun i _ => (hEll i).smul contDiffOn_const)
  have hU2 : ContDiff ℝ ∞ U2 := (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num)).contDiff.comp hU
  have hU20 (x : X) (hx : x ∉ S) : U2 x=0 := by simp only [U2,fiveHalfToTwoSection,hU0 x hx,map_zero]
  have hF : ContDiff ℝ ∞ F := OperatorForms.contDiff_supported_operator_apply U2 _ S hS.isClosed hU2 hU20
    (fun x hx => hFS.contDiffAt (hY.mem_nhds (hSY hx)))
  have hA : ContDiff ℝ ∞ A := OperatorForms.contDiff_supported_operator_apply U2 _ S hS.isClosed hU2 hU20
    (fun x hx => hAS.contDiffAt (hY.mem_nhds (hSY hx)))
  have hF0 (x : X) (hx : x ∉ S) : F x=0 := by simp only [F,hU20 x hx,map_zero]
  have hA0 (x : X) (hx : x ∉ S) : A x=0 := by simp only [A,hU20 x hx,map_zero]
  have hFlp : MemLp F 2 (volume.restrict Y) :=
    (hF.continuous.memLp_of_hasCompactSupport (HasCompactSupport.intro hS hF0)).restrict _
  have hAlp : MemLp A 2 (volume.restrict Y) :=
    (hA.continuous.memLp_of_hasCompactSupport (HasCompactSupport.intro hS hA0)).restrict _
  have hPF := P.potentialQuadraticCoreSection_memLp hY hSub hd hK W hCK U hU S hS hSY hU0 2
  have hPA := P.potentialQuadraticAdjointCoreSection_memLp hY hSub hd hK W hCG hCK U hU S hS hSY hU0 2
  have hIF := integrableOn_local_weighted_inner_of_memLp hY.measurableSet hS hSY F _ hFlp hPF
    (fun x _ hx => hF0 x hx) (metricDensity d.γ) (hg.contDiffOn_density hK).continuousOn
  have hIA := integrableOn_local_weighted_inner_of_memLp hY.measurableSet hS hSY A _ hAlp hPA
    (fun x _ hx => hA0 x hx) (metricDensity d.γ) (hg.contDiffOn_density hK).continuousOn
  have hEq : (fun x => 4*(metricDensity d.γ x*⟪F x,P.potentialQuadraticCoreSection W U x⟫_ℝ-
      metricDensity d.γ x*⟪A x,P.potentialQuadraticAdjointCoreSection W U x⟫_ℝ))=ᵐ[volume.restrict Y]
      modelPotentialZeroCoreDensity P W U := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with x hx
    have hFActual := model_zero_forward_actual P hx (W x hx) (U x)
    have hAActual := model_zero_adjoint_actual P hx (W x hx) Q hQ (U x)
    have hFValue : modelZeroForwardCoreValue P (W x hx) (U x)=F x := by
      simpa only [F,modelZeroForwardCoarseAtL,_root_.sum_apply,_root_.smul_apply,
        ContinuousLinearMap.comp_apply,U2,fiveHalfToTwoSection] using hFActual
    have hAValue : modelZeroAdjointCoreValue P (W x hx) (U x)=A x := by
      simpa only [A,modelZeroAdjointCoarseAtL,_root_.sum_apply,_root_.smul_apply,
        ContinuousLinearMap.comp_apply,_root_.sub_apply,map_sub,U2,fiveHalfToTwoSection,
        sphereSobolevInclusionL_trans_apply] using hAActual
    simp only [modelPotentialZeroCoreDensity,PhysicalPrincipalData.potentialQuadraticCoreSection,
      PhysicalPrincipalData.potentialQuadraticAdjointCoreSection,dite_eq_left hx,hFValue,hAValue]
    ring
  exact ((hIF.sub hIA).const_mul 4).congr hEq

end ShrinkingSpheres.ParallelEnergy
