import Proof.ParallelFirstSelfWeakAdjointPoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

/-- Complete actual first-adjoint core: genuine weak norm control with
constants before arbitrary profiles, frames, coherent packets, and sources.
This does not claim a stronger fibre-L2 or higher-adjoint-jet estimate. -/
theorem uniform_first_formal_adjoint_core_weak_norm_sq_bound
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT CB CS CG CK : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,
      ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      ∀ U : X → SphereSobolev (5/2:ℝ),ContDiffOn ℝ ∞ U Y → ∀ y ∈ Y,
      ‖sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (P.firstFormalAdjointCore WF W U y)‖^2 ≤
        CE*ε^2*∑ b : I,halfCovariantDirectionEnergy d
          (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x))
          y (beta d.γ d.radius y) (axis b) := by
  obtain ⟨ηL,CL,hηL,hηL1,hCL,hLow⟩ := uniform_effective_first_low_endpoint_data
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηD,CD,hηD,hηD1,hCD,hDerivative⟩ := uniform_effective_first_balanced_derivative_bound
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let MQ := 27*K*|M ⟨1,by omega⟩|
  let CE := 9*(CL^2+CD^2+(MQ*CL)^2)
  have hMQ : 0 ≤ MQ := by dsimp only [MQ];positivity
  refine ⟨min ηL ηD,CE,lt_min hηL hηD,(min_le_left _ _).trans hηL1,by dsimp only [CE];positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT CB CS CG CK P WF W U hU y hy
  let V := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
  let β := beta d.γ d.radius y
  let Row := fun b : I => firstAdjointLeadingWeakRow P U b y+firstAdjointDefectWeakRow P WF U b y
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hJet := hDerivative floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CF CT P CB CS WF
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hμ : 0 < metricDensity d.γ y := metricDensity_pos hg (zero_lt_one.trans_le hK) hy
  have hq (b : I) : |(metricDensity d.γ y)⁻¹*fderiv ℝ (metricDensity d.γ) y (axis b)| ≤ MQ := by
    have hRaw := hd.relative_density_axis_bound hΩ (by omega) (zero_lt_one.trans_le hK) hy b
    change |fderiv ℝ (metricDensity d.γ) y (axis b)| ≤ MQ*metricDensity d.γ y at hRaw
    rw [abs_mul,abs_inv,abs_of_pos hμ]
    calc
      _ ≤ (metricDensity d.γ y)⁻¹*(MQ*metricDensity d.γ y) :=
        mul_le_mul_of_nonneg_left hRaw (inv_nonneg.mpr hμ.le)
      _ = MQ := by field_simp
  have hRow (b : I) : ‖Row b‖^2 ≤ (3*(CL^2+CD^2+(MQ*CL)^2))*ε^2*
      halfCovariantDirectionEnergy d V y β (axis b) := by
    obtain ⟨L,H,hForward,hAdj,hHigh,hLN,hAN,hHN⟩ := hJet y hy b b
    have hCN : ‖(P.firstCovariantCoordinateHalfL b y).adjoint‖ ≤ CL*ε/β := by
      simpa only [ContinuousLinearMap.adjoint.norm_map] using
        (hLow floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CF CT P b).2 y hy
    have hDN : ‖WF.covariantCoordinateAdjointDerivative b b y‖ ≤ CD*ε := by
      change ‖halfOperatorCovariantDerivativeL d (fun x => (P.firstCovariantCoordinateHalfL b x).adjoint)
        (WF.covariantCoordinateAdjointHigher b) y (axis b)‖ ≤ _
      rw [hAdj]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul_of_nonneg_left (norm_sphereSobolevInclusionL_le _ _ _) (norm_nonneg _)).trans
          ((mul_one _).le.trans hAN))
    have hBound := weak_adjoint_row_norm_sq_le
      (P.firstCovariantCoordinateHalfL b y).adjoint (WF.covariantCoordinateAdjointDerivative b b y)
      (V y) (halfSectionCovariantDerivativeL d V y (axis b)) hCL hCD hMQ hε hβ hCN hDN (hq b)
    have hJ : sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V y)=
        sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) (U y) := by
      dsimp only [V]
      rw [sphereSobolevInclusionL_trans_apply]
    change ‖-(P.firstCovariantCoordinateHalfL b y).adjoint (halfSectionCovariantDerivativeL d V y (axis b))+
      (-WF.covariantCoordinateAdjointDerivative b b y (V y)-
        ((metricDensity d.γ y)⁻¹*fderiv ℝ (metricDensity d.γ) y (axis b)) •
          (P.firstCovariantCoordinateHalfL b y).adjoint
            (sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) (U y)))‖^2 ≤ _
    rw [←hJ]
    have hNeg (a b c : SphereSobolev (-(1/2:ℝ))) : -a+(-b-c)=-(a+b+c) := by abel
    rw [hNeg,norm_neg]
    exact hBound
  have hSumGraph : sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (P.firstFormalAdjointCore WF W U y)=∑ b : I,Row b := by
    rw [firstFormalAdjointCore_weak_normal_form hY hΩ hSub hd (zero_lt_one.trans_le hK) P WF W U hU hy,
      ←Finset.sum_add_distrib]
  rw [hSumGraph]
  have hSumNorm : ‖∑ b : I,Row b‖^2 ≤ 3*∑ b : I,‖Row b‖^2 := norm_fin_three_sum_sq_le Row
  refine hSumNorm.trans ?_
  calc
    _ ≤ 3*∑ b : I,(3*(CL^2+CD^2+(MQ*CL)^2))*ε^2*halfCovariantDirectionEnergy d V y β (axis b) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun b _ => hRow b)) (by norm_num)
    _ = _ := by rw [←Finset.mul_sum];dsimp only [CE,V,β];ring

end ShrinkingSpheres.ParallelEnergy
