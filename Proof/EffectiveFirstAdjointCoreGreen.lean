import Proof.EffectiveFirstAdjointBalancedDensity
import Proof.CovariantHalfOperatorMixedGreenAdjoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing

/-- The constructed higher-domain density core represents the actual
formal adjoint on compactly supported sections. The pointwise chosen high
lift is used only through its proved inclusion graph. -/
theorem PhysicalPrincipalData.firstAdjointDensityCoreRow_green
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (WQ : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (Ψ : X → SphereSobolev (3/2:ℝ))
    (hU : ContDiff ℝ ∞ U) (hΨ : ContDiff ℝ ∞ Ψ)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (h0U : ∀ x ∉ S,U x=0) (h0Ψ : ∀ x ∉ S,Ψ x=0) (b : I)
    (hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) :
    IntegrableOn (fun y => ⟪sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) (Ψ y),
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
        (P.firstAdjointDensityCoreRow WF WQ U b y)⟫_ℝ) Y ∧
    (∫ y in Y,metricDensity d.γ y*sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) (U y))
      (P.firstCovariantCoordinateHalfL b y (halfSectionCovariantDerivativeL d Ψ y (axis b))))=
      -(∫ y in Y,⟪sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) (Ψ y),
        sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
          (P.firstAdjointDensityCoreRow WF WQ U b y)⟫_ℝ) := by
  let L := fun y => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let C := fun y => (P.firstCovariantCoordinateHalfL b y).adjoint
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y :=
    (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hL : ContDiff ℝ ∞ L :=
    (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).contDiff.comp hU
  have h0L (x) (hx : x ∉ S) : L x=0 := by simp only [L,h0U x hx,map_zero]
  have hC := P.firstCovariantCoordinateAdjoint_smooth hd hY hΩ hK b hw
  have hA := WF.covariantCoordinateAdjointHigher_smooth hd b hw
  have hG := covariant_half_operator_mixed_green_adjoint hY d hg hK he Ψ L hΨ hL S hS hSY
    h0Ψ h0L C (WF.covariantCoordinateAdjointHigher b) hC hA
    (fun _ hy => WF.covariantCoordinateAdjointHigher_balanced b hy) b
  have hG' : IntegrableOn (fun y => sphereSobolevDualPairing (1/2:ℝ) (J (Ψ y))
      (P.firstAdjointBalancedDensityRow WF U b y)) Y ∧
    (∫ y in Y,metricDensity d.γ y*sphereSobolevDualPairing (1/2:ℝ)
      (halfSectionCovariantDerivativeL d Ψ y (axis b)) (C y (J (L y))))=
      -(∫ y in Y,sphereSobolevDualPairing (1/2:ℝ) (J (Ψ y))
        (P.firstAdjointBalancedDensityRow WF U b y)) := by
    simpa only [PhysicalPrincipalData.firstAdjointBalancedDensityRow,
      PhysicalFirstCommutatorPacket.covariantCoordinateAdjointDerivative,C,J,L,
      sphereSobolevInclusionL_trans_apply] using hG
  have hPoint (y : X) (hy : y ∈ Y) :
      sphereSobolevDualPairing (1/2:ℝ) (J (Ψ y)) (P.firstAdjointBalancedDensityRow WF U b y)=
      ⟪sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) (Ψ y),
        sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
          (P.firstAdjointDensityCoreRow WF WQ U b y)⟫_ℝ := by
    rw [←P.firstAdjointDensityCoreRow_balanced_graph hY hΩ hd hK WF WQ U hU.contDiffOn b hw hy]
    have hh := sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num)
      (J (Ψ y)) (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
        (P.firstAdjointDensityCoreRow WF WQ U b y))
    simpa only [J,sphereSobolevInclusionL_trans_apply] using hh
  have hAE := (ae_restrict_mem (μ:=volume) hY.measurableSet).mono hPoint
  refine ⟨hG'.1.congr hAE,?_⟩
  have hLeft (y : X) : sphereSobolevDualPairing (1/2:ℝ)
      (halfSectionCovariantDerivativeL d Ψ y (axis b)) (C y (J (L y)))=
      sphereSobolevDualPairing (1/2:ℝ)
        (sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) (U y))
        (P.firstCovariantCoordinateHalfL b y (halfSectionCovariantDerivativeL d Ψ y (axis b))) := by
    simp only [C,J,L,sphereSobolevInclusionL_trans_apply,sphereSobolevDualPairing]
    exact (real_inner_comm _ _).trans ((P.firstCovariantCoordinateHalfL b y).adjoint_inner_left _ _)
  calc
    _ = ∫ y in Y,metricDensity d.γ y*sphereSobolevDualPairing (1/2:ℝ)
        (halfSectionCovariantDerivativeL d Ψ y (axis b)) (C y (J (L y))) :=
      integral_congr_ae (Eventually.of_forall (fun y => congrArg (fun z => metricDensity d.γ y*z) (hLeft y).symm))
    _ = _ := hG'.2.trans (congrArg Neg.neg (integral_congr_ae hAE))

end ShrinkingSpheres
