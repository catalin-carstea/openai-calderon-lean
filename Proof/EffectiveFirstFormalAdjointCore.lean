import Proof.EffectiveFirstCoarseAdjointGreen
import Proof.EffectiveFirstAdjointDensityCoreLp
import Proof.EffectiveFirstAdjointCoreSupport
import Proof.CompactSupportedLpLocalScalar
import Mathlib.MeasureTheory.Function.L2Space

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

def PhysicalPrincipalData.firstFormalAdjointCoreRow
    {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ} (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (WQ : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (b : I) (y : X) : SphereSobolev 0 :=
  -(metricDensity d.γ y)⁻¹ • sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
    (P.firstAdjointDensityCoreRow WF WQ U b y)

lemma PhysicalPrincipalData.firstFormalAdjointCoreRow_density
    {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ} (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (WQ : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (b : I) {y : X} (hμ : metricDensity d.γ y ≠ 0) :
    metricDensity d.γ y • P.firstFormalAdjointCoreRow WF WQ U b y=
      -sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (P.firstAdjointDensityCoreRow WF WQ U b y) := by
  unfold PhysicalPrincipalData.firstFormalAdjointCoreRow
  rw [smul_smul,mul_neg,mul_inv_cancel₀ hμ,neg_one_smul]

lemma PhysicalPrincipalData.firstFormalAdjointCoreRow_memLp
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (WQ : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) (b : I)
    (hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) (p : ℝ≥0∞) :
    MemLp (P.firstFormalAdjointCoreRow WF WQ U b) p (volume.restrict Y) := by
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hCore := P.firstAdjointDensityCoreRow_memLp hY hΩ hSub hd hK WF WQ hCG hCK U hU S hS hSY h0U b hw p
  have hIncl := (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp_memLp' hCore
  exact memLp_local_scalar_smul_of_compact_support hY.measurableSet hS hSY
    (fun y => sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (P.firstAdjointDensityCoreRow WF WQ U b y)) hIncl
    (fun y _ hs => by rw [P.firstAdjointDensityCoreRow_zero_off hY hd WF WQ U hU S hS.isClosed hSY h0U b hw hs,map_zero])
    (fun y => -(metricDensity d.γ y)⁻¹)
    (((hg.contDiffOn_density hK).continuousOn.inv₀ (fun y hy => (metricDensity_pos hg hK hy).ne')).neg)

/-- Actual physical-density adjunction for one complete effective first
row. Both sides use the same source, the same coarse coefficient and the
constructed fibre-L2 adjoint, with the genuine density factor restored. -/
theorem PhysicalPrincipalData.firstFormalAdjointCoreRow_green
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (WQ : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (Ψ : X → SphereSobolev 2)
    (hU : ContDiff ℝ ∞ U) (hΨ : ContDiff ℝ ∞ Ψ)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (h0U : ∀ x ∉ S,U x=0) (h0Ψ : ∀ x ∉ S,Ψ x=0) (b : I)
    (hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) :
    (∫ y in Y,metricDensity d.γ y*⟪sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (U y),
      P.firstCovariantCoordinateCoarseL b y (highSectionCovariantDerivative d Ψ y (axis b))⟫_ℝ)=
      (∫ y in Y,metricDensity d.γ y*⟪sphereSobolevInclusionL 2 0 (by norm_num) (Ψ y),
        P.firstFormalAdjointCoreRow WF WQ U b y⟫_ℝ) := by
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hG := P.firstAdjointDensityCoreRow_coarse_green hY hΩ hSub hd hK WF WQ U Ψ hU hΨ S hS hSY h0U h0Ψ b hw
  have hRight : (∫ y in Y,metricDensity d.γ y*⟪sphereSobolevInclusionL 2 0 (by norm_num) (Ψ y),
        P.firstFormalAdjointCoreRow WF WQ U b y⟫_ℝ)=
      -(∫ y in Y,⟪sphereSobolevInclusionL 2 0 (by norm_num) (Ψ y),
        sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
          (P.firstAdjointDensityCoreRow WF WQ U b y)⟫_ℝ) := by
    rw [←integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    rw [←real_inner_smul_right,
      P.firstFormalAdjointCoreRow_density WF WQ U b (metricDensity_pos hg hK hy).ne',inner_neg_right]
  exact hG.trans hRight.symm

end ShrinkingSpheres
