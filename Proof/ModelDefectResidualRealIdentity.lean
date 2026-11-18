import Proof.AmbientModelDefectCommonCore
import Proof.PotentialModelDefectForm
import Proof.PhysicalScalarModelDefectSecondIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing

def PhysicalPrincipalData.modelDefectResidualRealForm {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (y : X) : ℝ :=
  sphereSobolevDualPairing (1/2:ℝ) (ambientSobolevSection (1/2:ℝ) (by norm_num) G hG y)
    (P.truncatedResidualValue (ambientModelAdjointDefectSection d G hG) y)

theorem PhysicalPrincipalData.modelDefectResidualRealForm_decomposition
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) {y : X} (hy : y ∈ Y)
    (W : PhysicalPotentialQuarticData P y CG CK) :
    metricDensity d.γ y*P.modelDefectResidualRealForm G hG y=
      (∑ a : I,∑ b : I,scalarModelDefectSecondDensity d
        (scalarPrincipalDensityWeight d.γ d.g₂ d.radius a b)
        (ambientSobolevSection 2 (by norm_num) G hG)
        (ambientHigherSobolevSection 3 (by norm_num) G hG) (axis a) (axis b) y)+
      metricDensity d.γ y*(∑ b : I,firstModelDefectRealForm d (P.firstCovariantCoordinateCoarseL b) G hG b y)+
      metricDensity d.γ y*P.potentialModelDefectRealForm W G hG := by
  let U := ambientSobolevSection 2 (by norm_num) G hG
  let V := ambientModelAdjointDefectSection d G hG
  let Z := ambientModelDefectFiveHalfSection d G hG
  let I0 := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  let u0 := sphereSobolevInclusionL 2 0 (by norm_num) (U y)
  let uh := ambientSobolevSection (1/2:ℝ) (by norm_num) G hG y
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y :=
    hd.2.2.2.2.1.1.log (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
  have hVS := contDiffOn_ambientModelAdjointDefectSection hY d G hG he hlog
  have hNormal := P.truncatedResidualValue_covariant_derivative_normal_form hd hY hΩ hK V hVS hy
  have hMass : sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) uh=u0 := by
    have hh := congrArg (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num))
      (ambientSobolevSection_inclusion 2 (1/2:ℝ) (by norm_num) (by norm_num) (by norm_num) G hG y)
    simpa only [U,uh,u0,sphereSobolevInclusionL_trans_apply] using hh.symm
  have hMass15 : sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num)
      (ambientSobolevSection (3/2:ℝ) (by norm_num) G hG y)=u0 := by
    have hh := congrArg (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num))
      (ambientSobolevSection_inclusion 2 (3/2:ℝ) (by norm_num) (by norm_num) (by norm_num) G hG y)
    simpa only [U,u0,sphereSobolevInclusionL_trans_apply] using hh.symm
  have hPair (v : SphereSobolev 0) : sphereSobolevDualPairing (1/2:ℝ) uh (I0 v)=⟪u0,v⟫_ℝ :=
    (sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num) uh v).trans
      (congrArg (fun z => ⟪z,v⟫_ℝ) hMass)
  have hQArg : sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (Z y)=
      sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) (V y) := by
    have hh : sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num) (Z y)=V y :=
      ambientModelDefectFiveHalfSection_two d G hG y
    have ht := congrArg (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num)) hh
    simpa only [sphereSobolevInclusionL_trans_apply] using ht
  have hQ := P.potentialQuadraticCoreL_balanced hy W (Z y)
  rw [hQArg] at hQ
  change metricDensity d.γ y*sphereSobolevDualPairing (1/2:ℝ) uh (P.truncatedResidualValue V y)=_
  rw [hNormal,←hQ,←map_add,hPair]
  simp only [inner_add_right,inner_sum,real_inner_smul_right,
    scalarModelDefectSecondDensity,scalarPrincipalDensityWeight,firstModelDefectRealForm,
    PhysicalPrincipalData.potentialModelDefectRealForm,sphereSobolevInclusionL_trans_apply,hMass15]
  simp only [Finset.mul_sum]
  dsimp only [U,V,Z,u0,ambientModelAdjointDefectSection]
  have hVeq : ambientModelAdjointDefectSection d G hG=
      (fun z => modelAdjointDefectSobolevL 3 d z (ambientHigherSobolevSection 3 (by norm_num) G hG z)) := rfl
  simp only [hVeq]
  simp only [mul_add,Finset.mul_sum]
  ring

end ShrinkingSpheres
