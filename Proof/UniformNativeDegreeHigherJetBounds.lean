import Proof.NativeDegreeHigherEndpoints
import Proof.RotationHighLiftJets
import Proof.UniformNativeRelativeDegreeHigherData
import Proof.UniformNativeSelectedDegreeJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- Closed common radius-squared joint two-jet bounds for BOTH genuine
higher degree-commutator endpoints of ANY already selected native domain.
The low family is identified as a genuine germ before transferring bounds;
no higher endpoint or derivative estimate is an extra premise. -/
theorem uniform_native_degree_higher_two_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CI CW : ℝ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1) :
    ∃ η CH : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ CH ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CQ CF CA CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      ∀ V : s.response.SymmetricAdjointDomain,
      V.HigherDegreeJetBound hd.1.1 (zero_lt_one.trans_le hK) (by norm_num)
        ((y,frameVectorLinear d.frame y),0) 2 (CH*(d.radius y)^2) := by
  obtain ⟨η,CD,hη,hη1,hCD,hDegree⟩ := uniform_native_selected_degree_jets
    hY hΩ 3 (by omega) K ρ c₀ M Cj hK hρ CI CW hCI hCW F0 hF0
  obtain ⟨CG,hCG,hAngular⟩ := uniform_relative_angular_derivative_higher_jets
    (E:=SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) hΩ 2 (by omega) K M hK
  let CP := (19+9*Real.sqrt 2)*CG*CD
  let CH := 1+CP
  have hCG0 : 0 ≤ CG := zero_le_one.trans hCG
  have hCD0 : 0 ≤ CD := zero_le_one.trans hCD
  have hCP : 0 ≤ CP := by dsimp only [CP];positivity
  have hCH : 1 ≤ CH := by dsimp only [CH];linarith only [hCP]
  have hCPC : CP ≤ CH := by dsimp only [CH];linarith
  refine ⟨η,CH,hη,hη1,hCH,?_⟩
  intro floor hf ε hε hSmall d hd y hy CQ CF CA CM s V
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let S := V.degreeFamily hd.1.1 (zero_lt_one.trans_le hK) (by norm_num)
  have hSelected := hDegree floor hf ε hε hSmall d hd y hy CQ CF CA CM s V
  have hSJ := hSelected.bound
  have hSS : ContDiffAt ℝ ∞ S p := hSelected.smooth
  have he (i j : I) : metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hSub hy) i j
  have hAngularS := hAngular d.γ d.g₁ d.g₂ d.frame hd.1 y (hSub hy) (frameVectorLinear d.frame y)
    he S hSS (CD*(d.radius y)^2) (by positivity) hSJ
  let BB := CG*(CD*(d.radius y)^2)
  have hBB : 0 ≤ BB := by dsimp only [BB];positivity
  have hLow : CD*(d.radius y)^2 ≤ BB := by
    simpa only [BB,one_mul] using mul_le_mul_of_nonneg_right hCG (mul_nonneg hCD0 (sq_nonneg (d.radius y)))
  have hS : SmoothFiniteJetBound S p 2 BB :=
    ⟨hBB,hSS,fun n hn => (hSJ n (by omega)).trans hLow⟩
  have hG (ij : I × I) : SmoothFiniteJetBound (normalFrameRelativeAngularDerivative d.γ S ij.1 ij.2) p 2 BB :=
    ⟨hBB,(hAngularS ij.1 ij.2).1,(hAngularS ij.1 ij.2).2⟩
  have hHigh := smoothFiniteJetBound_rotation_high_lift S
    (fun ij => normalFrameRelativeAngularDerivative d.γ S ij.1 ij.2) p 2 BB hS hG
  have hAdj := smoothFiniteJetBound_rotation_high_lift (fun x => (S x).adjoint)
    (fun ij x => (normalFrameRelativeAngularDerivative d.γ S ij.1 ij.2 x).adjoint) p 2 BB
    hS.adjoint (fun ij => (hG ij).adjoint)
  have hFinal : (19+9*Real.sqrt 2)*BB ≤ CH*(d.radius y)^2 := by
    calc
      _ = CP*(d.radius y)^2 := by dsimp only [CP,BB];ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCPC (sq_nonneg _)
  constructor
  · exact hHigh.weaken hFinal
  · exact hAdj.weaken hFinal
end ShrinkingSpheres
