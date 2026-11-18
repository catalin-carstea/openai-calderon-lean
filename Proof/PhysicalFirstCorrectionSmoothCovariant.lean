import Proof.FirstCorrectionAngularFields
import Proof.PhysicalFirstCorrectionCoarseNormalForm
import Proof.CoarseCovariantJetFamily
import Proof.CanonicalFirstRadialFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def physicalFirstCorrectionAngularFields (d : Data) (b x : X) : CoarseAngularFields :=
  firstCorrectionAngularFields (firstDensityLogCovector d x)
    (fun j => frameCoordinateLinear d.γ d.frame x j b) (fderiv ℝ d.radius x b)

def physicalFirstCorrectionCovariantFamily (d : Data) (b : X) (x : X) :
    X →L[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
  coarseCovariantJetFamily d (physicalFirstCorrectionCoarseFamily d b)
    (fun i j y => (physicalFirstCorrectionAngularFields d b y).angular (i,j)) x

lemma physicalFirstCorrectionAngularFields_operator (d : Data) (x b : X)
    (hFrame : ∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (hr : DifferentiableAt ℝ d.radius x) (hr0 : d.radius x ≠ 0) :
    (physicalFirstCorrectionAngularFields d b x).operator=physicalFirstCorrectionCoarseFamily d b x := by
  rw [physicalFirstCorrectionAngularFields,firstCorrectionAngularFields_operator,
    physicalFirstCorrectionCoarseFamily_normal_form d x b hFrame hr hr0]
  congr 2
  simp only [actualCoframeNormalSobolevL,frameCoordinateLinear_apply]

/-- A genuine globally smooth first covariant family is fixed once, before
any centers or tests, for the SAME physical correction coefficient. -/
theorem Admissible.physicalFirstCorrectionCovariantFamily_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (b : X) :
    ContDiffOn ℝ ∞ (physicalFirstCorrectionCovariantFamily d b) Y ∧
      ∀ x ∈ Y,∀ a : X,CoarseCovariantRotationGraph d x a
        (physicalFirstCorrectionCoarseFamily d b) (physicalFirstCorrectionCovariantFamily d b x a) := by
  have hQ : ContDiffOn ℝ ∞ (firstDensityLogCovector d) Y :=
    (hd.1.firstDensityLogCovector_smooth hΩ hK).mono hSub
  have hc (j : I) : ContDiffOn ℝ ∞ (fun x => frameCoordinateLinear d.γ d.frame x j b) Y := by
    have hSmooth := hd.1.1.contDiffOn_metricPair (fun _ => b) (fun x => d.frame x j) contDiffOn_const
      (hd.1.2.2.2.2.2.2.1 j)
    exact (hSmooth.congr (fun x _ => frameCoordinateLinear_apply d.γ d.frame x b j)).mono hSub
  have ht : ContDiffOn ℝ ∞ (fun x => fderiv ℝ d.radius x b) Y :=
    (hd.2.2.2.2.1.1.fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const
  have hFields (x : X) (hx : x ∈ Y) : CoarseAngularFields.SmoothAt (physicalFirstCorrectionAngularFields d b) x :=
    firstCorrectionAngularFields_smoothAt (firstDensityLogCovector d)
      (fun j x => frameCoordinateLinear d.γ d.frame x j b) (fun x => fderiv ℝ d.radius x b) x
      (hQ.contDiffAt (hY.mem_nhds hx)) (fun j => (hc j).contDiffAt (hY.mem_nhds hx))
      (ht.contDiffAt (hY.mem_nhds hx))
  have hOp (x : X) (hx : x ∈ Y) := physicalFirstCorrectionAngularFields_operator d x b
    (hd.1.2.2.2.2.2.2.2 x (hSub hx))
    ((hd.2.2.2.2.1.1.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp))
    (hd.2.2.2.2.1.2 x hx).1.ne'
  have hH : ContDiffOn ℝ ∞ (physicalFirstCorrectionCoarseFamily d b) Y := by
    have hSmooth : ContDiffOn ℝ ∞ (fun x => (physicalFirstCorrectionAngularFields d b x).operator) Y :=
      fun x hx => (hFields x hx).operator.contDiffWithinAt
    exact hSmooth.congr (fun x hx => (hOp x hx).symm)
  have hC (i j : I) : ContDiffOn ℝ ∞ (fun x => (physicalFirstCorrectionAngularFields d b x).angular (i,j)) Y :=
    fun x hx => ((hFields x hx).angular (i,j)).contDiffWithinAt
  refine ⟨contDiffOn_coarseCovariantJetFamily hY hΩ hSub d hd.1.1 hK hd.1.2.2.2.2.2.2.1
    _ _ hH hC,?_⟩
  intro x hx a
  apply coarseCovariantJetFamily_graph d (physicalFirstCorrectionCoarseFamily d b) _ x a
  intro i j u
  let P := firstCorrectionAngularPacket (firstDensityLogCovector d x)
    (fun k => frameCoordinateLinear d.γ d.frame x k b) (fderiv ℝ d.radius x b)
  have hGraph := P.graph (i,j) u
  have hPOp : P.operator=physicalFirstCorrectionCoarseFamily d b x :=
    (congrArg CoarseAngularFields.operator (firstCorrectionAngularFields_ofPacket _ _ _)).trans (hOp x hx)
  rw [hPOp] at hGraph
  exact hGraph

end ShrinkingSpheres
