import Proof.CommonSupportWeakEnergyDerivative
import Proof.AngleLowJetDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- The local angle generator alone controls the actual zeroth coefficient
    parameter jet. No spatial derivative of that generator is required. -/
theorem norm_fderiv_angle_coefficient_zero_jet_le
    (a : ℝ × X → Mat) (b : X → Mat) (x : X)
    (hb : HasDerivAt (fun θ => a (θ,x)) (b x) 0)
    (q : ℝ) (hq : 0 ≤ q) (hValue : ‖b x‖ ≤ q) (i j : I) :
    ‖fderiv ℝ (fun θ => iteratedFDeriv ℝ 0 (fun z => a (θ,z) i j) x) 0‖ ≤ q := by
  let C := (continuousMultilinearCurryFin0 ℝ X ℝ).symm
  have hEntry : HasDerivAt (fun θ => a (θ,x) i j) (b x i j) 0 := by
    simpa only [Function.comp_def,matrixEntryL_apply] using
      (matrixEntryL i j).hasFDerivAt.comp_hasDerivAt (0:ℝ) hb
  have h := C.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0:ℝ) hEntry
  simp only [Function.comp_def] at h
  have hSame : (fun θ => iteratedFDeriv ℝ 0 (fun z => a (θ,z) i j) x) =
      fun θ => C (a (θ,x) i j) := rfl
  have hn : ‖fderiv ℝ (fun θ => C (a (θ,x) i j)) 0‖ = ‖C (b x i j)‖ := by
    rw [← norm_deriv_eq_norm_fderiv]
    exact congrArg norm h.deriv
  rw [hSame,hn,LinearIsometryEquiv.norm_map,Real.norm_eq_abs]
  exact (Matrix.norm_entry_le_entrywise_sup_norm (b x) (i:=i) (j:=j)).trans hValue

/-- Genuine full weak energy angle derivatives depend only on the local
    matrix angle generator on the physical ball. -/
theorem norm_fderiv_angle_commonSupport_fullWeakEnergy_le
    (a : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (K : Set X) (hK : IsCompact K)
    (hz : ∀ θ z,z ∉ K → a (θ,z) = 0) (b : X → Mat)
    (hb : ∀ z ∈ (ballOpens:Set X),HasDerivAt (fun θ => a (θ,z)) (b z) 0)
    (q : ℝ) (hq : 0 ≤ q) (hValue : ∀ z ∈ (ballOpens:Set X),‖b z‖ ≤ q) :
    ‖fderiv ℝ (commonSupportFullWeakEnergy a ha) 0‖ ≤ weakFullDerivativeBudget*q := by
  exact norm_fderiv_commonSupportFullWeakEnergy_le a ha K hK hz 0 q hq
    (fun i j x hx => norm_fderiv_angle_coefficient_zero_jet_le a b x (hb x hx) q hq (hValue x hx) i j)

/-- The same true angle generator controls both restrictions of the actual
    energy form, with their native inherited zero-boundary structures. -/
theorem norm_fderiv_angle_commonSupport_weakEnergy_le
    (a : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (K : Set X) (hK : IsCompact K)
    (hz : ∀ θ z,z ∉ K → a (θ,z) = 0) (b : X → Mat)
    (hb : ∀ z ∈ (ballOpens:Set X),HasDerivAt (fun θ => a (θ,z)) (b z) 0)
    (q : ℝ) (hq : 0 ≤ q) (hValue : ∀ z ∈ (ballOpens:Set X),‖b z‖ ≤ q) :
    ‖fderiv ℝ (commonSupportWeakEnergy a ha) 0‖ ≤ weakFullDerivativeBudget*q ∧
    ‖fderiv ℝ (commonSupportZeroWeakEnergy a ha) 0‖ ≤ weakFullDerivativeBudget*q := by
  have hJet (i j : I) (x : X) (hx : x ∈ (ballOpens:Set X)) :
      ‖fderiv ℝ (fun θ => iteratedFDeriv ℝ 0 (fun z => a (θ,z) i j) x) 0‖ ≤ q :=
    norm_fderiv_angle_coefficient_zero_jet_le a b x (hb x hx) q hq (hValue x hx) i j
  exact ⟨norm_fderiv_commonSupportWeakEnergy_le a ha K hK hz 0 q hq hJet,
    norm_fderiv_commonSupportZeroWeakEnergy_le a ha K hK hz 0 q hq hJet⟩

end ShrinkingSpheres
