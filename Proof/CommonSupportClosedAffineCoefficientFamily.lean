import Proof.ClosedCoefficientMatrixInclusion
import Proof.CommonSupportStrongAffineHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def commonSupportClosedAffineCoefficientFamily
    (a a1 : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (F0 : SmoothCoefficientMatrix 2) (r : ℝ) (t : P) : ClosedCoefficientMatrix 2 :=
  commonSupportClosedCoefficientMatrixFamily 2 a ha S hS hz t-
    smoothCoefficientMatrixClosureInclusionL 2 F0-
    r • commonSupportClosedCoefficientMatrixFamily 2 a1 ha1 S1 hS1 hz1 t

theorem contDiff_commonSupportClosedAffineCoefficientFamily
    (a a1 : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (F0 : SmoothCoefficientMatrix 2) (r : ℝ) :
    ContDiff ℝ ∞ (commonSupportClosedAffineCoefficientFamily a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r) :=
  ((contDiff_commonSupportClosedCoefficientMatrixFamily 2 a ha S hS hz).sub contDiff_const).sub
    ((contDiff_commonSupportClosedCoefficientMatrixFamily 2 a1 ha1 S1 hS1 hz1).const_smul r)

/-- The completed affine family has the exact local spatial jets of the true
    residual, simultaneously for every parameter. This serves both native
    forcing and boundary multiplier callers. -/
theorem commonSupportClosedAffineCoefficientFamily_jet_value
    (a a1 aD : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (F0 : SmoothCoefficientMatrix 2) (r : ℝ) (hField : ∀ p,aD p = a p-r • a1 p)
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (i j : I) (k : Fin 2) (x : X) (hx : x ∈ (ballOpens:Set X)) :
    (fun t => ((commonSupportClosedAffineCoefficientFamily a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r t) i j).val
      ⟨k.val,by omega⟩ x) =
      (fun t => iteratedFDeriv ℝ k.val (fun z => (aD (t,z)-(1:Mat)) i j) x) := by
  funext t
  let F := commonSupportMatrixFamily 2 a ha S hS hz
  let F1 := commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1
  have hIncl : commonSupportClosedAffineCoefficientFamily a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r t =
      smoothCoefficientMatrixClosureInclusionL 2 (F t-F0-r • F1 t) := by
    rw [(smoothCoefficientMatrixClosureInclusionL 2).map_sub,
      (smoothCoefficientMatrixClosureInclusionL 2).map_sub,(smoothCoefficientMatrixClosureInclusionL 2).map_smul]
    rfl
  rw [hIncl]
  change ((F t-F0-r • F1 t) i j).val ⟨k.val,by omega⟩ x = _
  rw [coefficientJet_eq_iteratedFDeriv]
  exact ((commonSupport_affine_remainder_coefficient_germs a a1 aD ha ha1 S S1 hS hS1 hz hz1
    r hField F0 hFlat t x hx i j).iteratedFDeriv ℝ k.val).eq_of_nhds

end ShrinkingSpheres
