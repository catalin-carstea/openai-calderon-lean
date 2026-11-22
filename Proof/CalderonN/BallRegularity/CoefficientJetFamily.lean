module

public import Proof.CalderonN.BallRegularity.CoefficientJetSpace
public import Proof.CalderonN.BallRegularity.SpatialJetFields
/-! From Proof/Archive/CoefficientJetFamily.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section


set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Set
open scoped ContDiff
namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]

def commonSupportCoefficientFamily (r : ℕ) (g : H × (X dim) → ℝ)
    (hg : ContDiff ℝ ∞ g) (K : Set (X dim)) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) (t : H) : (SmoothCoefficientJets dim) r :=
  compactCoefficient r (fun x => g (t,x))
    (SpatialJetFields.contDiff_spatial_slice g hg t)
    (SpatialJetFields.hasCompactSupport_spatial_slice g K hK hz t)

theorem coefficientValue_commonSupportCoefficientFamily (r : ℕ) (g : H × (X dim) → ℝ)
    (hg : ContDiff ℝ ∞ g) (K : Set (X dim)) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) (t : H) (x : (X dim)) :
    coefficientValue r (commonSupportCoefficientFamily r g hg K hK hz t) x = g (t,x) :=
  congrFun (coefficientValue_compactCoefficient r _ _ _) x

theorem commonSupportCoefficientFamily_jet (r : ℕ) (g : H × (X dim) → ℝ)
    (hg : ContDiff ℝ ∞ g) (K : Set (X dim)) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) (t : H) (j : Fin (r + 1)) (x : (X dim)) :
    (commonSupportCoefficientFamily r g hg K hK hz t).1 j x =
      iteratedFDeriv ℝ j.val (fun y => g (t,y)) x := rfl

theorem contDiff_commonSupportCoefficientFamily_val (r : ℕ) (g : H × (X dim) → ℝ)
    (hg : ContDiff ℝ ∞ g) (K : Set (X dim)) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) :
    ContDiff ℝ ∞ (fun t => (commonSupportCoefficientFamily r g hg K hK hz t).1) := by
  apply contDiff_pi.mpr
  intro j
  convert SpatialJetFields.contDiff_infty_spatialJetSlice j.val g hg K hK hz using 1
  funext t
  apply BoundedContinuousFunction.ext
  intro x
  exact (SpatialJetFields.spatialJetField_eq_iteratedFDeriv j.val g hg t x).symm

theorem continuous_commonSupportCoefficientFamily (r : ℕ) (g : H × (X dim) → ℝ)
    (hg : ContDiff ℝ ∞ g) (K : Set (X dim)) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) :
    Continuous (commonSupportCoefficientFamily r g hg K hK hz) :=
  continuous_induced_rng.mpr
    (contDiff_commonSupportCoefficientFamily_val r g hg K hK hz).continuous

end CalderonN.BallDirichlet
