module

public import Proof.CalderonN.BallRegularity.CoefficientJetFamily
public import Proof.CalderonN.BallRegularity.ClosedSubmoduleSmoothness
/-! From Proof/Archive/(ClosedCoefficientJets dim).lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section


set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Set
open scoped ContDiff
namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]

abbrev ClosedCoefficientJets (dim : ℕ) (r : ℕ) := ↥((smoothCoefficientJetSubmodule dim) r).topologicalClosure

instance instCompleteSpaceClosedCoefficientJets (r : ℕ) : CompleteSpace ((ClosedCoefficientJets dim) r) := by
  unfold ClosedCoefficientJets
  infer_instance

def smoothCoefficientClosureInclusionL (r : ℕ) :
    (SmoothCoefficientJets dim) r →L[ℝ] (ClosedCoefficientJets dim) r :=
  ((smoothCoefficientJetSubmodule dim) r).subtypeL.codRestrict
    ((smoothCoefficientJetSubmodule dim) r).topologicalClosure
    (fun F => ((smoothCoefficientJetSubmodule dim) r).le_topologicalClosure F.property)

theorem norm_smoothCoefficientClosureInclusionL (r : ℕ) (F : (SmoothCoefficientJets dim) r) :
    ‖smoothCoefficientClosureInclusionL r F‖ = ‖F‖ := rfl

theorem denseRange_smoothCoefficientClosureInclusionL (dim : ℕ) (r : ℕ) :
    DenseRange (smoothCoefficientClosureInclusionL (dim := dim) r) := by
  change DenseRange (Set.inclusion ((smoothCoefficientJetSubmodule dim) r).le_topologicalClosure)
  apply (denseRange_inclusion_iff ((smoothCoefficientJetSubmodule dim) r).le_topologicalClosure).mpr
  rw [Submodule.topologicalClosure_coe]

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]

def commonSupportClosedCoefficientFamily (r : ℕ) (g : H × (X dim) → ℝ)
    (hg : ContDiff ℝ ∞ g) (K : Set (X dim)) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) (t : H) : (ClosedCoefficientJets dim) r :=
  smoothCoefficientClosureInclusionL r (commonSupportCoefficientFamily r g hg K hK hz t)

theorem commonSupportClosedCoefficientFamily_val (r : ℕ) (g : H × (X dim) → ℝ)
    (hg : ContDiff ℝ ∞ g) (K : Set (X dim)) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) (t : H) :
    (commonSupportClosedCoefficientFamily r g hg K hK hz t).val =
      (commonSupportCoefficientFamily r g hg K hK hz t).val := rfl

theorem contDiff_commonSupportClosedCoefficientFamily [FiniteDimensional ℝ H]
    (r : ℕ) (g : H × (X dim) → ℝ) (hg : ContDiff ℝ ∞ g) (K : Set (X dim)) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) :
    ContDiff ℝ ∞ (commonSupportClosedCoefficientFamily r g hg K hK hz) := by
  apply contDiff_infty_closed_submodule _
    ((smoothCoefficientJetSubmodule dim) r).isClosed_topologicalClosure
  exact contDiff_commonSupportCoefficientFamily_val r g hg K hK hz
end CalderonN.BallDirichlet
