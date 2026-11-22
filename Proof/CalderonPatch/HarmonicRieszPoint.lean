module

public import Proof.CalderonN.HarmonicJetEvaluation
public import Mathlib.Analysis.InnerProductSpace.Dual

import Mathlib.Topology.Algebra.Module.Multilinear.Topology
import Mathlib.Tactic

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff RealInnerProductSpace Topology

namespace CalderonN

variable {d : ℕ} [NeZero d] {U : Set (X d)} (hU : IsOpen U)
  {g : MetricField d} (hg : SmoothMetric U g)

local notation "H" => harmonicL2Space hU hg
local notation "B" k => ContinuousMultilinearMap ℝ (fun _ : Fin k => X d) ℝ
local notation "Read" k => (H →L[ℝ] B k)
local notation "DRead" k => (X d →L[ℝ] Read k)

/-- Derivative evaluation as an operator-valued function on an
interior chart. Its values outside the chart are immaterial. -/
def harmonicEvalJets (k : ℕ) (x : X d) : H →L[ℝ] B k := by
  classical
  exact if hx : x ∈ U then harmonicJetCLM hU hg (harmonicInteriorJets_of_smoothMetric hU hg) k x hx
    else 0

theorem harmonicEvalJets_apply (k : ℕ) {x : X d} (hx : x ∈ U) (u : H) :
    harmonicEvalJets hU hg k x u = iteratedFDeriv ℝ k (harmonicRepresentative u) x := by
  rw [harmonicEvalJets,dite_eq_left hx,harmonicJetCLM_apply]

/-- The local Riesz representer of point evaluation in the closed
space of classical harmonic L² functions. -/
@[expose] def harmonicRiesz (x : X d) : H :=
  (InnerProductSpace.toDual ℝ H).symm
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => X d) ℝ 0).comp (harmonicEvalJets hU hg 0 x))

theorem harmonicRiesz_pair {x : X d} (hx : x ∈ U) (u : H) :
    ⟪harmonicRiesz hU hg x, u⟫ = harmonicRepresentative u x := by
  unfold harmonicRiesz
  rw [InnerProductSpace.toDual_symm_apply]
  change harmonicEvalJets hU hg 0 x u _ = _
  rw [harmonicEvalJets_apply hU hg 0 hx,iteratedFDeriv_zero_apply]

end CalderonN
