module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Algebra

/- Adopted from the selected ZIP, lean/Calderon/CompactParameterSmoothness.lean.
   Mathematical declarations and proof bodies are preserved; local imports are rewritten. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped ContDiff Topology
universe u
namespace OAI.AnisotropicCalderon.CompactParameterSmoothness

variable {K H E : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

def compactPullback (g : H × V → E) (hg : Continuous g) (v : C(K,V)) : H → C(K,E) :=
  fun x => ⟨fun theta => g (x,v theta),hg.comp (continuous_const.prodMk v.continuous)⟩

end OAI.AnisotropicCalderon.CompactParameterSmoothness
