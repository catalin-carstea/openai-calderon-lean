module

public import Proof.CalderonPatch.NativeInverseRegularity

import Proof.CalderonPatch.NativeInverseSmooth

public section

open scoped ContDiff Manifold

namespace CalderonPatch

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

/-- The canonical weak Dirichlet inverse has the smooth and local
zero-forcing representatives used by the native Green kernel. -/
theorem nativeInverseRegularity (D : DirichletData m M) : NativeInverseRegularity D :=
  ⟨nativeWeakInverse_smooth_solution D,nativeWeakInverse_local_zero_forcing D⟩

end CalderonPatch
