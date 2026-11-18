import Proof.Archive.SphereSobolevFinitePhysicalHalfDualPackets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped Topology
namespace OAI.AnisotropicCalderon.SphereHarmonic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Physical harmonic single modes determine a continuous Sobolev map. -/
lemma sphereSobolev_clm_ext_on_single (s : ℝ) (T S : SphereSobolev s →L[ℝ] E)
    (hSingle : ∀ n : ℕ,∀ z : harmonicSphereSubspace n,T (sphereSobolevSingleL s n z) = S (sphereSobolevSingleL s n z)) :
    T = S := by
  have hFinite (u : SphereSobolev s) (hu : u ∈ sphereSobolevFiniteSupport s) : T u = S u := by
    obtain ⟨n,hn⟩ := hu
    have hU := sphereSobolev_eq_physical_packet_of_finiteSupport s n u hn
    calc
      T u = T (∑ k ∈ Finset.range n,sphereSobolevSingleL s k (sphereSobolevCoefficientL s k u)) := congrArg T hU
      _ = ∑ k ∈ Finset.range n,T (sphereSobolevSingleL s k (sphereSobolevCoefficientL s k u)) := map_sum _ _ _
      _ = ∑ k ∈ Finset.range n,S (sphereSobolevSingleL s k (sphereSobolevCoefficientL s k u)) :=
        Finset.sum_congr rfl (fun k _ => hSingle k _)
      _ = S u := ((map_sum S _ _).symm.trans (congrArg S hU.symm))
  have hClosed : IsClosed {u : SphereSobolev s | T u = S u} := isClosed_eq T.continuous S.continuous
  have hc := closure_minimal (s := sphereSobolevFiniteSupport s) hFinite hClosed
  rw [closure_sphereSobolevFiniteSupport] at hc
  exact ContinuousLinearMap.ext (fun u => hc (mem_univ u))
end OAI.AnisotropicCalderon.SphereHarmonic
