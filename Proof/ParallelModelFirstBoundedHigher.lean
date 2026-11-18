import Proof.ParallelNormAssemblyReservedFirstBoundedAdjoint
import Proof.ReflectedFirstCorrectionAdjoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Reflected actual negative-grade order-zero remainder. Its genuine
positive H3/2 graph is proved below, rather than inferred from carriers. -/
def modelFirstBoundedAdjointThreeHalfL (d : Data) (b : I) (y : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  (effectiveFirstBoundedRemainderAtL (-(3/2:ℝ)) d b y).adjoint

lemma modelFirstBoundedAdjointThreeHalfL_graph (d : Data) (b : I) (y : X) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp (modelFirstBoundedAdjointThreeHalfL d b y)=
      (effectiveFirstBoundedAdjointHalfL d b y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have hFor : (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)).comp
      (effectiveFirstBoundedRemainderAtL (-(1/2:ℝ)) d b y)=
      (effectiveFirstBoundedRemainderAtL (-(3/2:ℝ)) d b y).comp
        (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)) := by
    apply ContinuousLinearMap.ext
    intro u
    exact effective_first_bounded_inclusion (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num) d b y u
  have hNeg := sphereSobolevInclusionL_normalized_gap_one (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num) (by norm_num)
  have hPos := sphereSobolevInclusionL_normalized_gap_one (3/2:ℝ) (1/2:ℝ) (by norm_num) (by norm_num)
  let J := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let C := effectiveFirstBoundedRemainderAtL (-(1/2:ℝ)) d b y
  let D := effectiveFirstBoundedRemainderAtL (-(3/2:ℝ)) d b y
  have hForJ : J.comp C=D.comp J := (congrArg (fun I0 => I0.comp C) hNeg.symm).trans
    (hFor.trans (congrArg (fun I0 => D.comp I0) hNeg))
  have hAdj := congrArg (fun A : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => A.adjoint) hForJ
  have hJA : J.adjoint=J := sphereSobolevHalfNegativeInclusion_adjoint
  simp only [ContinuousLinearMap.adjoint_comp,hJA] at hAdj
  change (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp D.adjoint=
    C.adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  exact (congrArg (fun I0 => I0.comp D.adjoint) hPos).trans
    (hAdj.symm.trans (congrArg (fun I0 => C.adjoint.comp I0) hPos.symm))

/-- SAME bounded adjoint output, now with a genuine H3/2 representative
of size epsilon/beta². No extra endpoint or regularity premise is used. -/
theorem uniform_model_first_bounded_adjoint_three_half {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 3 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ b : I,
      ContDiffOn ℝ ∞ (modelFirstBoundedAdjointThreeHalfL d b) Y ∧ ∀ y ∈ Y,
      ‖modelFirstBoundedAdjointThreeHalfL d b y‖ ≤ C*ε/(beta d.γ d.radius y)^2 := by
  obtain ⟨C,hC,hBound⟩ := uniform_effective_first_bounded_remainder hY hΩ hm K ρ c₀ M Cj hK (-(3/2:ℝ))
  let Adj : (SphereSobolev (-(3/2:ℝ)) →L[ℝ] SphereSobolev (-(3/2:ℝ))) →L[ℝ]
      (SphereSobolev (-(3/2:ℝ)) →L[ℝ] SphereSobolev (-(3/2:ℝ))) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨C,hC,?_⟩
  intro floor hf ε hε hε1 d hd b
  have hb := hBound floor hf ε hε hε1 d hd b
  refine ⟨Adj.contDiff.comp_contDiffOn hb.1,?_⟩
  intro y hy
  simpa only [modelFirstBoundedAdjointThreeHalfL,ContinuousLinearMap.adjoint.norm_map] using hb.2 y hy

end ShrinkingSpheres.ParallelEnergy
