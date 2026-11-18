import Proof.ParallelNormAssemblyReservedFirstBounded
import Proof.LowBoundedCorrectionAdjoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Genuine order-zero half realization of the true physical adjoint of
the explicitly separated bounded first coefficient. Its negative-grade
origin is retained in the exact adjunction graph below. -/
def effectiveFirstBoundedAdjointHalfL (d : Data) (b : I) (y : X) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (effectiveFirstBoundedRemainderAtL (-(1/2:ℝ)) d b y).adjoint

def effectiveFirstBoundedAdjointHigherL (d : Data) (b : I) (y : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (effectiveFirstBoundedAdjointHalfL d b y).comp
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))

lemma effective_first_bounded_low_adjoint_graph (d : Data) (b : I) (y : X)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) :
    (effectiveFirstBoundedRemainderHalfL d b y).adjoint=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        (effectiveFirstBoundedAdjointHalfL d b y) := by
  have hLow : effectiveFirstBoundedRemainderHalfL d b y=
      (effectiveFirstBoundedRemainderAtL (-(1/2:ℝ)) d b y).comp
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
    rw [←effective_first_bounded_half_actual d b y he]
    apply ContinuousLinearMap.ext
    intro u
    exact effective_first_bounded_inclusion (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) d b y u
  rw [hLow,ContinuousLinearMap.adjoint_comp,sphereSobolevHalfNegativeInclusion_adjoint]
  rfl

lemma effective_first_bounded_adjoint_higher_graph (d : Data) (b : I) (y : X)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (effectiveFirstBoundedAdjointHigherL d b y)=
      (effectiveFirstBoundedRemainderHalfL d b y).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  rw [effectiveFirstBoundedAdjointHigherL,effective_first_bounded_low_adjoint_graph d b y he,
    ContinuousLinearMap.comp_assoc]

/-- The genuine physical adjoint of the bounded geometric remainder has
one smooth order-zero half family and the same sharp epsilon/beta² bound.
The displayed graphs, rather than carrier equality, justify its use. -/
theorem uniform_effective_first_bounded_adjoint_half {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 3 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ b : I,
    ContDiffOn ℝ ∞ (effectiveFirstBoundedAdjointHalfL d b) Y ∧ ∀ y ∈ Y,
      ‖effectiveFirstBoundedAdjointHalfL d b y‖ ≤ C*ε/(beta d.γ d.radius y)^2 := by
  obtain ⟨C,hC,hBound⟩ := uniform_effective_first_bounded_remainder hY hΩ hm K ρ c₀ M Cj hK (-(1/2:ℝ))
  let Adj : (SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) →L[ℝ]
      (SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨C,hC,?_⟩
  intro floor hf ε hε hε1 d hd b
  have hB := hBound floor hf ε hε hε1 d hd b
  refine ⟨Adj.contDiff.comp_contDiffOn hB.1,?_⟩
  intro y hy
  simpa only [effectiveFirstBoundedAdjointHalfL,ContinuousLinearMap.adjoint.norm_map] using hB.2 y hy

end ShrinkingSpheres.ParallelEnergy
