import Proof.NormalFrameCovariantJetBound

noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres

/-- Uniform point, rotation and actual covariant first jets of one fixed
operator family. All bounds refer to the same independent-parameter family. -/
structure NormalFrameOperatorJetBounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : Data) (y : X) (H : NormalFrameParameter → E) (B C0 CC CD : ℝ) : Prop where
  point : ‖H (y,(d.radius y,frameVectorLinear d.frame y))‖ ≤ C0*B*(d.radius y)^2
  rotation : ∀ i j : I,
    ‖deriv (fun t => H (normalFrameRotationCurve d.frame d.radius y i j t)) 0‖ ≤ CC*B*(d.radius y)^2
  covariant : ∀ a : X,
    ‖deriv (fun t => H (normalFrameActualCurve d.frame d.radius y a t)) 0-
      ∑ i,∑ j,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
        deriv (fun t => H (normalFrameRotationCurve d.frame d.radius y i j t)) 0‖ ≤
      CD*B*(d.radius y)^2*beta d.γ d.radius y*‖a‖

end ShrinkingSpheres
