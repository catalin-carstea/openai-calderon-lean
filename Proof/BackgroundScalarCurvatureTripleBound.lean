import Proof.ScalarCurvatureTriplePointBound
import Proof.ScalarCovariantThirdCrossReduction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def fixedDirectionAngularCurvatureBudget {m : ℕ} (hm : 2 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) : ℝ :=
  3*Real.sqrt 2*curvatureBudget K |M 0| |M ⟨1,by omega⟩| |M ⟨2,by omega⟩|

lemma fixedDirectionAngularCurvatureBudget_nonneg {m : ℕ} (hm : 2 ≤ m) (K : ℝ)
    (hK : 0 ≤ K) (M : Fin (m+1) → ℝ) : 0 ≤ fixedDirectionAngularCurvatureBudget hm K M :=
  mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 2))
    (curvatureBudget_nonneg K _ _ _ hK (abs_nonneg _) (abs_nonneg _) (abs_nonneg _))

def coarseCovariantTripleEnergy (d : Data) (U : X → SphereSobolev 2) (y : X)
    (β : ℝ) (a b c : X) : ℝ :=
  let I10 := sphereSobolevInclusionL 1 0 (by norm_num)
  β⁻¹*(‖I10 (highSectionCovariantDerivative d U y a)‖^2+
    ‖I10 (highSectionCovariantDerivative d U y b)‖^2+
    ‖I10 (highSectionCovariantDerivative d U y c)‖^2)+
    β*‖sphereSobolevInclusionL 2 1 (by norm_num) (U y)‖^2

/-- The actual fixed-axis curvature remainder has the common reference
curvature constant. The three coefficient-weight premises are exposed for
the actual scalar-adjoint coefficient producer to discharge. -/
theorem Background.scalar_third_cross_remainder_bound {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} (hK : 1 ≤ K) {m : ℕ} (hm : 2 ≤ m) {M : Fin (m+1) → ℝ}
    {d : Data} (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame)
    (q : X → ℝ) (U : X → SphereSobolev 2) {y : X} (hy : y ∈ Ω)
    (μ Q Q0 ε β : ℝ) (hμ : 0 ≤ μ) (hQ : 0 ≤ Q) (hQ0 : 0 ≤ Q0) (hβ : 1 ≤ β)
    (hq : |q y| ≤ μ*Q0*ε^2/β^3)
    (hDq : ∀ k : I,|fderiv ℝ q y (axis k)| ≤ μ*Q*ε^2/β^2) (a b c : I) :
    |scalarCovariantThirdCrossRemainder d q U (axis a) (axis b) (axis c) y| ≤
      (3*Q+3*Q0*fixedDirectionAngularCurvatureBudget hm K M)*μ*ε^2*
        coarseCovariantTripleEnergy d U y β (axis a) (axis b) (axis c) := by
  let CR := fixedDirectionAngularCurvatureBudget hm K M
  have hCR : 0 ≤ CR := fixedDirectionAngularCurvatureBudget_nonneg hm K (zero_le_one.trans hK) M
  have hCurv (i j : I) : ‖frameCurvatureRotationL d.γ d.frame y (axis i) (axis j)‖ ≤ CR := by
    simpa only [norm_axis,mul_one,CR,fixedDirectionAngularCurvatureBudget] using
      h.norm_frameCurvatureRotationL_le hΩ hK hm hy (axis i) (axis j)
  exact scalar_curvature_triple_point_bound (sphereSobolevInclusionL 2 1 (by norm_num) (U y))
    (sphereSobolevInclusionL 1 0 (by norm_num) (highSectionCovariantDerivative d U y (axis a)))
    (sphereSobolevInclusionL 1 0 (by norm_num) (highSectionCovariantDerivative d U y (axis b)))
    (sphereSobolevInclusionL 1 0 (by norm_num) (highSectionCovariantDerivative d U y (axis c)))
    (frameCurvatureRotationL d.γ d.frame y (axis a) (axis b))
    (frameCurvatureRotationL d.γ d.frame y (axis c) (axis b))
    (frameCurvatureRotationL d.γ d.frame y (axis a) (axis c))
    (q y) (fderiv ℝ q y (axis a)) (fderiv ℝ q y (axis b)) (fderiv ℝ q y (axis c))
    μ Q Q0 CR ε β hμ hQ hQ0 hCR hβ (hCurv a b) (hCurv c b) (hCurv a c) hq (hDq a) (hDq b) (hDq c)

end ShrinkingSpheres
