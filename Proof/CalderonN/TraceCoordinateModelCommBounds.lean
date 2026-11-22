module

public import Proof.CalderonN.SupportedTraceFiberBounds

import Mathlib.Tactic

/-! A chart derivative and the rotation and degree coefficients give a
fiber estimate for the commutator with a coordinate-model derivative. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3700000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}
variable (hn : 3 ≤ dim) (hY : IsOpen Y) {K : ℝ} {g : MetricField dim} {e : Frame dim}
  {r : X dim → ℝ} (hg : Elliptic Y K g) (hK : 0 < K)
  (he : ∀ a,ContDiffOn ℝ ∞ (fun x => e x a) Y)
  (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (r x)) Y)
variable {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
  {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
  {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)

theorem supportedCoordinateModelDerivative_comm_fiber_bound
    {x : X dim} (hx : x ∈ Y) {β U V : ℝ} (hβ : 1 ≤ β) (hV : 0 ≤ V)
    (F G : X dim → Module.End ℝ (SmoothSphereTrace dim))
    (hF : SmoothSupportedTraceFiberRegular Y F) (hG : SmoothSupportedTraceFiberRegular Y G)
    (hAdj : ∀ y ∈ Y, SmoothTraceAdjoint hn (F y) (G y))
    (hU : SmoothSupportedTraceCoefficientBounds hn (smoothTraceFlatDegree hA hEll S) hY x β 1 U F hF)
    (i : I dim) (hΓ : ∀ a b, |frameConnectionCoefficient g e x (axis i) a b| ≤ V)
    (hl : |traceCoordinateLogGradient r i x| ≤ V*β) :
    let P := supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S i
    let T := smoothSupportedTraceFiberAction hY F hF
    SupportedTraceFiberBound hn x 1 ((U+(dim:ℝ)^2*(V*U)+V*U)*β) (P*T-T*P) := by
  dsimp only
  let B := smoothTraceFlatDegree hA hEll S
  let D := smoothSupportedTraceFiberDerivative hY F hF (axis i) x
  let D' := smoothSupportedTraceFiberDerivative hY G hG (axis i) x
  let Γ (a b : I dim) := -(1/2:ℝ)*frameConnectionCoefficient g e x (axis i) a b
  let l := traceCoordinateLogGradient r i x
  let R (a b : I dim) := smoothSphereTraceRotation a b
  let T (a b : I dim) := Γ a b • smoothTraceAngularComm a b (F x)
  let T' (a b : I dim) := Γ a b • (G x*(-R a b)-(-R a b)*G x)
  let U₀ := l • (B*F x-F x*B)
  let U' := l • (G x*B-B*G x)
  have hD : SmoothTraceAdjoint hn D D' :=
    smoothSupportedTraceFiberDerivative_adjoint hn hY F G hF hG hAdj (axis i) hx
  have hT (a b : I dim) : SmoothTraceAdjoint hn (T a b) (T' a b) := by
    let hR := smoothTraceRotation_skew hn a b
    exact ((hR.mul (hAdj x hx)).sub ((hAdj x hx).mul hR)).const_smul _
  have hB := smoothTraceFlatDegree_symmetric hn hA hEll S
  have h₀ : SmoothTraceAdjoint hn U₀ U' :=
    ((hB.mul (hAdj x hx)).sub ((hAdj x hx).mul hB)).const_smul _
  refine ⟨D+(∑ a,∑ b,T a b)+U₀,D'+(∑ a,∑ b,T' a b)+U',?_,?_,?_⟩
  · exact (hD.add (SmoothTraceAdjoint.sum Finset.univ _ _ (fun a _ =>
      SmoothTraceAdjoint.sum Finset.univ _ _ (fun b _ => hT a b)))).add h₀
  · have hΓ' (a b : I dim) : |Γ a b| ≤ V := by
      dsimp only [Γ]
      rw [abs_mul,abs_of_nonpos (by norm_num : -(1/2:ℝ) ≤ 0)]
      exact (mul_le_mul_of_nonneg_left (hΓ a b) (by norm_num)).trans
        (by nlinarith [hV])
    have hA (a b : I dim) : SmoothTraceAngularBound hn 1 (V*U) (T a b) :=
      ((hU.angular.rotation a b).const_smul _).enlarge
        (mul_le_mul_of_nonneg_right (hΓ' a b) hU.angular.nonneg)
    have hSumBound : SmoothTraceAngularBound hn 1 ((dim:ℝ)^2*(V*U)) (∑ a,∑ b,T a b) := by
      have hh := SmoothTraceAngularBound.sum Finset.univ (fun a : I dim => ∑ b,T a b)
        (fun _ => ∑ _b : I dim,V*U) (fun a _ =>
          SmoothTraceAngularBound.sum Finset.univ (T a) (fun _ => V*U) (fun b _ => hA a b))
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,pow_two,mul_assoc] using hh
    have hL := (hU.angular.degree.const_smul l).enlarge (mul_le_mul_of_nonneg_right hl hU.angular.nonneg)
    have hBound := ((hU.first (axis i) (norm_axis i).le).add hSumBound).add hL
    apply hBound.enlarge
    have hPos : 0 ≤ (dim:ℝ)^2*(V*U) := by have := hU.angular.nonneg; positivity
    nlinarith only [mul_le_mul_of_nonneg_left hβ hPos]
  · intro u
    exact supportedCoordinateModelDerivative_comm_fiber hY hg hK he hlog hA hEll S F hF i hx u

end CalderonN
