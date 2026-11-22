module

public import Proof.CalderonN.MovingTraceDriftSplit
public import Proof.CalderonN.TraceCoordinatePotential
public import Proof.CalderonN.ActualSupportedLowerOrderVelocity

import Proof.CalderonN.SmoothTraceAngularCommutator
import Mathlib.Tactic

/-! The direct drift remainder needs only the size of the drift.
Its coefficient on base derivatives has weight β⁻² and the angular
potential has weight β⁻¹. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4300000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}

theorem actualDriftRemainder_fiber (hn : 3 ≤ dim) (hY : IsOpen Y) {K : ℝ}
    (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ a,ContDiffOn ℝ ∞ (fun x => d.frame x a) Y)
    (hr : ContDiffOn ℝ ∞ d.radius Y) (hr₀ : ∀ x ∈ Y,d.radius x ≠ 0)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
    (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun x => principal d.γ d.g₂ x i j) Y)
    (hb : ∀ k,ContDiffOn ℝ ∞ (fun x => drift d.γ d.g₂ x k) Y)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)
    (F : ∀ x ∈ Y,ActualGaussFiberData d x)
    (hC : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussFiberFamily F i))
    (hF : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussAffineFamily F i))
    {x : X dim} (hx : x ∈ Y) {β D U : ℝ} (hβ : 1 ≤ β) (hD : 0 ≤ D) (hU : 0 ≤ U)
    (hrp : 0 ≤ d.radius x) (hSmall : d.radius x*β^2 ≤ 1)
    (hk : ∀ i,|traceCoordinateDrift d.γ d.g₂ i x| ≤ D)
    (hΓ : ∀ i a b,|frameConnectionCoefficient d.γ d.frame x (axis i) a b| ≤ D)
    (hl : ∀ i,|traceCoordinateLogGradient d.radius i x| ≤ D*β)
    (hW : ∀ i,SmoothTraceAngularBound hn 1 U (actualGaussLowerVelocityFamily F i x)) :
    let V := supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S
    let b := supportedCoordinateTraceDrift hY hg hK hr hQ hb
    let E := actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF
    let F₁ := actualSupportedAffine hY F hF
    let C := D+(dim:ℝ)*(D*((dim:ℝ)^2*(D*(2*(dim:ℝ)))+D+U))
    ∃ (L : I dim → Module.End ℝ (SmoothSphereTrace dim)) (Q : Module.End ℝ (SmoothSphereTrace dim)),
      (∀ i,SmoothTraceAngularBound hn 0 (C*(β⁻¹)^2) (L i)) ∧
      SmoothTraceAngularBound hn 1 (C*β⁻¹) Q ∧
      ∀ w,smoothSupportedTraceFiberL x (movingTraceDriftRemainder b V E F₁ w) =
        (∑ i,L i (smoothSupportedTraceFiberL x (smoothSupportedTraceBaseDiff (axis i) w)))+
          Q (smoothSupportedTraceFiberL x w) := by
  dsimp only
  let B := smoothTraceFlatDegree hA hEll S
  let Γ (i a b : I dim) := traceCoordinateConnectionScalar d.γ d.frame i a b x
  let f (i : I dim) := traceCoordinateLogGradient d.radius i x
  let c (i : I dim) := d.radius x*traceCoordinateDrift d.γ d.g₂ i x
  let Pot (i : I dim) := (∑ a : I dim,∑ b : I dim,Γ i a b • smoothSphereTraceRotation a b)+f i • B
  let W (i : I dim) := actualGaussLowerVelocityFamily F i x
  let T := (dim:ℝ)^2*(D*(2*(dim:ℝ)))+D+U
  let C := D+(dim:ℝ)*(D*T)
  let L (i : I dim) : Module.End ℝ (SmoothSphereTrace dim) := c i • 1
  let Q := ∑ i,c i • (Pot i+W i)
  have hβ₀ : 0 < β := zero_lt_one.trans_le hβ
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hC₁ : D ≤ C := le_add_of_nonneg_right (by positivity)
  have hC₂ : (dim:ℝ)*(D*T) ≤ C := le_add_of_nonneg_left hD
  have hr' : d.radius x ≤ (β⁻¹)^2 := by
    rw [inv_pow,inv_eq_one_div,le_div_iff₀ (sq_pos_of_pos hβ₀)]
    exact hSmall
  have hc (i : I dim) : |c i| ≤ D*(β⁻¹)^2 := by
    rw [show c i = d.radius x*traceCoordinateDrift d.γ d.g₂ i x from rfl,abs_mul,abs_of_nonneg hrp,mul_comm D]
    exact mul_le_mul hr' (hk i) (abs_nonneg _) (by positivity)
  have hOne : SmoothTraceAngularBound hn 0 1 (1 : Module.End ℝ (SmoothSphereTrace dim)) := by
    intro i j hij w
    have hji : j = i := Fin.ext (by simpa using hij)
    rw [hji,Module.End.one_apply,one_mul]
  have hB : SmoothTraceAngularBound hn 1 1 B :=
    smoothTraceDegree_angularBound hn B (smoothTraceFlatDegree_symmetric hn hA hEll S)
      (smoothTraceFlatDegree_finite hA hEll S)
  have hΓ' (i a b : I dim) : |Γ i a b| ≤ D := by
    dsimp only [Γ,traceCoordinateConnectionScalar]
    rw [abs_mul,show |-(1/2:ℝ)| = 1/2 by norm_num]
    exact (mul_le_mul_of_nonneg_left (hΓ i a b) (by norm_num)).trans (by linarith)
  have hPot (i : I dim) : SmoothTraceAngularBound hn 1 (T*β) (Pot i+W i) := by
    have hRot (a b : I dim) : SmoothTraceAngularBound hn 1 (D*(2*(dim:ℝ)))
        (Γ i a b • smoothSphereTraceRotation a b) :=
      ((smoothTraceRotation_angularBound hn a b).const_smul (Γ i a b)).enlarge
        (mul_le_mul_of_nonneg_right (hΓ' i a b) (by positivity))
    have hSum {F' : I dim → Module.End ℝ (SmoothSphereTrace dim)} {s : ℝ}
        (h : ∀ a,SmoothTraceAngularBound hn 1 s (F' a)) :
        SmoothTraceAngularBound hn 1 ((dim:ℝ)*s) (∑ a,F' a) := by
      intro j k hjk w
      unfold traceOrderNorm
      simp only [LinearMap.sum_apply,map_sum]
      refine (norm_sum_le _ _).trans ?_
      have h' := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => h a j k hjk w)
      refine h'.trans_eq ?_
      simp only [traceOrderNorm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc]
    have hA := hSum (fun a => hSum (hRot a))
    have hf := (hB.const_smul (f i)).enlarge
      (show |f i| * 1 ≤ D*β by simpa only [mul_one] using hl i)
    refine ((hA.add hf).add (hW i)).enlarge ?_
    dsimp only [T]
    have hh := mul_le_mul_of_nonneg_left hβ (show 0 ≤ (dim:ℝ)^2*(D*(2*(dim:ℝ)))+U by positivity)
    nlinarith only [hh]
  refine ⟨L,Q,fun i => (hOne.const_smul (c i)).enlarge ?_,?_,?_⟩
  · rw [mul_one]
    exact (hc i).trans (mul_le_mul_of_nonneg_right hC₁ (sq_nonneg _))
  · have hEach (i : I dim) : SmoothTraceAngularBound hn 1 (D*T*β⁻¹)
        (c i • (Pot i+W i)) := by
      refine ((hPot i).const_smul (c i)).enlarge (le_trans (mul_le_mul_of_nonneg_right (hc i) (by positivity)) ?_)
      apply le_of_eq
      field_simp
    intro i j hij w
    unfold Q traceOrderNorm
    simp only [LinearMap.sum_apply,map_sum]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum (fun k _ => hEach k i j hij w)).trans ?_
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have h := mul_le_mul_of_nonneg_right hC₂ (inv_nonneg.mpr hβ₀.le)
    have hw : 0 ≤ traceOrderNorm hn j w := norm_nonneg _
    simpa only [traceOrderNorm,mul_assoc] using mul_le_mul_of_nonneg_right h hw
  · intro w
    let Bx := smoothSupportedTraceFiberL (Y:=Y) x
    have hK' (i : I dim) :
        Bx (supportedCoordinateModelPotential hY hg hK he hA hEll S hlog i w) = Pot i (Bx w) := by
      simp only [Bx,Pot,Γ,f,B,supportedCoordinateModelPotential,LinearMap.add_apply,LinearMap.sum_apply,
        map_add,map_sum,Module.End.mul_apply,smoothSupportedTraceBaseMul_fiber,
        smoothSupportedTraceFiberAction_fiber,LinearMap.smul_apply]
    unfold movingTraceDriftRemainder
    simp only [LinearMap.sum_apply,map_sum,Module.End.mul_apply,supportedCoordinateTraceDrift,
      smoothSupportedTraceBaseMul_fiber,supportedCoordinateModelDerivative_eq_base_add_potential,
      LinearMap.add_apply,map_add]
    have hW' (i : I dim) :
        Bx (actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF i w)+
          Bx (actualSupportedAffine hY F hF i w) = W i (Bx w) := by
      simpa only [LinearMap.add_apply,map_add] using
        actualSupportedGaussLowerVelocity_fiber hY hg he hr hr₀ hlog hA hEll S F hC hF hn hx i w
    simp only [← smul_add]
    change (∑ i,c i • ((Bx (smoothSupportedTraceBaseDiff (axis i) w)+
      Bx (supportedCoordinateModelPotential hY hg hK he hA hEll S hlog i w))+
      (Bx (actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF i w)+
        Bx (actualSupportedAffine hY F hF i w)))) = _
    simp only [hK',hW']
    simp only [L,Q,W,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.one_apply,LinearMap.add_apply,
      smul_add,Finset.sum_add_distrib]
    abel

end CalderonN
