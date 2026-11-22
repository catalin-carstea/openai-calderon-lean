module

public import Proof.CalderonN.ActualLowerVelocityCoefficientBounds
public import Proof.CalderonN.ActualConormalCoefficientBounds
public import Proof.CalderonN.ActualRadialMultiplierBounds
public import Proof.CalderonN.ActualTranslationMultiplierBounds
public import Proof.CalderonN.PhysicalRadiusFirstDerivativeBounds

import Mathlib.Tactic

/-! Apply the joint coefficient estimates to the actual lower-order
velocity and the affine coefficient in the physical trace expansion. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

theorem uniform_actual_lowerVelocity_coefficient_bounds (hn : 3 ≤ dim)
    {Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y)) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 8 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1,∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i,d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ (F : ∀ x ∈ Y,ActualGaussFiberData d x)
        (hR : SmoothSupportedTraceFiberRegular Y (actualGaussScaledConormalFamily F))
        (hSym : ∀ x (hx : x ∈ Y),∀ z ∈ ball (0:X dim) 1,((F x hx).coefficient z).IsSymm)
        (i : I dim) (hW : SmoothSupportedTraceFiberRegular Y (actualGaussLowerVelocityFamily F i))
        (hF : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussAffineFamily F i)),
        ∀ x ∈ Y,
          SmoothSupportedTraceCoefficientBounds hn (smoothTraceFlatDegree hA hEll S) hY x
            (beta d.γ d.radius x) 1 C (actualGaussLowerVelocityFamily F i) hW ∧
          SupportedTraceFiberBound hn x 0 C (actualSupportedAffine hY F hF i) := by
  let B := smoothTraceFlatDegree hA hEll S
  have hB := smoothTraceFlatDegree_symmetric hn hA hEll S
  have hFin := smoothTraceFlatDegree_finite hA hEll S
  obtain ⟨η₀,C₀,hη₀,hC₀,hCR⟩ := uniform_actualGauss_scaledConormal_coefficientBounds
    hn hA hEll S hY hΩ hYc hSub (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨η₁,C₁,hη₁,hC₁,hCH⟩ := uniform_actual_radialMultiplier_bounds
    hn hY hΩ hYc hSub hm K ρ c₀ M Cj hK hρ B hB hFin
  obtain ⟨η₂,C₂,hη₂,hC₂,hCV⟩ := uniform_actual_centerCorrectionMultiplier_bounds
    hn hY hΩ hYc hSub hm K ρ c₀ M Cj hK hρ B hB hFin
  obtain ⟨C₃,hC₃,hCM⟩ := uniform_actual_translationMultiplier_bounds
    hn hY hΩ hSub (by omega) K ρ c₀ M Cj (zero_lt_one.trans_le hK) B hB hFin
  obtain ⟨C₄,hC₄,hCb⟩ := uniform_actual_radius_firstDerivative_bounds
    hY hΩ hSub (by omega) K ρ c₀ M Cj (zero_lt_one.trans_le hK)
  let C := 1+(C₀+C₁+C₂+C₃+2*C₄+8*(dim:ℝ))
  have hC : 1 ≤ C := le_add_of_nonneg_right (by have := zero_le_one.trans hC₄; positivity)
  obtain ⟨D₀,hD₀,hWV⟩ := actualGaussLowerVelocity_bounds_of_factors (Y:=Y) hn hY C hC
  let η := min 1 (min η₀ (min η₁ η₂))
  let D := D₀+C^2
  refine ⟨η,D,lt_min zero_lt_one (lt_min hη₀ (lt_min hη₁ hη₂)),by dsimp only [D]; positivity,?_⟩
  intro floor hFloor ε hε hs d hd hFrame F hR hSym i hW hF x hx
  let β := beta d.γ d.radius x
  have hβ := zero_le_one.trans (hFloor.trans (hd.2.2.2.2.1.2 x hx).2.1)
  let r := d.radius
  let b (y : X dim) := fderiv ℝ r y (axis i)
  let hb := (hd.2.2.2.2.1.1.fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply
    (show ContDiffOn ℝ ∞ (fun _ : X dim => axis i) Y from contDiffOn_const)
  have hs' := hs.trans (min_le_right _ _)
  obtain ⟨hL,hH,hH₁,hRad⟩ := hCH floor hFloor ε hε (hs'.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd hFrame F
  obtain ⟨hN,hV,hVel⟩ := hCV floor hFloor ε hε (hs'.trans ((min_le_right _ _).trans (min_le_right _ _))) d hd hFrame F i
  obtain ⟨hM,hTr⟩ := hCM floor hFloor ε d hd hFrame i
  obtain ⟨hr₀,hr₁,hb₀,hb₁⟩ := hCb floor hFloor ε (hs.trans (min_le_left _ _)) d hd x hx
  obtain ⟨bL,bH,bH₁⟩ := hRad x hx
  obtain ⟨bN,bV⟩ := hVel x hx
  let M₀ := supportedSphereMultiplierFamily (fun y (_ : y ∈ Y) => actualTranslationMultiplierDatum d i y)
  let M₁ (y : X dim) := M₀ y+b y • (1 : Module.End ℝ (SmoothSphereTrace dim))
  let hb₁reg := smoothSupportedTraceFiberRegular_smul hY hb
  let hM₁ := hM.add hb₁reg
  let hI := smoothSupportedTraceFiberRegular_smul hY (f:=fun _ => 1) contDiffOn_const
  have hI₀ : SmoothSupportedTraceFiberRegular Y (fun _ => (1 : Module.End ℝ (SmoothSphereTrace dim))) := by
    simpa only [one_smul] using hI
  have hBI := SmoothSupportedTraceCoefficientBounds.const (hY:=hY) (hT:=hI₀) (smoothTraceIdentity_commutatorBounds hn B) hx hβ
  have hbs := hBI.base_smul hx hβ b hb (zero_le_one.trans hC₄) (hb₀ i) (hb₁ i)
  have bM₁ : SmoothSupportedTraceCoefficientBounds hn B hY x β 0 C M₁ hM₁ :=
    ((hTr x hx).add hbs hx).enlarge hβ (by dsimp only [C]; simpa only [mul_one] using
      (show C₃+(C₄+C₄) ≤ 1+(C₀+C₁+C₂+C₃+2*C₄+8*(dim:ℝ)) by linarith [show 0 ≤ (dim:ℝ) by positivity]))
  have hbB : SmoothSupportedTraceFiberRegular Y (fun _ => B) :=
    smoothSupportedTraceFiberRegular_flatDegree hA hEll S Y
  have hbRot (a b : I dim) : SmoothSupportedTraceFiberRegular Y (fun _ => smoothSphereTraceRotation a b) :=
    smoothSupportedTraceFiberRegular_rotation a b
  have bB := SmoothSupportedTraceCoefficientBounds.const (hY:=hY) (hT:=hbB) (smoothTraceFlatDegree_commutatorBounds hn hA hEll S) hx hβ
  have bRot (a b : I dim) := SmoothSupportedTraceCoefficientBounds.const (hY:=hY) (hT:=hbRot a b)
    (smoothTraceRotation_commutatorBounds hn hA hEll S a b) hx hβ
  have bR := hCR floor hFloor ε hε (hs'.trans (min_le_left _ _)) d hd hFrame F hR hSym x hx
  let L := supportedSphereMultiplierFamily (fun y (_ : y ∈ Y) => actualDensityLinearDatum d y)
  let H := supportedSphereMultiplierFamily (fun y hy => (F y hy).reciprocal)
  let H₁ := supportedSphereMultiplierFamily (actualReciprocalWeightDifferenceDatum F)
  let R := actualGaussScaledConormalFamily F
  let N := supportedSphereMultiplierFamily (fun y hy => smoothVelocityNormal ((F y hy).centerCorrection i))
  let V (a b : I dim) := supportedSphereMultiplierFamily
    (fun y hy => smoothVelocityAngular ((F y hy).centerCorrection i) a b)
  have hB' (y : X dim) (hy : y ∈ Y) : (F y hy).flatDegree = B :=
    smoothTraceFlatDegree_eq hn (F y hy).smoothCoefficient hA (F y hy).ellipticCoefficient hEll (F y hy).solve S
  have hM' (y : X dim) (hy : y ∈ Y) : M₁ y =
      ActualGaussFiberData.translationMultiplier d y i+b y • 1 := by
    simp only [M₁,M₀,supportedSphereMultiplierFamily,dite_eq_left hy,actualTranslationMultiplierDatum,
      ActualGaussFiberData.translationMultiplier]
  have hL' (y : X dim) (hy : y ∈ Y) : L y = ActualGaussFiberData.affineDensityMul d y := by
    simp only [L,supportedSphereMultiplierFamily,dite_eq_left hy,actualDensityLinearDatum,
      smoothLinearTraceDatum,ActualGaussFiberData.affineDensityMul]
  have hF' (y : X dim) (hy : y ∈ Y) : (F y hy).affineCorrection =
      (-(1/2:ℝ)) • (L y+(B*L y-L y*B)) := by
    rw [hL' y hy]
    exact (F y hy).affineCorrection_eq hn hA hEll S
  have hC₄' : C₄ ≤ C := by dsimp only [C]; linarith [show 0 ≤ (dim:ℝ) by positivity]
  have hWbound : SmoothSupportedTraceCoefficientBounds hn B hY x β 1 D₀ (actualGaussLowerVelocityFamily F i) hW := by
    apply hWV F i hW x hx β hβ B hbB hbRot (bB.enlarge hβ hC) (fun a b =>
      (bRot a b).enlarge hβ (by dsimp only [C]; linarith))
      L H H₁ R M₁ N V hL hH hH₁ hR hM₁ hN hV
      (bL.enlarge hβ (by dsimp only [C]; linarith))
      (bH.enlarge hβ (by dsimp only [C]; linarith))
      (bH₁.enlarge hβ (by dsimp only [C]; linarith))
      (bR.enlarge hβ (by dsimp only [C]; linarith)) bM₁
      (bN.enlarge hβ (by dsimp only [C]; linarith))
      (fun a b => (bV a b).enlarge hβ (by dsimp only [C]; linarith))
      hd.2.2.2.2.1.1 (hr₀.trans hC₄') (fun a ha => (hr₁ a ha).trans (mul_le_mul_of_nonneg_right hC₄' hβ))
    filter_upwards [hY.mem_nhds hx] with y hy hyY
    refine ⟨(hd.2.2.2.2.1.2 y hyY).1.ne',hB' y hyY,?_,hL' y hyY,?_,?_,?_,hM' y hyY,?_,?_⟩
    · rw [hF' y hyY]
      module
    · simp only [H,supportedSphereMultiplierFamily,dite_eq_left hyY]
    · simp only [H,H₁,supportedSphereMultiplierFamily,dite_eq_left hyY]
      ext u : 1
      apply Subtype.ext
      funext z
      simp only [actualReciprocalWeightDifferenceDatum,smoothSphereTraceMul_apply,LinearMap.smul_apply,
        LinearMap.sub_apply,Module.End.one_apply,Submodule.coe_sub,Submodule.coe_smul,Pi.sub_apply,
        Pi.smul_apply,smul_eq_mul]
      ring
    · simp only [R,actualGaussScaledConormalFamily,dite_eq_left hyY]
    · simp only [N,supportedSphereMultiplierFamily,dite_eq_left hyY]
    · intro a b
      simp only [V,supportedSphereMultiplierFamily,dite_eq_left hyY]
  have hSize : 0 ≤ C^2 := sq_nonneg _
  refine ⟨hWbound.enlarge hβ (le_add_of_nonneg_right hSize),?_⟩
  let Q := (F x hx).affineCorrection
  let Q' := (-(1/2:ℝ)) • (L x+(L x*B-B*L x))
  have hLadj : SmoothTraceAdjoint hn (L x) (L x) := supportedSphereMultiplierFamily_selfAdjoint hn _ x hx
  have hM₀adj : SmoothTraceAdjoint hn (M₀ x) (M₀ x) := supportedSphereMultiplierFamily_selfAdjoint hn _ x hx
  have hM₁adj : SmoothTraceAdjoint hn (M₁ x) (M₁ x) := by
    have hId : SmoothTraceAdjoint hn (1 : Module.End ℝ (SmoothSphereTrace dim)) 1 := by
      intro u v
      simp only [Module.End.one_apply]
    exact hM₀adj.add (hId.const_smul (b x))
  have hQadj : SmoothTraceAdjoint hn Q Q' := by
    rw [show Q = _ from hF' x hx]
    exact (hLadj.add ((hB.mul hLadj).sub (hLadj.mul hB))).const_smul _
  have hQbd : SmoothTraceAngularBound hn 0 C₁ Q := by
    rw [show Q = _ from hF' x hx]
    have hBound := (bL.angular.bound.add bL.angular.degree).const_smul (-(1/2:ℝ))
    exact hBound.enlarge (by norm_num; ring_nf; rfl)
  refine ⟨Q*M₁ x,M₁ x*Q',hQadj.mul hM₁adj,?_,?_⟩
  · have hC₁' : C₁ ≤ C := by dsimp only [C]; linarith [show 0 ≤ (dim:ℝ) by positivity]
    exact ((hQbd.enlarge hC₁').mul bM₁.angular.bound (zero_le_one.trans hC)).enlarge
      (by dsimp only [D]; rw [pow_two]; exact le_add_of_nonneg_left hD₀)
  · intro u
    rw [actualSupportedAffine,smoothSupportedTraceFiberAction_fiber,actualGaussAffineFamily,dite_eq_left hx,hM' x hx]
    change _ = (Q*(ActualGaussFiberData.translationMultiplier d x i+b x • 1)) (smoothSupportedTraceFiberL x u)
    rw [mul_add,mul_smul_comm,mul_one]

end CalderonN
