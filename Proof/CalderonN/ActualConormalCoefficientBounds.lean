module

public import Proof.CalderonN.SmoothSupportedTraceCoefficientBounds
public import Proof.CalderonN.ActualGaussConormalFirstBaseBounds
public import Proof.CalderonN.SmoothTraceRotationBracket

import Mathlib.Tactic

/-! The flat degree, rotations, and the single actual conormal
remainder are order-one coefficients on the normalized chart scale. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

theorem smoothTraceAngularBound_zero (hn : 3 ≤ dim) (k : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    SmoothTraceAngularBound hn k C (0 : Module.End ℝ (SmoothSphereTrace dim)) := by
  intro i j hij u
  rw [LinearMap.zero_apply]
  simpa only [traceOrderNorm,map_zero,norm_zero] using mul_nonneg hC (norm_nonneg (smoothSphereTraceSobolev hn _ (traceOrderExponent_le j) u))

theorem smoothTraceIdentity_commutatorBounds (hn : 3 ≤ dim) (B : Module.End ℝ (SmoothSphereTrace dim)) :
    SmoothTraceCommutatorBounds hn B 0 1 (1 : Module.End ℝ (SmoothSphereTrace dim)) := by
  refine ⟨zero_le_one,?_,?_,?_⟩
  · intro i j hij u
    have he : i = j := Fin.ext (by omega)
    rw [Module.End.one_apply,he,one_mul]
  · rw [mul_one,one_mul]
    rw [show B-B = 0 by abel]
    exact smoothTraceAngularBound_zero hn 0 zero_le_one
  · intro i j
    rw [smoothTraceAngularComm,mul_one,one_mul]
    rw [show smoothSphereTraceRotation i j-smoothSphereTraceRotation i j = 0 by abel]
    exact smoothTraceAngularBound_zero hn 0 zero_le_one

variable (hn : 3 ≤ dim) {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
  {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
  {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)

theorem smoothTraceFlatDegree_commutatorBounds :
    let B := smoothTraceFlatDegree hA hEll S
    SmoothTraceCommutatorBounds hn B 1 1 B := by
  dsimp only
  let B := smoothTraceFlatDegree hA hEll S
  refine ⟨zero_le_one,smoothTraceDegree_angularBound hn B (smoothTraceFlatDegree_symmetric hn hA hEll S)
    (smoothTraceFlatDegree_finite hA hEll S),?_,?_⟩
  · rw [show B*B-B*B = 0 by abel]
    exact smoothTraceAngularBound_zero hn 1 zero_le_one
  · intro i j
    change SmoothTraceAngularBound hn 1 1 (smoothSphereTraceRotation i j*B-B*smoothSphereTraceRotation i j)
    have hComm : B*smoothSphereTraceRotation i j = smoothSphereTraceRotation i j*B :=
      smoothTraceFlatDegree_commutes_rotation hA hEll S i j
    rw [← hComm,show B*smoothSphereTraceRotation i j-B*smoothSphereTraceRotation i j = 0 by abel]
    exact smoothTraceAngularBound_zero hn 1 zero_le_one

theorem smoothTraceRotation_commutatorBounds (i j : I dim) :
    SmoothTraceCommutatorBounds hn (smoothTraceFlatDegree hA hEll S) 1 (8*(dim:ℝ)) (smoothSphereTraceRotation i j) := by
  have hC : 0 ≤ 8*(dim:ℝ) := by positivity
  refine ⟨hC,(smoothTraceRotation_angularBound hn i j).enlarge (by nlinarith only [show 0 ≤ (dim:ℝ) by positivity] : (2*(dim:ℝ)) ≤ 8*(dim:ℝ)),?_,
    fun a b => smoothTraceRotation_comm_rotation_bound hn a b i j⟩
  rw [smoothTraceFlatDegree_commutes_rotation hA hEll S i j]
  rw [show smoothSphereTraceRotation i j*smoothTraceFlatDegree hA hEll S-
    smoothSphereTraceRotation i j*smoothTraceFlatDegree hA hEll S = 0 by abel]
  exact smoothTraceAngularBound_zero hn 1 hC

theorem uniform_actualGauss_scaledConormal_coefficientBounds
    {Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y)) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 6 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i,d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ (F : ∀ x ∈ Y,ActualGaussFiberData d x)
        (hF : SmoothSupportedTraceFiberRegular Y (actualGaussScaledConormalFamily F)),
        (∀ x (hx : x ∈ Y),∀ z ∈ ball (0:X dim) 1,((F x hx).coefficient z).IsSymm) →
        ∀ x ∈ Y, SmoothSupportedTraceCoefficientBounds hn (smoothTraceFlatDegree hA hEll S) hY x
          (beta d.γ d.radius x) 1 C (actualGaussScaledConormalFamily F) hF := by
  obtain ⟨η₀,C₀,hη₀,hC₀,hAng⟩ := uniform_actualGauss_conormal_angularBounds hn hY hΩ (by omega : 5 ≤ m)
    K ρ c₀ M Cj hK hρ
  obtain ⟨η₁,C₁,hη₁,hC₁,hD⟩ := uniform_actualGauss_scaledConormal_first_base_angularBounds_on_unit_directions
    hn hY hΩ hYc hSub hm K ρ c₀ M Cj hK hρ
  let C := C₀+C₁
  refine ⟨min η₀ η₁,C,lt_min hη₀ hη₁,add_nonneg hC₀ hC₁,?_⟩
  intro floor hf ε he hs d hd hFrame F hF hSym x hx
  have hB : (F x hx).flatDegree = smoothTraceFlatDegree hA hEll S :=
    smoothTraceFlatDegree_eq hn (F x hx).smoothCoefficient hA (F x hx).ellipticCoefficient hEll (F x hx).solve S
  obtain ⟨_,hR,hRot,hBR⟩ := hAng floor hf ε he (hs.trans (min_le_left _ _)) d hd x hx (F x hx)
  constructor
  · rw [actualGaussScaledConormalFamily,dite_eq_left hx]
    refine (show SmoothTraceCommutatorBounds hn (smoothTraceFlatDegree hA hEll S) 1 C₀ _
      from ⟨hC₀,hR,?_ ,hRot⟩).enlarge (le_add_of_nonneg_right hC₁)
    rwa [hB] at hBR
  · intro a ha
    exact (hD floor hf ε he (hs.trans (min_le_right _ _)) d hd hFrame F hF hSym x hx a ha).enlarge
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₀) (Real.sqrt_nonneg _))

end CalderonN
