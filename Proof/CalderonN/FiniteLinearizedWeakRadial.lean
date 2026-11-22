module

public import Proof.CalderonN.FiniteLinearizedConormal
public import Proof.CalderonN.LinearizedRadialWeightBounds
public import Proof.CalderonN.ActualAngularRadialWeights
public import Proof.CalderonN.ActualFiniteWeakRadialTaylor

import Proof.CalderonN.FixedBallFluxUnique
import Proof.CalderonN.FixedBallMetricEllipticity
import Mathlib.Tactic

/-! Gauss' scalar weight converts the differentiated conormal estimate
to the actual radial commutator in negative half order. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Gradient Matrix.Norms.Elementwise
set_option maxHeartbeats 4100000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem uniform_finite_linearized_weak_radial (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (P₀ Q₀ : ℝ) (hP₀ : 0 ≤ P₀) (hQ₀ : 0 ≤ Q₀) :
    ∃ η H B : ℝ, 0 < η ∧ 0 ≤ H ∧ 0 ≤ B ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let r := d.radius y
      let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
      ∃ F : X dim → Mat dim, ContDiff ℝ ∞ F ∧
        EqOn F a (ball (0 : X dim) (5/4)) ∧
        (∀ z ∈ closedBall (0 : X dim) 1, (F z).PosDef) ∧
        ∀ (ellθ : X dim →L[ℝ] ℝ) (Aθ : X dim → Mat dim),
          ContDiff ℝ ∞ Aθ → ‖ellθ‖ ≤ 2*P₀ →
          (∀ z ∈ standardSphere dim, IsRadialRow z (Aθ z)) →
          (∀ z ∈ closedBall (0 : X dim) 1, let R := Aθ-r • (fun z => ellθ z • (1 : Mat dim))
            ‖R z‖ ≤ Q₀*r^2 ∧ ‖fderiv ℝ R z‖ ≤ Q₀*r^2) →
        ∀ f : HarmonicFiniteCoefficients dim,
          let u := harmonicFiniteSmooth f
          let qθ := harmonicFiniteDriftVariationSmooth ellθ f
          ∃ b w e R : SmoothData dim,
            EqOn b.1 u.1 (standardSphere dim) ∧ EqOn w.1 0 (standardSphere dim) ∧
            EqOn (negativeBallDivergence a b.1) 0 (ball (0 : X dim) 1) ∧
            (∀ z ∈ ball (0 : X dim) 1,
              negativeBallDivergence a w.1 z = -negativeBallDivergence Aθ b.1 z) ∧
            (∀ z, e.1 z = w.1 z-r*qθ.1 z) ∧
            ‖smoothBallSobolev 2 e‖ ≤ H*r^2*‖smoothBallSobolev 2 u‖ ∧
            (∀ z, R.1 z = fderiv ℝ w.1 z z-r*fderiv ℝ qθ.1 z z) ∧
            ‖smoothBoundarySobolev hn (-(1/2 : ℝ)) (by norm_num) R‖ ≤
              B*r^2*‖harmonicBoundaryFiniteL (1/2 : ℝ) f‖ := by
  obtain ⟨η,H,A,hη,hH,hA,hCon⟩ := uniform_finite_linearized_conormal (Y:=Y)
    hn hΩ hm K ρ c₀ M Cj hK hρ P₀ Q₀ hP₀ hQ₀
  obtain ⟨ηW,C,hηW,hC,hWeights⟩ := uniform_actual_angular_radial_weights (Y := Y)
    (by omega : 2 ≤ dim) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηR,C₁,hηR,hC₁,hRad⟩ := uniform_actual_finite_weak_radial_taylor (Y := Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηL,P,hηL,hP,hEll⟩ := uniform_actual_radial_weight_remainder (Y := Y)
    (by omega : 2 ≤ dim) hΩ hm K ρ c₀ M Cj hK hρ
  let T := 2*Real.sqrt ((dim : ℝ)+3)
  let D₀ := (dim : ℝ)^2
  let D₁ := (1+T)*D₀
  let B₁ := C₁+D₁*P
  let J := 3*(dim : ℝ)^2*Q₀
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  let B := T*C*(A+T*J*D₀+T*(2*P₀+J)*B₁+T*C*(D₁*(2*P₀)))
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hD₀ : 0 ≤ D₀ := sq_nonneg _
  have hD₁ : 0 ≤ D₁ := by dsimp only [D₁]; positivity
  have hB₁ : 0 ≤ B₁ := by dsimp only [B₁]; positivity
  refine ⟨min (min η ηW) (min (min ηR ηL) 1),H,B,
    lt_min (lt_min hη hηW) (lt_min (lt_min hηR hηL) zero_lt_one),hH,by dsimp only [B,J]; positivity,?_⟩
  intro floor hf ε hε hs d hd y hy
  dsimp only
  let r := d.radius y
  let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
  let ell := firstDensityCenterLinear d y
  let S := smoothBoundarySobolev hn (-(1/2 : ℝ)) (by norm_num)
  let L := harmonicBoundaryFiniteL (dim := dim) (1/2 : ℝ)
  obtain ⟨F,hF,hFa,hFpos,hResp⟩ := hCon floor hf ε hε (hs.trans ((min_le_left _ _).trans (min_le_left _ _))) d hd y hy
  obtain ⟨hPos,W,D,WI,hW,hWD,hVInv,_⟩ := hWeights floor hf ε hε
    (hs.trans ((min_le_left _ _).trans (min_le_right _ _))) d hd y hy F hF hFa
  refine ⟨F,hF,hFa,hFpos,?_⟩
  intro ellθ Aθ hAθ hℓθ hRow hRem f
  let u := harmonicFiniteSmooth f
  let q := harmonicFiniteDriftVariationSmooth ell f
  let qθ := harmonicFiniteDriftVariationSmooth ellθ f
  let U := smoothBallRadialDerivative u
  let Q := smoothBallRadialDerivative q
  let Qθ := smoothBallRadialDerivative qθ
  obtain ⟨b,w,e,Cθ,hbT,hwT,hbH,hwH,he,heN,hCθ,hCθN⟩ :=
    hResp ellθ Aθ hAθ hℓθ (fun z hz => hRem z (ball_subset_closedBall hz)) f
  obtain ⟨b₀,R₀,hb₀T,hb₀H,hR₀,hR₀N⟩ := hRad floor hf ε hε
    (hs.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))) d hd y hy f
  obtain ⟨lo,hi,hFE⟩ := exists_uniformEllipticOn_fixedBall F hF.continuous hPos
  have hℓ : ‖ell‖ ≤ P := (hEll floor hf ε hε
    (hs.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))) d hd y hy).1
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hβ := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hrε : r ≤ ε := (le_mul_of_one_le_right hr.le (one_le_pow₀ hβ)).trans (hd.2.2.2.2.2 y hy).2
  have hr1 : r ≤ 1 := hrε.trans (hs.trans ((min_le_right _ _).trans (min_le_right _ _)))
  let B₀ := smoothBallRadialDerivative b
  let Bθ := smoothBallRadialDerivative w
  obtain ⟨V,E,hV,hVE,hVN⟩ := exists_linearized_radial_weights ellθ hAθ hRow r P₀ Q₀ hr hr1 hP₀ hQ₀ hℓθ hRem
  let dU : SmoothData dim := ⟨B₀.1-U.1,B₀.2.sub U.2⟩
  let asData (v : SmoothData dim) : smoothBallDataSubmodule dim := ⟨v.1,v.2⟩
  let SL := smoothBoundarySobolevLinear hn (-(1/2 : ℝ)) (by norm_num)
  have hDiff : EqOn B₀.1 (fun z => fderiv ℝ b₀.1 z z) (standardSphere dim) :=
    eqOn_radialDerivative_of_classicalNormalResponses hF hFE
      (fun z hz => hFa (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 5/4) hz)) b b₀ hbH hb₀H
      (fun z hz => (hbT hz).trans (hb₀T hz).symm)
  have hU : ‖S U‖ ≤ D₀*‖L f‖ := norm_flat_finite_radial_low_le hn f
  have hQ : ‖S Q‖ ≤ D₁*P*‖L f‖ :=
    (norm_first_finite_radial_low_le hn ell f).trans (by gcongr)
  have hQθ : ‖S Qθ‖ ≤ D₁*(2*P₀)*‖L f‖ :=
    (norm_first_finite_radial_low_le hn ellθ f).trans (by gcongr)
  have hDu : ‖S dU‖ ≤ B₁*r*‖L f‖ := by
    let v := asData R₀+r • asData Q
    have he : EqOn dU.1 v.1 (standardSphere dim) := by
      intro z hz
      change B₀.1 z-U.1 z = R₀.1 z+r*Q.1 z
      rw [hDiff hz,hR₀]
      change fderiv ℝ b₀.1 z z-fderiv ℝ u.1 z z =
        fderiv ℝ b₀.1 z z-fderiv ℝ u.1 z z-r*fderiv ℝ q.1 z z+r*fderiv ℝ q.1 z z
      ring
    rw [show S dU = S ⟨v.1,smoothBallData_contDiff v⟩ from
      smoothBoundarySobolev_eq_of_eqOn hn _ (by norm_num) dU _ he]
    change ‖SL (asData R₀+r • asData Q)‖ ≤ _
    rw [map_add,map_smul]
    change ‖S R₀+r • S Q‖ ≤ _
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    refine (add_le_add hR₀N (mul_le_mul_of_nonneg_left hQ hr.le)).trans ?_
    have he := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ C₁*r by positivity)
    have hN : C₁*r^2+r*(D₁*P) ≤ B₁*r := by dsimp only [B₁]; nlinarith only [he]
    exact (by
      rw [show C₁*r^2*‖L f‖+r*(D₁*P*‖L f‖) = (C₁*r^2+r*(D₁*P))*‖L f‖ by ring]
      exact mul_le_mul_of_nonneg_right hN (norm_nonneg _))
  let R : SmoothData dim := ⟨fun z => Bθ.1 z-r*Qθ.1 z,Bθ.2.sub (contDiff_const.mul Qθ.2)⟩
  let P₁ := smoothDataMul E U
  let P₂ := smoothDataMul V dU
  let P₃ := smoothDataMul D Qθ
  let Z' := asData Cθ-asData P₁-asData P₂-r • asData P₃
  let Z : SmoothData dim := ⟨Z'.1,smoothBallData_contDiff Z'⟩
  refine ⟨b,w,e,R,hbT,hwT,hbH,hwH,he,heN,fun _ => rfl,?_⟩
  have hEq : EqOn R.1 (smoothDataMul WI Z).1 (standardSphere dim) := by
    intro z hz
    have hc := hCθ z
    rw [hW w hz,hV b hz] at hc
    have hZ : Z.1 z = W.1 z*R.1 z := by
      change Cθ.1 z-E.1 z*U.1 z-V.1 z*(B₀.1 z-U.1 z)-r*(D.1 z*Qθ.1 z) =
        W.1 z*(Bθ.1 z-r*Qθ.1 z)
      change Cθ.1 z = W.1 z*Bθ.1 z+V.1 z*B₀.1 z-r*(ellθ z*U.1 z+Qθ.1 z) at hc
      rw [hc,hVE z,hWD z]
      ring
    change R.1 z = WI.1 z*Z.1 z
    rw [hZ,← mul_assoc,(hVInv z (sphere_subset_closedBall hz)).1,one_mul]
  change ‖S R‖ ≤ B*r^2*‖L f‖
  rw [show S R = S (smoothDataMul WI Z) from
    smoothBoundarySobolev_eq_of_eqOn hn _ (by norm_num) R _ hEq]
  have hProd (k v : SmoothData dim) (c : ℝ) (hc : 0 ≤ c)
      (hb : ∀ z ∈ closedBall (0 : X dim) 1, |k.1 z| ≤ c ∧ ‖fderiv ℝ k.1 z‖ ≤ c) :
      ‖S (smoothDataMul k v)‖ ≤ T*c*‖S v‖ := by
    apply norm_smoothBoundarySobolev_mul_negHalf_le hn k v hc
    · exact fun z hz => (hb z (ball_subset_closedBall hz)).1
    · intro z hz
      rw [gradient,LinearIsometryEquiv.norm_map]
      exact (hb z (ball_subset_closedBall hz)).2
  have h₁ : ‖S P₁‖ ≤ T*(J*r^2)*(D₀*‖L f‖) :=
    (hProd E U _ (by positivity) (fun z hz => ⟨(hVN z hz).2.2.1,(hVN z hz).2.2.2⟩)).trans
      (mul_le_mul_of_nonneg_left hU (by positivity))
  have h₂ : ‖S P₂‖ ≤ T*((2*P₀+J)*r)*(B₁*r*‖L f‖) :=
    (hProd V dU _ (by positivity) (fun z hz => ⟨(hVN z hz).1,(hVN z hz).2.1⟩)).trans
      (mul_le_mul_of_nonneg_left hDu (by positivity))
  have h₃ : ‖S P₃‖ ≤ T*(C*r)*(D₁*(2*P₀)*‖L f‖) :=
    (hProd D Qθ _ (by positivity) (fun z hz => ⟨(hVInv z hz).2.2.2.1,(hVInv z hz).2.2.2.2⟩)).trans
      (mul_le_mul_of_nonneg_left hQθ (by positivity))
  have hZn : ‖S Z‖ ≤ (A+T*J*D₀+T*(2*P₀+J)*B₁+T*C*(D₁*(2*P₀)))*r^2*‖L f‖ := by
    change ‖SL (asData Cθ-asData P₁-asData P₂-r • asData P₃)‖ ≤ _
    rw [map_sub,map_sub,map_sub,map_smul]
    change ‖S Cθ-S P₁-S P₂-r • S P₃‖ ≤ _
    refine ((norm_sub_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)).trans ?_
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    refine (add_le_add (add_le_add (add_le_add hCθN h₁) h₂) (mul_le_mul_of_nonneg_left h₃ hr.le)).trans_eq ?_
    ring
  exact ((hProd WI Z C hC (fun z hz => ⟨(hVInv z hz).2.1,(hVInv z hz).2.2.1⟩)).trans
    (mul_le_mul_of_nonneg_left hZn (by positivity))).trans_eq (by dsimp only [B]; ring)

end CalderonN
