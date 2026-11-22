module

public import Proof.CalderonN.NormalizedAngularFluxBudgets
public import Proof.CalderonN.FiniteDoubleConormalTrace

import Proof.CalderonN.ActualAngularRadialWeights
import Proof.CalderonN.FiniteHarmonicH2Lift
import Proof.CalderonN.PolynomialConormalFirstVariation
import Mathlib.Tactic

/-! Both Sobolev endpoints of the actual double conormal rotation
commutator, for one common smooth trace operator. -/

public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 8400000
set_option maxSynthPendingDepth 29
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon SphereHarmonic GreenRadialTrace SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem norm_finiteHarmonicSmooth_ballH2_le (f : HarmonicFiniteCoefficients dim) :
    ‖smoothBallSobolev 2 (harmonicFiniteSmooth f)‖ ≤
      Real.sqrt (((dim:ℝ)+3)*unitSphereArea dim)*‖harmonicBoundaryFiniteL (3/2:ℝ) f‖ := by
  let p (k : ℕ) := harmonicPolynomialRepresentativeL k (f k)
  classical
  have h := norm_sq_all_finite_harmonic_H2_lift_le f.support p
    (fun k _ => harmonicPolynomialRepresentative_mem k (f k))
  rw [polynomialBallSobolevL_apply] at h
  change ‖smoothBallSobolev 2 (harmonicFiniteSmooth f)‖^2 ≤ _ at h
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have hArea : 0 < unitSphereArea dim := unitSphereArea_pos
  rw [mul_pow,Real.sq_sqrt (mul_nonneg (by positivity) hArea.le),harmonicBoundaryFiniteL_eq_sum,norm_sq_finite_boundary_sum]
  simpa only [p,polynomialSphereL2_harmonicPolynomialRepresentative,besselWeight_three_halves_sq,
    Submodule.coe_norm] using h

theorem uniform_actual_doubleAngular_conormal_endpoints (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 5 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C_H C_L : ℝ, 0 < η ∧ 0 ≤ C_H ∧ 0 ≤ C_L ∧
      ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
        Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
        let r := d.radius y
        let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
        let ell := firstDensityCenterLinear d y
        ∃ (A : X dim → Mat dim) (hA : ContDiff ℝ ∞ A)
          (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)
          (T : Module.End ℝ (SmoothSphereTrace dim)),
          EqOn A a (ball (0 : X dim) (5/4)) ∧ SmoothTraceAdjoint hn T T ∧
          (∀ f, T (smoothSphereTrace f) = smoothSphereTrace ((S f).remainder hA r)) ∧
          ∀ (i j k l : Fin dim) (f : HarmonicFiniteCoefficients dim),
            let p := smoothTraceAngularComm k l (smoothTraceAngularComm i j T) (finiteHarmonicSmoothTraceL f)
            ‖smoothSphereTraceSobolev hn (1/2 : ℝ) (by norm_num) p‖ ≤
              C_H*r^2*‖harmonicBoundaryFiniteL (3/2 : ℝ) f‖ ∧
            ‖smoothSphereTraceSobolev hn (-(1/2) : ℝ) (by norm_num) p‖ ≤
              C_L*r^2*‖harmonicBoundaryFiniteL (1/2 : ℝ) f‖ := by
  have h₂ : 2 ≤ dim := by omega
  obtain ⟨F₀,η,C,G,hη,hC,hG,hF₀,hI₀H,hI₀L,hBudget⟩ :=
    uniform_normalized_angularFlux_budgets (Y:=Y) h₂ hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηW,_,hηW,_,hWeights⟩ :=
    uniform_actual_angular_radial_weights (Y:=Y) h₂ hΩ (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨B_H,B_L,hB_H,hB_L,hEnds⟩ := doubleAngularConormal_remainder_endpoints hn C G hC hG
  let C_H := B_H*Real.sqrt (((dim:ℝ)+3)*unitSphereArea dim)
  let C_L := B_L*unitSphereArea dim
  have hArea : 0 < unitSphereArea dim := unitSphereArea_pos
  refine ⟨min η ηW,C_H,C_L,lt_min hη hηW,by dsimp [C_H]; positivity,by dsimp [C_L]; positivity,?_⟩
  intro floor hf ε he hs d hd y hy
  dsimp only
  let r := d.radius y
  let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
  let ell := firstDensityCenterLinear d y
  obtain ⟨F,lo,hi,hr,hr₁,hFA,hEll,hSym,hIH,hIL,hA_G,hD,hAng⟩ :=
    hBudget floor hf ε he (hs.trans (min_le_left _ _)) d hd y hy
  let A := coefficientMatrixField 2 F
  let hA := contDiff_coefficientMatrixField 2 F
  obtain ⟨_,W,_,_,hW,_,_,_⟩ :=
    hWeights floor hf ε he (hs.trans (min_le_right _ _)) d hd y hy A hA hFA
  let S (f : SmoothData dim) := Classical.choice (exists_conormalTaylorSolutions_of_extension F F₀ hF₀
    (fun _ _ => rfl) hEll ell f)
  let R := smoothSphereTaylorResponses hA hEll S
  let A' := (LinearMap.fst ℝ _ _).comp R
  let B := (LinearMap.fst ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp R)
  let Q := (LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp R)
  let T := smoothSphereTraceMul W*A'-B-r • (smoothSphereTraceMul ⟨ell,ell.contDiff⟩*B+Q)
  have hT (p : SmoothData dim) :
      T (smoothSphereTrace p) = smoothSphereTrace ((S p).remainder hA r) :=
    (smoothSphereTaylorResponse_remainder hA hEll S W hW r p).symm
  refine ⟨A,hA,S,T,hFA,smoothSphereTrace_remainder_symmetric hn hA hEll hSym S W hW r,hT,?_⟩
  intro i j k l f
  let J₁ := finiteHarmonicRotationL i j
  let J₂ := finiteHarmonicRotationL k l
  let b (g : HarmonicFiniteCoefficients dim) := (S (harmonicFiniteSmooth g)).actual
  let u := harmonicFiniteSmooth f
  let ell₂ := (ell.comp (ballRotationGeneratorL i j)).comp (ballRotationGeneratorL k l)
  let q := harmonicFiniteDriftVariationSmooth ell₂ f
  let p := smoothTraceAngularComm k l (smoothTraceAngularComm i j T) (finiteHarmonicSmoothTraceL f)
  have hB_T (g : HarmonicFiniteCoefficients dim) :
      EqOn (b g).1 (harmonicFiniteSmooth g).1 (standardSphere dim) := (S (harmonicFiniteSmooth g)).actualTrace
  have hB_D (g : HarmonicFiniteCoefficients dim) :
      EqOn (negativeBallDivergence A (b g).1) 0 (ball (0 : X dim) 1) := (S (harmonicFiniteSmooth g)).actualEquation
  have hB₁ : EqOn (b (J₁ f)).1 (sphereRotationDerivative i j u.1) (standardSphere dim) := by
    rw [← harmonicFiniteSmooth_rotation]
    exact hB_T (J₁ f)
  have hB₂ : EqOn (b (J₂ f)).1 (sphereRotationDerivative k l u.1) (standardSphere dim) := by
    rw [← harmonicFiniteSmooth_rotation]
    exact hB_T (J₂ f)
  have hB₁₂ : EqOn (b (J₁ (J₂ f))).1 (sphereRotationDerivative i j (harmonicFiniteSmooth (J₂ f)).1)
      (standardSphere dim) := by
    rw [← harmonicFiniteSmooth_rotation]
    exact hB_T (J₁ (J₂ f))
  let w₁ := angularBallCorrection i j (b f) (b (J₁ f))
  let w₂ := angularBallCorrection k l (b f) (b (J₂ f))
  let w₁₂ := angularBallCorrection i j (b (J₂ f)) (b (J₁ (J₂ f)))
  have hw₁ : EqOn w₁.1 0 (standardSphere dim) := eqOn_zero_angularBallCorrection_of_trace i j _ _ u (hB_T f) hB₁
  have hw₂ : EqOn w₂.1 0 (standardSphere dim) := eqOn_zero_angularBallCorrection_of_trace k l _ _ u (hB_T f) hB₂
  have hw₁₂ : EqOn w₁₂.1 0 (standardSphere dim) :=
    eqOn_zero_angularBallCorrection_of_trace i j _ _ _ (hB_T (J₂ f)) hB₁₂
  have hw : EqOn (angularBallCorrection k l w₁ w₁₂).1 0 (standardSphere dim) := by
    apply eqOn_zero_angularBallCorrection_of_trace k l w₁ w₁₂ ⟨0,contDiff_const⟩ hw₁
    convert hw₁₂ using 1
    funext z
    simp [sphereRotationDerivative]
  obtain ⟨hA₁,hA₂,hA₁₂,hL,hR⟩ := hAng i j k l
  obtain ⟨Z,hZ,hHigh,hLow⟩ := hEnds i j k l hA (b f) (b (J₁ f)) (b (J₂ f)) (b (J₁ (J₂ f))) u q ell₂ r
    hr.le hr₁ (hB_D f) (hB_D (J₁ f)) (hB_D (J₂ f)) (hB_D (J₁ (J₂ f)))
    (fun z _ => negativeBallDivergence_flat_harmonicFiniteSmooth f z)
    (fun z _ => negativeBallDivergence_flat_harmonicFiniteDriftVariation ell₂ f z)
    (hB_T f) hw₁ hw₂ hw (harmonicFiniteDriftVariationSmooth_trace ell₂ f)
    hA_G hD hA₁ hA₂ hA₁₂ hL hR hIH hI₀H hIL hI₀L
  have hpZ : p = smoothSphereTrace Z := by
    apply Subtype.ext
    funext z
    have hId := finiteSmoothTrace_doubleAngularComm_remainder hA hEll S W hW r i j k l f z
    change p.1 z = _ at hId
    rw [hId,smoothSphereTrace_apply,hZ]
    have hc (x : X dim) :
        (firstConormalDataL ell₂ f).1 x =
          smoothBallConormal (fun z => ell₂ z • (1 : Mat dim)) u.1 x+
            smoothBallConormal (fun _ => (1 : Mat dim)) q.1 x := by
      rw [firstConormalDataL_apply]
      have hFlat : smoothBallConormal (fun _ => (1 : Mat dim)) q.1 x = fderiv ℝ q.1 x x := by
        simpa only [smoothBallConormal,one_smul,one_mul] using inner_smoothBallFlux_scalar (fun _ => 1) q.1 x
      rw [hFlat,smoothBallConormal,inner_smoothBallFlux_scalar]
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    rw [show (firstConormalDataL ((ell.comp (ballRotationGeneratorL i j)).comp (ballRotationGeneratorL k l)) f).1
      (z : X dim) = _ from hc z]
    rfl
  change ‖smoothSphereTraceSobolev hn (1/2 : ℝ) (by norm_num) p‖ ≤ _ ∧
    ‖smoothSphereTraceSobolev hn (-(1/2) : ℝ) (by norm_num) p‖ ≤ _
  rw [hpZ,smoothSphereTraceSobolev_apply,smoothSphereTraceSobolev_apply]
  refine ⟨hHigh.trans ((mul_le_mul_of_nonneg_left (norm_finiteHarmonicSmooth_ballH2_le f)
    (by positivity)).trans_eq (by dsimp [C_H]; ring)),?_⟩
  apply norm_smoothBoundarySobolev_le_of_finite_tests hn (1/2 : ℝ) (by norm_num) (by norm_num)
  · positivity
  · intro g
    have h₁ : ‖smoothSobolev u‖ ≤ Real.sqrt (unitSphereArea dim)*‖harmonicBoundaryFiniteL (1/2 : ℝ) f‖ :=
      (harmonicFirstOrderLift_finite_smooth f) ▸ norm_harmonicFirstOrderLift_le _
    have h₂' : ‖smoothSobolev (harmonicFiniteSmooth g)‖ ≤
        Real.sqrt (unitSphereArea dim)*‖harmonicBoundaryFiniteL (1/2 : ℝ) g‖ :=
      (harmonicFirstOrderLift_finite_smooth g) ▸ norm_harmonicFirstOrderLift_le _
    have hPair : |∫ z : ↥(standardSphere dim), Z.1 z*(harmonicFiniteSmooth g).1 z ∂(sphereProbability dim)| ≤
        B_L*r^2*‖smoothSobolev u‖*‖smoothSobolev (harmonicFiniteSmooth g)‖ := by
      simpa only [mul_comm] using hLow (harmonicFiniteSmooth g)
    have hLow' := (mul_le_mul (mul_le_mul_of_nonneg_left h₁ (by positivity : 0 ≤ B_L*r^2))
      h₂' (norm_nonneg _) (by positivity))
    refine (hPair.trans hLow').trans_eq ?_
    dsimp only [C_L]
    calc
      _ = B_L*r^2*(Real.sqrt (unitSphereArea dim))^2*
          ‖harmonicBoundaryFiniteL (1/2:ℝ) f‖*‖harmonicBoundaryFiniteL (1/2:ℝ) g‖ := by ring
      _ = _ := by rw [Real.sq_sqrt hArea.le]; ring

end CalderonN
