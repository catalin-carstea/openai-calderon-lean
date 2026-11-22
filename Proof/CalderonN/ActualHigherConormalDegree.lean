module

public import Proof.CalderonN.ActualDoubleAngularConormal
public import Proof.CalderonN.SmoothTraceDegreeFromRotation
public import Proof.CalderonN.SmoothTraceDualOrder

import Proof.CalderonN.ActualAngularConormalMidpoint
import Proof.CalderonN.ActualWeakAngularConormal
import Proof.CalderonN.ActualConormalSobolevTaylor
import Mathlib.Tactic

/-! The actual conormal degree commutator gains its higher endpoint
from its own rotation commutators. -/

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 8700000
set_option maxSynthPendingDepth 29
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem traceAngular_degree_comm (K B T : Module.End ℝ (SmoothSphereTrace dim))
    (hKB : K*B = B*K) :
    K*(B*T-T*B)-(B*T-T*B)*K = B*(K*T-T*K)-(K*T-T*K)*B := by
  have h₁ : K*(B*T) = B*(K*T) := by rw [← mul_assoc,hKB,mul_assoc]
  have h₂ : T*(K*B) = T*(B*K) := congrArg (T * ·) hKB
  noncomm_ring [h₁,h₂]

theorem uniform_actual_higher_conormal_degree_comm (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 5 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C_L C_H C₀ C₁ C₂ C₃ : ℝ, 0 < η ∧ 0 ≤ C_L ∧ 0 ≤ C_H ∧
      0 ≤ C₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧
      ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
        Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
        let r := d.radius y
        let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
        let ell := firstDensityCenterLinear d y
        ∃ (A : X dim → Mat dim) (hA : ContDiff ℝ ∞ A) (lo hi : ℝ)
          (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
          (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)
          (T : Module.End ℝ (SmoothSphereTrace dim)),
          EqOn A a (ball (0 : X dim) (5/4)) ∧ SmoothTraceAdjoint hn T T ∧
          (∀ f, T (smoothSphereTrace f) = smoothSphereTrace ((S f).remainder hA r)) ∧
          (∀ u, ‖smoothSphereTraceSobolev hn (-(1/2):ℝ) (by norm_num) (T u)‖ ≤
              C₀*r^2*‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) u‖ ∧
            ‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) (T u)‖ ≤
              C₁*r^2*‖smoothSphereTraceSobolev hn (3/2:ℝ) (by norm_num) u‖) ∧
          (∀ i j u, ‖smoothSphereTraceSobolev hn (-(1/2):ℝ) (by norm_num) (smoothTraceAngularComm i j T u)‖ ≤
              C₂*r^2*‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) u‖ ∧
            ‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) (smoothTraceAngularComm i j T u)‖ ≤
              C₃*r^2*‖smoothSphereTraceSobolev hn (3/2:ℝ) (by norm_num) u‖) ∧
          ∀ u, let B := smoothTraceFlatDegree hA hEll S
            ‖smoothSphereTraceSobolev hn (-(1/2):ℝ) (by norm_num) ((B*T-T*B) u)‖ ≤
              C_L*r^2*‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) u‖ ∧
            ‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) ((B*T-T*B) u)‖ ≤
              C_H*r^2*‖smoothSphereTraceSobolev hn (3/2:ℝ) (by norm_num) u‖ := by
  have h₂ : 2 ≤ dim := by omega
  obtain ⟨η₂,B₂H,B₂L,hη₂,hB₂H,hB₂L,hDouble⟩ :=
    uniform_actual_doubleAngular_conormal_endpoints (Y:=Y) hn hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨η₁,B₁,hη₁,hB₁,hSingle⟩ :=
    uniform_actual_angular_conormal_midpoint (Y:=Y) hn hΩ (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηW,_,hηW,_,hWeights⟩ :=
    uniform_actual_angular_radial_weights (Y:=Y) h₂ hΩ (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηR,C₀,hηR,hC₀,hWeakR⟩ :=
    uniform_actual_conormal_sobolev_taylor (Y:=Y) hn hΩ (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηK,C₂,hηK,hC₂,hWeakK⟩ :=
    uniform_actual_weak_angular_conormal (Y:=Y) hn hΩ (by omega) K ρ c₀ M Cj hK hρ
  let C₁ := smoothTraceRotationLiftConstant dim C₀ C₂
  let C₃ := smoothTraceRotationLiftConstant dim C₂ B₂L
  let τ := min η₂ (min η₁ ηW)
  let D₂ := (B₂L+B₂H)/2
  let D := (dim:ℝ)^4*(B₁+B₁)
  let G := (dim:ℝ)^4*(D₂+D₂)
  let C_H := Real.sqrt (2*D^2+(dim:ℝ)^2*(G+D*(2*(dim:ℝ)))^2)
  have hD₂ : 0 ≤ D₂ := by dsimp [D₂]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  refine ⟨min τ (min ηR ηK),D,C_H,C₀,C₁,C₂,C₃,
    lt_min (lt_min hη₂ (lt_min hη₁ hηW)) (lt_min hηR hηK),
    hD,Real.sqrt_nonneg _,hC₀,Real.sqrt_nonneg _,hC₂,Real.sqrt_nonneg _,?_⟩
  intro floor hf ε he hs d hd y hy
  dsimp only
  have hsτ : ε ≤ τ := hs.trans (min_le_left _ _)
  have hsR : ε ≤ ηR := hs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsK : ε ≤ ηK := hs.trans ((min_le_right _ _).trans (min_le_right _ _))
  let r := d.radius y
  let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
  let ell := firstDensityCenterLinear d y
  obtain ⟨A,hA,S,T,hFA,hSymT,hT,hDbl⟩ :=
    hDouble floor hf ε he (hsτ.trans (min_le_left _ _)) d hd y hy
  obtain ⟨hPos,W,_,_,hW,_,_,_⟩ := hWeights floor hf ε he
    (hsτ.trans ((min_le_right _ _).trans (min_le_right _ _))) d hd y hy A hA hFA
  obtain ⟨lo,hi,hEll⟩ := exists_uniformEllipticOn_fixedBall A hA.continuous hPos
  let B := smoothTraceFlatDegree hA hEll S
  let R := smoothSphereTaylorResponses hA hEll S
  let A' := (LinearMap.fst ℝ _ _).comp R
  let Q := (LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp R)
  let T₀ := smoothSphereTraceMul W*A'-B-r • (smoothSphereTraceMul ⟨ell,ell.contDiff⟩*B+Q)
  let b (g : HarmonicFiniteCoefficients dim) := (S (harmonicFiniteSmooth g)).actual
  have hT₀ : T = T₀ := by
    ext u : 1
    obtain ⟨v,rfl⟩ := smoothSphereTraceL_surjective u
    let p : SmoothData dim := ⟨v.1,smoothBallData_contDiff v⟩
    change T (smoothSphereTrace p) = T₀ (smoothSphereTrace p)
    rw [hT p]
    exact smoothSphereTaylorResponse_remainder hA hEll S W hW r p
  have hSub : ball (0 : X dim) 1 ⊆ ball (0 : X dim) (5/4) := ball_subset_ball (by norm_num)
  have hAg (z : X dim) (hz : z ∈ ball (0 : X dim) 1) : A =ᶠ[𝓝 z] a := by
    filter_upwards [isOpen_ball.mem_nhds hz] with x hx using hFA (hSub hx)
  have hB (g : HarmonicFiniteCoefficients dim) : EqOn (negativeBallDivergence a (b g).1) 0 (ball (0 : X dim) 1) := by
    intro z hz
    rw [← negativeBallDivergence_congr_germ (hAg z hz) EventuallyEq.rfl]
    exact (S (harmonicFiniteSmooth g)).actualEquation hz
  have hMatch (g : HarmonicFiniteCoefficients dim) (v : SmoothData dim)
      (hvT : EqOn v.1 (harmonicFiniteSmooth g).1 (standardSphere dim))
      (hvH : EqOn (negativeBallDivergence a v.1) 0 (ball (0 : X dim) 1)) :
      EqOn (smoothBallConormal A (b g).1) (smoothBallConormal A v.1) (standardSphere dim) := by
    have hE := eqOn_radialDerivative_of_classicalNormalResponses hA hEll (hFA.mono hSub) (b g) v
      (hB g) hvH ((S (harmonicFiniteSmooth g)).actualTrace.trans hvT.symm)
    intro z hz
    rw [hW (b g) hz,hW v hz]
    exact congrArg (W.1 z * ·) (hE hz)
  have hOne (i j : Fin dim) (f : HarmonicFiniteCoefficients dim) :
      ‖smoothSphereTraceSobolev hn 0 (by norm_num) (smoothTraceAngularComm i j T (finiteHarmonicSmoothTraceL f))‖ ≤
        (B₁*r^2)*‖harmonicBoundaryFiniteL 1 f‖ := by
    obtain ⟨u,v,E,huT,hvT,huH,hvH,hE,hEN⟩ := hSingle floor hf ε he
      (hsτ.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy A hA hFA i j f
    have hu := hMatch f u huT huH
    have hv := hMatch (finiteHarmonicRotationL i j f) v (by rw [harmonicFiniteSmooth_rotation]; exact hvT) hvH
    have hAngle := EqOn.sphereRotationDerivative hu (contDiff_smoothBallConormal hA (b f))
      (contDiff_smoothBallConormal hA u) i j
    have hTrace : smoothTraceAngularComm i j T (finiteHarmonicSmoothTraceL f) = smoothSphereTrace E := by
      apply Subtype.ext
      funext z
      have hId := finiteSmoothTrace_angularComm_remainder hA hEll S W hW r i j f z
      change (smoothTraceAngularComm i j T₀ (finiteHarmonicSmoothTraceL f)).1 z = _ at hId
      rw [hT₀,hId,smoothSphereTrace_apply]
      have hV : smoothBallConormal A (b (finiteHarmonicRotationL i j f)).1 z =
          smoothBallConormal A v.1 z := hv z.2
      have hU : sphereRotationDerivative i j (smoothBallConormal A (b f).1) z =
          sphereRotationDerivative i j (smoothBallConormal A u.1) z := hAngle z.2
      change sphereRotationDerivative i j (smoothBallConormal A (b f).1) z-
        smoothBallConormal A (b (finiteHarmonicRotationL i j f)).1 z-
          r*((firstConormalDataL (ell.comp (ballRotationGeneratorL i j)) f).1 z) = _
      rw [hU,hV,firstConormalDataL_apply]
      exact (hE z.2).symm
    rw [hTrace,smoothSphereTraceSobolev_apply,norm_smoothBoundarySobolev_zero_eq]
    exact hEN
  have hLowRFin (f : HarmonicFiniteCoefficients dim) :
      ‖smoothSphereTraceSobolev hn (-(1/2):ℝ) (by norm_num) (T (finiteHarmonicSmoothTraceL f))‖ ≤
        (C₀*r^2)*‖harmonicBoundaryFiniteL (1/2:ℝ) f‖ := by
    obtain ⟨v,E,hvT,hvH,hE,hEN⟩ := hWeakR floor hf ε he hsR d hd y hy f
    have hv := hMatch f v hvT hvH
    have hTrace : T (finiteHarmonicSmoothTraceL f) = smoothSphereTrace E := by
      apply Subtype.ext
      funext z
      have hId := finiteSmoothTrace_remainder_apply hA hEll S W hW r f
      change T₀ (finiteHarmonicSmoothTraceL f) = _ at hId
      rw [hT₀,hId,smoothSphereTrace_apply]
      have hz : z.val ∈ ball (0 : X dim) (5/4) :=
        closedBall_subset_ball (by norm_num : (1:ℝ) < 5/4) (sphere_subset_closedBall z.2)
      have hC : smoothBallConormal A v.1 z = ⟪(z : X dim),smoothBallFlux a v.1 z⟫_ℝ := by
        change ⟪(z : X dim),smoothBallFlux A v.1 z⟫_ℝ = _
        have hFlux : smoothBallFlux A v.1 z = smoothBallFlux a v.1 z := by
          ext i
          simp only [smoothBallFlux_apply,hFA hz,a,r]
        rw [hFlux]
      change smoothBallConormal A (b f).1 z-(flatRadialDataL f).1 z-r*(firstConormalDataL ell f).1 z = E.1 z
      rw [hv z.2,hC,flatRadialDataL_apply,firstConormalDataL_apply,hE z.2]
    rw [hTrace,smoothSphereTraceSobolev_apply]
    exact hEN
  have hLowKFin (i j : Fin dim) (f : HarmonicFiniteCoefficients dim) :
      ‖smoothSphereTraceSobolev hn (-(1/2):ℝ) (by norm_num)
        (smoothTraceAngularComm i j T (finiteHarmonicSmoothTraceL f))‖ ≤
        (C₂*r^2)*‖harmonicBoundaryFiniteL (1/2:ℝ) f‖ := by
    obtain ⟨A₀,hA₀,hFA₀,hData⟩ := hWeakK floor hf ε he hsK d hd y hy
    obtain ⟨u,v,E,huT,hvT,huH,hvH,hE₀,hEN⟩ := hData i j f
    have hAC (w : SmoothData dim) : EqOn (smoothBallConormal A₀ w.1)
        (smoothBallConormal A w.1) (standardSphere dim) := by
      intro z hz
      have hz' := closedBall_subset_ball (by norm_num : (1:ℝ) < 5/4) (sphere_subset_closedBall hz)
      have hFlux : smoothBallFlux A₀ w.1 z = smoothBallFlux A w.1 z := by
        ext i
        simp only [smoothBallFlux_apply,hFA₀ hz',hFA hz']
      change ⟪z,smoothBallFlux A₀ w.1 z⟫_ℝ = ⟪z,smoothBallFlux A w.1 z⟫_ℝ
      rw [hFlux]
    have hAngleA := EqOn.sphereRotationDerivative (hAC u) (contDiff_smoothBallConormal hA₀ u)
      (contDiff_smoothBallConormal hA u) i j
    have hE (z : X dim) (hz : z ∈ standardSphere dim) :
        E.1 z = sphereRotationDerivative i j (smoothBallConormal A u.1) z-
          smoothBallConormal A v.1 z-r*((ell.comp (ballRotationGeneratorL i j)) z*
           fderiv ℝ (harmonicFiniteSmooth f).1 z z+
           fderiv ℝ (harmonicFiniteDriftVariationSmooth (ell.comp (ballRotationGeneratorL i j)) f).1 z z) := by
      rw [hE₀ z,hAngleA hz,hAC v hz]
    have hu := hMatch f u huT huH
    have hv := hMatch (finiteHarmonicRotationL i j f) v (by rw [harmonicFiniteSmooth_rotation]; exact hvT) hvH
    have hAngle := EqOn.sphereRotationDerivative hu (contDiff_smoothBallConormal hA (b f))
      (contDiff_smoothBallConormal hA u) i j
    have hTrace : smoothTraceAngularComm i j T (finiteHarmonicSmoothTraceL f) = smoothSphereTrace E := by
      apply Subtype.ext
      funext z
      have hId := finiteSmoothTrace_angularComm_remainder hA hEll S W hW r i j f z
      change (smoothTraceAngularComm i j T₀ (finiteHarmonicSmoothTraceL f)).1 z = _ at hId
      rw [hT₀,hId,smoothSphereTrace_apply]
      have hV : smoothBallConormal A (b (finiteHarmonicRotationL i j f)).1 z =
          smoothBallConormal A v.1 z := hv z.2
      have hU : sphereRotationDerivative i j (smoothBallConormal A (b f).1) z =
          sphereRotationDerivative i j (smoothBallConormal A u.1) z := hAngle z.2
      change sphereRotationDerivative i j (smoothBallConormal A (b f).1) z-
        smoothBallConormal A (b (finiteHarmonicRotationL i j f)).1 z-
          r*((firstConormalDataL (ell.comp (ballRotationGeneratorL i j)) f).1 z) = _
      rw [hU,hV,firstConormalDataL_apply]
      rw [hE z z.2]
    rw [hTrace,smoothSphereTraceSobolev_apply]
    exact hEN
  have hKSym (i j : Fin dim) :
      SmoothTraceAdjoint hn (smoothTraceAngularComm i j T) (smoothTraceAngularComm i j T) :=
    SmoothTraceAdjoint.rotation_commutator_symmetric hn i j T hSymT
  have hLowR := norm_smoothTraceOperator_le_of_finite hn (1/2:ℝ) (-(1/2):ℝ)
    (by norm_num) (by norm_num) (by norm_num) T T hSymT (C₀*r^2) (by positivity) hLowRFin
  have hLowK (i j : Fin dim) := norm_smoothTraceOperator_le_of_finite hn (1/2:ℝ) (-(1/2):ℝ)
    (by norm_num) (by norm_num) (by norm_num) (smoothTraceAngularComm i j T) (smoothTraceAngularComm i j T)
    (hKSym i j) (C₂*r^2) (by positivity) (hLowKFin i j)
  have hLowKK (i j k l : Fin dim) := norm_smoothTraceOperator_le_of_finite hn (1/2:ℝ) (-(1/2):ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (smoothTraceAngularComm k l (smoothTraceAngularComm i j T)) (smoothTraceAngularComm k l (smoothTraceAngularComm i j T))
    (SmoothTraceAdjoint.rotation_commutator_symmetric hn k l _ (hKSym i j))
    (B₂L*r^2) (by positivity) (fun f => (hDbl i j k l f).2)
  have hHighR := norm_smoothTrace_halfOrderHigher_of_rotation hn T C₀ C₂ (r^2) hC₀ hC₂ (sq_nonneg _) hLowR hLowK
  have hHighK (i j : Fin dim) := norm_smoothTrace_halfOrderHigher_of_rotation hn (smoothTraceAngularComm i j T)
    C₂ B₂L (r^2) hC₂ hB₂L (sq_nonneg _) (hLowK i j) (hLowKK i j)
  have hTwo (i j k l : Fin dim) (f : HarmonicFiniteCoefficients dim) :
      ‖smoothSphereTraceSobolev hn 0 (by norm_num)
        (smoothTraceAngularComm k l (smoothTraceAngularComm i j T) (finiteHarmonicSmoothTraceL f))‖ ≤
        (D₂*r^2)*‖harmonicBoundaryFiniteL 1 f‖ := by
    have hM := norm_finite_smoothTrace_midpoint hn (smoothTraceAngularComm k l (smoothTraceAngularComm i j T))
      (B₂L*r^2) (B₂H*r^2) (by positivity) (by positivity)
      (fun g => (hDbl i j k l g).2) (fun g => (hDbl i j k l g).1) f
    refine hM.trans_eq ?_
    change ((B₂L*r^2+B₂H*r^2)/2)*‖harmonicBoundaryFiniteL 1 f‖ = D₂*r^2*‖harmonicBoundaryFiniteL 1 f‖
    have hScale : (B₂L * r^2 + B₂H * r^2) / 2 = D₂ * r^2 := by
      change (B₂L * r^2 + B₂H * r^2) / 2 = ((B₂L + B₂H) / 2) * r^2
      ring
    rw [hScale]
  have hSymB : SmoothTraceAdjoint hn B B := smoothTraceFlatDegree_symmetric hn hA hEll S
  have hBF (f : HarmonicFiniteCoefficients dim) : B (finiteHarmonicSmoothTraceL f) =
      finiteHarmonicSmoothTraceL (finiteHarmonicDegreeL f) := smoothTraceFlatDegree_finite hA hEll S f
  let D_B := B*T-T*B
  have hLow (u : SmoothSphereTrace dim) :
      ‖smoothSphereTraceSobolev hn (-(1/2):ℝ) (by norm_num) (D_B u)‖ ≤
        (D*r^2)*‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) u‖ :=
    (norm_smoothTrace_degreeComm_of_rotation hn B T hSymT hSymB hBF (B₁*r^2) (by positivity) hOne u).trans_eq
      (by dsimp [D]; ring)
  have hRot (i j : Fin dim) (u : SmoothSphereTrace dim) :
      ‖smoothSphereTraceSobolev hn (-(1/2):ℝ) (by norm_num) (smoothTraceAngularComm i j D_B u)‖ ≤
        (G*r^2)*‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) u‖ := by
    have hK : B*smoothSphereTraceRotation i j = smoothSphereTraceRotation i j*B :=
      smoothTraceFlatDegree_commutes_rotation hA hEll S i j
    change ‖smoothSphereTraceSobolev hn (-(1/2):ℝ) (by norm_num)
      ((smoothSphereTraceRotation i j*D_B-D_B*smoothSphereTraceRotation i j) u)‖ ≤ _
    change ‖smoothSphereTraceSobolev hn (-(1/2):ℝ) (by norm_num)
      ((smoothSphereTraceRotation i j*(B*T-T*B)-(B*T-T*B)*smoothSphereTraceRotation i j) u)‖ ≤ _
    rw [traceAngular_degree_comm _ B T hK.symm]
    exact (norm_smoothTrace_degreeComm_of_rotation hn B (smoothTraceAngularComm i j T)
      (SmoothTraceAdjoint.rotation_commutator_symmetric hn i j T hSymT) hSymB hBF
      (D₂*r^2) (by positivity) (hTwo i j) u).trans_eq (by dsimp [G]; ring)
  refine ⟨A,hA,lo,hi,hEll,S,T,hFA,hSymT,hT,fun u => ⟨hLowR u,hHighR u⟩,
    fun i j u => ⟨hLowK i j u,hHighK i j u⟩,fun u => ⟨hLow u,?_⟩⟩
  have hLift := norm_smoothSphereTrace_higher_of_rotation hn (-(1/2):ℝ) (1/2:ℝ) (by norm_num)
    (by norm_num) D_B (D*r^2) (G*r^2) (by positivity) (by positivity) hLow hRot u
  rw [smoothSphereTraceSobolev_order_eq hn (show (-(1/2):ℝ)+1 = 1/2 by norm_num) _ (by norm_num),
    smoothSphereTraceSobolev_order_eq hn (show (1/2:ℝ)+1 = 3/2 by norm_num) _ (by norm_num)] at hLift
  refine hLift.trans_eq ?_
  have hFactor : 2*(D*r^2)^2+(dim:ℝ)^2*(G*r^2+D*r^2*(2*(dim:ℝ)))^2 =
      r^4*(2*D^2+(dim:ℝ)^2*(G+D*(2*(dim:ℝ)))^2) := by ring
  rw [hFactor,Real.sqrt_mul (by positivity),show r^4 = (r^2)^2 by ring,Real.sqrt_sq (sq_nonneg r)]
  dsimp only [C_H]
  ring

end CalderonN
