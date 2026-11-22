module

public import Proof.CalderonN.SmoothTraceLinearAdjunction
public import Proof.CalderonN.FiniteSmoothTraceAngularModel
public import Proof.CalderonN.DoubleAngularConormalEndpoints

import Proof.CalderonN.SmoothMultiplierCommutatorCompletion
import Mathlib.Tactic

/-! The exact double angular trace operator and its physical conormal
expression on finite input. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5600000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def smoothTraceAngularComm (i j : Fin dim)
    (T : Module.End ℝ (SmoothSphereTrace dim)) : Module.End ℝ (SmoothSphereTrace dim) :=
  smoothSphereTraceRotation i j*T-T*smoothSphereTraceRotation i j

theorem finiteSmoothTrace_doubleAngularComm_apply (i j k l : Fin dim)
    (T : Module.End ℝ (SmoothSphereTrace dim)) (f : HarmonicFiniteCoefficients dim) :
    let K₁ := smoothSphereTraceRotation i j
    let K₂ := smoothSphereTraceRotation k l
    let J₁ := finiteHarmonicRotationL i j
    let J₂ := finiteHarmonicRotationL k l
    let L (g : HarmonicFiniteCoefficients dim) := T (finiteHarmonicSmoothTraceL g)
    smoothTraceAngularComm k l (smoothTraceAngularComm i j T) (finiteHarmonicSmoothTraceL f) =
      K₂ (K₁ (L f)-L (J₁ f))-(K₁ (L (J₂ f))-L (J₁ (J₂ f))) := by
  dsimp only
  unfold smoothTraceAngularComm
  simp only [LinearMap.sub_apply,Module.End.mul_apply,finiteHarmonicSmoothTraceL_rotation]

theorem finiteSmoothTrace_remainder_apply
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)
    (W : SmoothData dim)
    (hW : ∀ u : SmoothData dim, EqOn (smoothBallConormal A u.1)
      (fun z => W.1 z*fderiv ℝ u.1 z z) (standardSphere dim))
    (r : ℝ) (g : HarmonicFiniteCoefficients dim) :
    let R := smoothSphereTaylorResponses hA hEll S
    let A' := (LinearMap.fst ℝ _ _).comp R
    let B := (LinearMap.fst ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp R)
    let Q := (LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp R)
    let T := smoothSphereTraceMul W*A'-B-r • (smoothSphereTraceMul ⟨ell,ell.contDiff⟩*B+Q)
    T (finiteHarmonicSmoothTraceL g) =
      smoothSphereTrace (smoothConormalData hA (S (harmonicFiniteSmooth g)).actual)-
        finiteFlatRadialTraceL g-r • finiteAffineConormalTraceL ell g := by
  dsimp only
  let R := smoothSphereTaylorResponses hA hEll S
  let A' := (LinearMap.fst ℝ _ _).comp R
  let B := (LinearMap.fst ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp R)
  let Q := (LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp R)
  let T := smoothSphereTraceMul W*A'-B-r • (smoothSphereTraceMul ⟨ell,ell.contDiff⟩*B+Q)
  let b (f : HarmonicFiniteCoefficients dim) := (S (harmonicFiniteSmooth f)).actual
  change T (finiteHarmonicSmoothTraceL g) = _
  rw [finiteHarmonicSmoothTraceL_apply]
  have h := smoothSphereTaylorResponse_remainder hA hEll S W hW r (harmonicFiniteSmooth g)
  have hT' : T (smoothSphereTrace (harmonicFiniteSmooth g)) =
      smoothSphereTrace ((S (harmonicFiniteSmooth g)).remainder hA r) := h.symm
  rw [hT']
  let u := harmonicFiniteSmooth g
  let q := harmonicFiniteDriftVariationSmooth ell g
  let U := S u
  let V : ConormalTaylorSolutions A ell u := {
    actual := U.actual
    flat := u
    first := q
    actualTrace := U.actualTrace
    actualEquation := U.actualEquation
    flatTrace := fun _ _ => rfl
    flatEquation := fun z _ => negativeBallDivergence_flat_harmonicFiniteSmooth g z
    firstTrace := harmonicFiniteDriftVariationSmooth_trace ell g
    firstEquation := fun z _ => negativeBallDivergence_flat_harmonicFiniteDriftVariation ell g z }
  have hRem := conormalTaylorSolutions_remainder_eqOn hA hEll U V (fun _ _ => rfl) r
  change smoothSphereTrace (U.remainder hA r) = _
  rw [(smoothSphereTrace_eq_iff _ _).mpr hRem]
  apply Subtype.ext
  funext z
  change smoothBallConormal A (b g).1 z-fderiv ℝ u.1 z z-r*(ell z*fderiv ℝ u.1 z z+
    fderiv ℝ q.1 z z) =
    smoothBallConormal A (b g).1 z-(flatRadialDataL g).1 z-r*(firstConormalDataL ell g).1 z
  rw [flatRadialDataL_apply,firstConormalDataL_apply]

theorem finiteSmoothTrace_angularComm_remainder
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)
    (W : SmoothData dim)
    (hW : ∀ u : SmoothData dim, EqOn (smoothBallConormal A u.1)
      (fun z => W.1 z*fderiv ℝ u.1 z z) (standardSphere dim))
    (r : ℝ) (i j : Fin dim) (f : HarmonicFiniteCoefficients dim) :
    let R := smoothSphereTaylorResponses hA hEll S
    let A' := (LinearMap.fst ℝ _ _).comp R
    let B := (LinearMap.fst ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp R)
    let Q := (LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp R)
    let T := smoothSphereTraceMul W*A'-B-r • (smoothSphereTraceMul ⟨ell,ell.contDiff⟩*B+Q)
    let b (g : HarmonicFiniteCoefficients dim) := (S (harmonicFiniteSmooth g)).actual
    let J₁ := finiteHarmonicRotationL i j
    let ell₁ := ell.comp (ballRotationGeneratorL i j)
    ∀ z : ↥(standardSphere dim),
      (smoothTraceAngularComm i j T (finiteHarmonicSmoothTraceL f)).1 z =
        (sphereRotationDerivative i j (smoothBallConormal A (b f).1)-
          smoothBallConormal A (b (J₁ f)).1-r • (firstConormalDataL ell₁ f).1) z := by
  dsimp only
  let R := smoothSphereTaylorResponses hA hEll S
  let A' := (LinearMap.fst ℝ _ _).comp R
  let B := (LinearMap.fst ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp R)
  let Q := (LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp R)
  let T := smoothSphereTraceMul W*A'-B-r • (smoothSphereTraceMul ⟨ell,ell.contDiff⟩*B+Q)
  let b (g : HarmonicFiniteCoefficients dim) := (S (harmonicFiniteSmooth g)).actual
  let J₁ := finiteHarmonicRotationL i j
  let K₁ := smoothSphereTraceRotation i j
  let P (g : HarmonicFiniteCoefficients dim) := smoothConormalData hA (b g)
  let Z (g : HarmonicFiniteCoefficients dim) := smoothSphereTrace (P g)
  have hT (g : HarmonicFiniteCoefficients dim) :
      T (finiteHarmonicSmoothTraceL g) = Z g-finiteFlatRadialTraceL g-r • finiteAffineConormalTraceL ell g :=
    finiteSmoothTrace_remainder_apply hA hEll S W hW r g
  have hK : smoothTraceAngularComm i j T (finiteHarmonicSmoothTraceL f) =
      K₁ (Z f)-Z (J₁ f)-r • finiteAffineConormalTraceL (ell.comp (ballRotationGeneratorL i j)) f := by
    change K₁ (T (finiteHarmonicSmoothTraceL f))-T (K₁ (finiteHarmonicSmoothTraceL f)) = _
    rw [show K₁ (finiteHarmonicSmoothTraceL f) = finiteHarmonicSmoothTraceL (J₁ f) from
      finiteHarmonicSmoothTraceL_rotation i j f,hT f,hT (J₁ f)]
    simp only [map_sub,map_smul]
    have hB := finiteFlatRadialTraceL_rotation i j f
    have hQ := finiteAffineConormalTraceL_rotation i j ell f
    change K₁ (finiteFlatRadialTraceL f) = finiteFlatRadialTraceL (J₁ f) at hB
    change K₁ (finiteAffineConormalTraceL ell f)-finiteAffineConormalTraceL ell (J₁ f) = _ at hQ
    rw [hB]
    have hQ' := congrArg (r • ·) hQ
    rw [smul_sub] at hQ'
    rw [← hQ']
    abel
  intro z
  change (smoothTraceAngularComm i j T (finiteHarmonicSmoothTraceL f)).1 z = _
  rw [hK]
  dsimp only [K₁,Z]
  rw [smoothSphereTraceRotation_apply]
  rfl

theorem finiteSmoothTrace_doubleAngularComm_remainder
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)
    (W : SmoothData dim)
    (hW : ∀ u : SmoothData dim, EqOn (smoothBallConormal A u.1)
      (fun z => W.1 z*fderiv ℝ u.1 z z) (standardSphere dim))
    (r : ℝ) (i j k l : Fin dim) (f : HarmonicFiniteCoefficients dim) :
    let R := smoothSphereTaylorResponses hA hEll S
    let A' := (LinearMap.fst ℝ _ _).comp R
    let B := (LinearMap.fst ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp R)
    let Q := (LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp R)
    let T := smoothSphereTraceMul W*A'-B-r • (smoothSphereTraceMul ⟨ell,ell.contDiff⟩*B+Q)
    let b (g : HarmonicFiniteCoefficients dim) := (S (harmonicFiniteSmooth g)).actual
    let J₁ := finiteHarmonicRotationL i j
    let J₂ := finiteHarmonicRotationL k l
    let ell₂ := (ell.comp (ballRotationGeneratorL i j)).comp (ballRotationGeneratorL k l)
    ∀ z : ↥(standardSphere dim),
      (smoothTraceAngularComm k l (smoothTraceAngularComm i j T) (finiteHarmonicSmoothTraceL f)).1 z =
        (sphereRotationDerivative k l
          (sphereRotationDerivative i j (smoothBallConormal A (b f).1)-smoothBallConormal A (b (J₁ f)).1)-
          (sphereRotationDerivative i j (smoothBallConormal A (b (J₂ f)).1)-
            smoothBallConormal A (b (J₁ (J₂ f))).1)-
          r • (firstConormalDataL ell₂ f).1) z := by
  dsimp only
  let R := smoothSphereTaylorResponses hA hEll S
  let A' := (LinearMap.fst ℝ _ _).comp R
  let B := (LinearMap.fst ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp R)
  let Q := (LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp R)
  let T := smoothSphereTraceMul W*A'-B-r • (smoothSphereTraceMul ⟨ell,ell.contDiff⟩*B+Q)
  let b (g : HarmonicFiniteCoefficients dim) := (S (harmonicFiniteSmooth g)).actual
  let J₁ := finiteHarmonicRotationL i j
  let J₂ := finiteHarmonicRotationL k l
  let K₁ := smoothSphereTraceRotation i j
  let K₂ := smoothSphereTraceRotation k l
  let P (g : HarmonicFiniteCoefficients dim) := smoothConormalData hA (b g)
  let Z (g : HarmonicFiniteCoefficients dim) := smoothSphereTrace (P g)
  let ell₂ := (ell.comp (ballRotationGeneratorL i j)).comp (ballRotationGeneratorL k l)
  have hT (g : HarmonicFiniteCoefficients dim) :
      T (finiteHarmonicSmoothTraceL g) = Z g-finiteFlatRadialTraceL g-r • finiteAffineConormalTraceL ell g :=
    finiteSmoothTrace_remainder_apply hA hEll S W hW r g
  have hK1 (g : HarmonicFiniteCoefficients dim) :
      K₁ (T (finiteHarmonicSmoothTraceL g))-T (finiteHarmonicSmoothTraceL (J₁ g)) =
        K₁ (Z g)-Z (J₁ g)-
          r • finiteAffineConormalTraceL (ell.comp (ballRotationGeneratorL i j)) g := by
    rw [hT g,hT (J₁ g)]
    simp only [map_sub,map_smul]
    have hB := finiteFlatRadialTraceL_rotation i j g
    have hQ := finiteAffineConormalTraceL_rotation i j ell g
    change K₁ (finiteFlatRadialTraceL g) = finiteFlatRadialTraceL (J₁ g) at hB
    change K₁ (finiteAffineConormalTraceL ell g)-finiteAffineConormalTraceL ell (J₁ g) = _ at hQ
    rw [hB]
    have hQ' := congrArg (r • ·) hQ
    rw [smul_sub] at hQ'
    rw [← hQ']
    abel
  have hK2 :
      smoothTraceAngularComm k l (smoothTraceAngularComm i j T) (finiteHarmonicSmoothTraceL f) =
        (K₂ (K₁ (Z f)-Z (J₁ f))-(K₁ (Z (J₂ f))-Z (J₁ (J₂ f))))-
          r • finiteAffineConormalTraceL ell₂ f := by
    rw [finiteSmoothTrace_doubleAngularComm_apply]
    change K₂ (K₁ (T (finiteHarmonicSmoothTraceL f))-T (finiteHarmonicSmoothTraceL (J₁ f)))-
      (K₁ (T (finiteHarmonicSmoothTraceL (J₂ f)))-T (finiteHarmonicSmoothTraceL (J₁ (J₂ f)))) = _
    rw [hK1 f,hK1 (J₂ f)]
    simp only [map_sub,map_smul]
    have hQ := finiteAffineConormalTraceL_rotation k l (ell.comp (ballRotationGeneratorL i j)) f
    change K₂ (finiteAffineConormalTraceL (ell.comp (ballRotationGeneratorL i j)) f)-
      finiteAffineConormalTraceL (ell.comp (ballRotationGeneratorL i j)) (J₂ f) =
        finiteAffineConormalTraceL ell₂ f at hQ
    have hQ' := congrArg (r • ·) hQ
    rw [smul_sub] at hQ'
    rw [← hQ']
    abel
  intro z
  change (smoothTraceAngularComm k l (smoothTraceAngularComm i j T) (finiteHarmonicSmoothTraceL f)).1 z = _
  rw [hK2]
  have hRot (a c : Fin dim) (U : SmoothData dim) :
      (smoothSphereTraceRotation a c (smoothSphereTrace U)).1 z =
        sphereRotationDerivative a c U.1 z := by rw [smoothSphereTraceRotation_apply,smoothSphereTrace_apply]
  have hSplit (g : HarmonicFiniteCoefficients dim) :
      K₁ (Z g)-Z (J₁ g) =
        smoothSphereTrace (smoothSubtractData
          ⟨sphereRotationDerivative i j (P g).1,
            contDiff_sphereRotationDerivative i j (P g).1 (P g).2⟩ (P (J₁ g))) := by
    dsimp only [K₁,Z]
    rw [smoothSphereTraceRotation_apply]
    rfl
  rw [hSplit,hSplit]
  simp only [Submodule.coe_sub,Submodule.coe_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  change (smoothSphereTraceRotation k l (smoothSphereTrace _)).1 z-(smoothSphereTrace _).1 z-_ = _
  rw [hRot,smoothSphereTrace_apply]
  rfl

end CalderonN
