module

public import Proof.CalderonN.ActualSupportedConormal
public import Proof.CalderonN.FiniteSmoothTraceAngularModel

import Proof.CalderonN.BallRotationConormal
import Proof.CalderonN.PolynomialConormalFirstVariation
import Mathlib.Tactic

/-! Matrix elements of the actual conormal remainder's rotation
commutator on finite harmonic packets. -/

public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {d : Data dim} {x : X dim}

theorem harmonicFiniteDriftVariationSmooth_equation (ell : X dim →L[ℝ] ℝ)
    (f : HarmonicFiniteCoefficients dim) (z : X dim) :
    negativeBallDivergence (fun _ => (1:Mat dim)) (harmonicFiniteDriftVariationSmooth ell f).1 z =
      -negativeBallDivergence (fun w => ell w • (1:Mat dim)) (harmonicFiniteSmooth f).1 z := by
  let u := harmonicFiniteSmooth f
  let q := harmonicFiniteDriftVariationSmooth ell f
  have hQ := negativeBallDivergence_scalar (fun _ => (1 : ℝ)) q contDiff_const z
  have hU := negativeBallDivergence_scalar ell u ell.contDiff z
  simp only [one_smul,one_mul,coordDeriv,fderiv_fun_const,Pi.zero_apply,zero_apply,
    zero_mul,Finset.sum_const_zero,add_zero] at hQ
  change negativeBallDivergence (fun _ => (1:Mat dim)) q.1 z =
    -negativeBallDivergence (fun w => ell w • (1:Mat dim)) u.1 z
  rw [hQ,hU,harmonicFiniteDriftVariationSmooth_flat_laplace,laplace_flat_harmonicFiniteSmooth]
  simp only [coordDeriv,ContinuousLinearMap.fderiv,mul_zero,zero_add,neg_neg,u]

theorem ActualGaussFiberData.conormalRemainder_finite_eq (D : ActualGaussFiberData d x)
    (f : HarmonicFiniteCoefficients dim) :
    D.conormalRemainder (finiteHarmonicSmoothTraceL f) =
      D.conormal (finiteHarmonicSmoothTraceL f)-finiteFlatRadialTraceL f-
        d.radius x • finiteAffineConormalTraceL (firstDensityCenterLinear d x) f := by
  let u := harmonicFiniteSmooth f
  let ell := firstDensityCenterLinear d x
  let S := D.solve u
  let U : ConormalTaylorSolutions D.coefficient ell u :=
    ⟨S.actual,u,harmonicFiniteDriftVariationSmooth ell f,S.actualTrace,S.actualEquation,
      fun _ _ => rfl,fun z _ => negativeBallDivergence_flat_harmonicFiniteSmooth f z,
      harmonicFiniteDriftVariationSmooth_trace ell f,fun z _ => harmonicFiniteDriftVariationSmooth_equation ell f z⟩
  let r := d.radius x
  have hEq := conormalTaylorSolutions_remainder_eqOn D.smoothCoefficient D.ellipticCoefficient S U
    (fun _ _ => rfl) r
  rw [finiteHarmonicSmoothTraceL_apply,D.conormalRemainder_apply,D.conormal_apply]
  have hS : smoothSphereTrace (S.remainder D.smoothCoefficient r) =
      smoothSphereTrace (U.remainder D.smoothCoefficient r) :=
    (smoothSphereTrace_eq_iff _ _).mpr hEq
  rw [hS]
  apply Subtype.ext
  funext z
  simp only [smoothSphereTrace_apply,ConormalTaylorSolutions.remainder,ConormalTaylorSolutions.degree,
    ConormalTaylorSolutions.affineConormal,smoothBallRadialDerivative,
    finiteFlatRadialTraceL,finiteAffineConormalTraceL,LinearMap.comp_apply,smoothSphereTraceL_apply,
    flatRadialDataL_apply,firstConormalDataL_apply,Submodule.coe_sub,Submodule.coe_smul,
    Pi.sub_apply,Pi.smul_apply,smul_eq_mul,U,S,u,ell,r]

theorem ActualGaussFiberData.rotation_conormalRemainder_finite_eq (D : ActualGaussFiberData d x)
    (i j : I dim) (f : HarmonicFiniteCoefficients dim) (z : ↥(standardSphere dim)) :
    ((smoothSphereTraceRotation i j*D.conormalRemainder-D.conormalRemainder*smoothSphereTraceRotation i j)
      (finiteHarmonicSmoothTraceL f)).1 z =
      sphereRotationDerivative i j (smoothBallConormal D.coefficient (D.solve (harmonicFiniteSmooth f)).actual.1) z-
        smoothBallConormal D.coefficient (D.solve (harmonicFiniteSmooth (finiteHarmonicRotationL i j f))).actual.1 z-
        d.radius x*(firstConormalDataL ((firstDensityCenterLinear d x).comp (ballRotationGeneratorL i j)) f).1 z := by
  let K := smoothSphereTraceRotation i j
  let F := finiteHarmonicSmoothTraceL (dim:=dim)
  let R := finiteHarmonicRotationL i j
  let L := finiteFlatRadialTraceL (dim:=dim)
  let V := finiteAffineConormalTraceL (firstDensityCenterLinear d x)
  let V' := finiteAffineConormalTraceL ((firstDensityCenterLinear d x).comp (ballRotationGeneratorL i j))
  have hR : K (F f) = F (R f) := finiteHarmonicSmoothTraceL_rotation i j f
  have hL : K (L f) = L (R f) := finiteFlatRadialTraceL_rotation i j f
  have hV : K (V f)-V (R f) = V' f := finiteAffineConormalTraceL_rotation i j _ f
  have hR₁ : D.conormalRemainder (F f) = D.conormal (F f)-L f-d.radius x • V f :=
    D.conormalRemainder_finite_eq f
  have hR₂ : D.conormalRemainder (F (R f)) = D.conormal (F (R f))-L (R f)-d.radius x • V (R f) :=
    D.conormalRemainder_finite_eq (R f)
  have hEq : K (D.conormalRemainder (F f))-D.conormalRemainder (K (F f)) =
      K (D.conormal (F f))-D.conormal (F (R f))-d.radius x • V' f := by
    rw [hR,hR₁,hR₂,map_sub,map_sub,map_smul,hL,← hV,smul_sub]
    abel
  change (K (D.conormalRemainder (F f))-D.conormalRemainder (K (F f))).1 z = _
  rw [hEq]
  simp only [K,F,R,V',finiteHarmonicSmoothTraceL_apply,D.conormal_apply,
    smoothSphereTraceRotation_apply,finiteAffineConormalTraceL,LinearMap.comp_apply,smoothSphereTraceL_apply,
    smoothSphereTrace_apply,Submodule.coe_sub,Submodule.coe_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]

theorem ActualGaussFiberData.rotation_conormalRemainder_finite_energy (D : ActualGaussFiberData d x)
    (hSym : ∀ z ∈ ball (0:X dim) 1,(D.coefficient z).IsSymm)
    (i j : I dim) (f g : HarmonicFiniteCoefficients dim) :
    unitSphereArea dim *
      (∫ z : ↥(standardSphere dim),(harmonicFiniteSmooth g).1 z*
        ((smoothSphereTraceRotation i j*D.conormalRemainder-D.conormalRemainder*smoothSphereTraceRotation i j)
          (finiteHarmonicSmoothTraceL f)).1 z ∂(sphereProbability dim)) =
      energyFormH1 (ballRotationCoefficient i j D.coefficient) 0 0
        (smoothSobolev (D.solve (harmonicFiniteSmooth f)).actual)
        (smoothSobolev (D.solve (harmonicFiniteSmooth g)).actual)-
      d.radius x*energyFormH1 (fun z => ((firstDensityCenterLinear d x).comp
        (ballRotationGeneratorL i j)) z • (1:Mat dim)) 0 0
        (smoothSobolev (harmonicFiniteSmooth f)) (smoothSobolev (harmonicFiniteSmooth g)) := by
  let S := D.solve (harmonicFiniteSmooth f)
  let T := D.solve (harmonicFiniteSmooth (finiteHarmonicRotationL i j f))
  let V := D.solve (harmonicFiniteSmooth g)
  let u := harmonicFiniteSmooth f
  let v := harmonicFiniteSmooth g
  let ell := (firstDensityCenterLinear d x).comp (ballRotationGeneratorL i j)
  let A := D.coefficient
  let Q (z : X dim) := sphereRotationDerivative i j (smoothBallConormal A S.actual.1) z-
    smoothBallConormal A T.actual.1 z
  let J := firstConormalDataL ell f
  let r := d.radius x
  have hTV : EqOn T.actual.1 (sphereRotationDerivative i j u.1) (standardSphere dim) := by
    rw [← harmonicFiniteSmooth_rotation i j f]
    exact T.actualTrace
  have hE := integral_angular_conormal_commutator i j D.smoothCoefficient hSym
    S.actual T.actual V.actual u S.actualTrace hTV S.actualEquation T.actualEquation V.actualEquation
  have hEF : unitSphereArea dim *
      (∫ z : ↥(standardSphere dim),v.1 z*Q z ∂(sphereProbability dim)) =
      energyFormH1 (ballRotationCoefficient i j A) 0 0 (smoothSobolev S.actual) (smoothSobolev V.actual) := by
    rw [← hE]
    congr 1
    apply integral_congr_ae
    filter_upwards with z
    rw [V.actualTrace z.2]
  have hA := affineEnergy_harmonicFinite_eq_firstConormal ell f g
  have hJA : energyFormH1 (fun z => ell z • (1:Mat dim)) 0 0 (smoothSobolev u) (smoothSobolev v) =
      unitSphereArea dim * ∫ z : ↥(standardSphere dim), v.1 z*J.1 z ∂(sphereProbability dim) := by
    rw [show J = firstConormalDataL ell f from rfl,firstConormalDataL_apply]
    exact hA
  let : CompactSpace ↥(standardSphere dim) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0:X dim) 1)
  have hQ : Continuous Q :=
    (contDiff_sphereRotationDerivative i j _ (contDiff_smoothBallConormal D.smoothCoefficient S.actual)).continuous.sub
      (contDiff_smoothBallConormal D.smoothCoefficient T.actual).continuous
  have hInt (a : X dim → ℝ) (ha : Continuous a) :
      Integrable (fun z : ↥(standardSphere dim) => v.1 z*a z) (sphereProbability dim) :=
    ((v.2.continuous.mul ha).comp continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPt (z : ↥(standardSphere dim)) :
      v.1 z*((smoothSphereTraceRotation i j*D.conormalRemainder-D.conormalRemainder*smoothSphereTraceRotation i j)
        (finiteHarmonicSmoothTraceL f)).1 z = v.1 z*Q z-r*(v.1 z*J.1 z) := by
    rw [D.rotation_conormalRemainder_finite_eq i j f z]
    change v.1 z*(Q z-r*J.1 z) = _
    ring
  change unitSphereArea dim *
      (∫ z : ↥(standardSphere dim),v.1 z*((smoothSphereTraceRotation i j*D.conormalRemainder-
        D.conormalRemainder*smoothSphereTraceRotation i j) (finiteHarmonicSmoothTraceL f)).1 z
          ∂(sphereProbability dim)) =
      energyFormH1 (ballRotationCoefficient i j A) 0 0 (smoothSobolev S.actual) (smoothSobolev V.actual)-
        r*energyFormH1 (fun z => ell z • (1:Mat dim)) 0 0 (smoothSobolev u) (smoothSobolev v)
  simp_rw [hPt]
  rw [integral_sub (hInt Q hQ) ((hInt J.1 (smoothBallData_contDiff J).continuous).const_mul r),
    integral_const_mul,hJA,← hEF]
  ring

end CalderonN
