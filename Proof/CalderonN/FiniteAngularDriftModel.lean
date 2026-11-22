module

public import Proof.CalderonN.AngularPoissonEquation
public import Proof.CalderonN.FiniteHarmonicRotation
public import Proof.CalderonN.AngularRadialWeight

import Mathlib.Tactic

/-! The explicit flat drift correction is equivariant under rotation.
Its commutator differentiates only the linear drift functional. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Matrix.Norms.Elementwise Topology
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem ballRotationCoefficient_flat (i j : Fin dim) :
    ballRotationCoefficient i j (fun _ : X dim => (1 : Mat dim)) = 0 := by
  funext z
  unfold ballRotationCoefficient
  simp

private theorem ballRotationCoefficient_linear_scalar (i j : Fin dim) (ell : X dim →L[ℝ] ℝ) :
    ballRotationCoefficient i j (fun z => ell z • (1 : Mat dim)) =
      fun z => (ell.comp (ballRotationGeneratorL i j)) z • (1 : Mat dim) := by
  let L := ell.smulRight (1 : Mat dim)
  funext z
  unfold ballRotationCoefficient
  change fderiv ℝ (⇑L) z (ballRotationGeneratorL i j z)+
    (ell z • (1 : Mat dim))*coordinateMatrix (ballRotationGeneratorL i j)-
    coordinateMatrix (ballRotationGeneratorL i j)*(ell z • (1 : Mat dim)) = _
  rw [ContinuousLinearMap.fderiv]
  simp only [L,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,
    smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  abel

/-- The commutator of the first drift model and a solid rotation is its
first variation with the differentiated drift coefficient. -/
theorem eqOn_angular_harmonicFiniteDriftVariation (i j : Fin dim)
    (ell : X dim →L[ℝ] ℝ) (f : HarmonicFiniteCoefficients dim) :
    let u := harmonicFiniteDriftVariationSmooth ell f
    let v := harmonicFiniteDriftVariationSmooth ell (finiteHarmonicRotationL i j f)
    let qθ := harmonicFiniteDriftVariationSmooth (ell.comp (ballRotationGeneratorL i j)) f
    EqOn (angularBallCorrection i j u v).1 qθ.1 (closedBall (0 : X dim) 1) := by
  dsimp only
  let p := harmonicFiniteSmooth f
  let pθ := harmonicFiniteSmooth (finiteHarmonicRotationL i j f)
  let u := harmonicFiniteDriftVariationSmooth ell f
  let v := harmonicFiniteDriftVariationSmooth ell (finiteHarmonicRotationL i j f)
  let ellθ := ell.comp (ballRotationGeneratorL i j)
  let qθ := harmonicFiniteDriftVariationSmooth ellθ f
  let A₀ : X dim → Mat dim := fun _ => 1
  let A (z : X dim) := ell z • (1 : Mat dim)
  let Aθ (z : X dim) := ellθ z • (1 : Mat dim)
  let w := angularBallCorrection i j u v
  let e : SmoothData dim := ⟨w.1-qθ.1,w.2.sub qθ.2⟩
  have hA : ContDiff ℝ ∞ A := ell.contDiff.smul contDiff_const
  have hW (z : X dim) :
      negativeBallDivergence A₀ (sphereRotationDerivative i j u.1) z =
        -(negativeBallDivergence A pθ.1 z+negativeBallDivergence Aθ p.1 z) := by
    have h := sphereRotationDerivative_negativeBallDivergence i j
      (contDiff_const (c := (1 : Mat dim))) u z
    rw [ballRotationCoefficient_flat] at h
    have hZero : negativeBallDivergence (0 : X dim → Mat dim) u.1 z = 0 := by
      unfold negativeBallDivergence Elliptic.Lop
      simp [Elliptic.pd,coordDeriv]
    rw [hZero,add_zero] at h
    have hD : negativeBallDivergence A₀ u.1 = -negativeBallDivergence A p.1 :=
      funext (negativeBallDivergence_flat_harmonicFiniteDriftVariation ell f)
    change sphereRotationDerivative i j (negativeBallDivergence A₀ u.1) z = _ at h
    rw [hD] at h
    have hRotNeg : sphereRotationDerivative i j (-negativeBallDivergence A p.1) z =
        -sphereRotationDerivative i j (negativeBallDivergence A p.1) z := by
      unfold sphereRotationDerivative
      rw [fderiv_neg,neg_apply]
    rw [← h,hRotNeg,sphereRotationDerivative_negativeBallDivergence i j hA p z,
      ballRotationCoefficient_linear_scalar]
    change _ = -(negativeBallDivergence A pθ.1 z+_)
    rw [show pθ.1 = sphereRotationDerivative i j p.1 from harmonicFiniteSmooth_rotation i j f]
  have hT : EqOn e.1 0 (standardSphere dim) := by
    intro z hz
    have hU := sphereRotationDerivative_eq_zero_of_sphere_zero i j u.1 u.2
      (fun z => harmonicFiniteDriftVariationSmooth_trace ell f z.property) ⟨z,hz⟩
    change sphereRotationDerivative i j u.1 z-v.1 z-qθ.1 z = 0
    rw [hU,show v.1 z = 0 from harmonicFiniteDriftVariationSmooth_trace ell _ hz,
      show qθ.1 z = 0 from harmonicFiniteDriftVariationSmooth_trace ellθ f hz]
    ring
  have hE : EqOn (negativeBallDivergence A₀ e.1) 0 (ball (0 : X dim) 1) := by
    intro z hz
    let uθ : SmoothData dim := ⟨sphereRotationDerivative i j u.1,
      contDiff_sphereRotationDerivative i j u.1 u.2⟩
    change negativeBallDivergence A₀ (w.1-qθ.1) z = 0
    rw [negativeBallDivergence_sub_solution contDiff_const w qθ]
    change negativeBallDivergence A₀ (uθ.1-v.1) z-negativeBallDivergence A₀ qθ.1 z = 0
    rw [negativeBallDivergence_sub_solution contDiff_const uθ v,hW z,
      negativeBallDivergence_flat_harmonicFiniteDriftVariation ell (finiteHarmonicRotationL i j f) z,
      negativeBallDivergence_flat_harmonicFiniteDriftVariation ellθ f z]
    change -(_+_) - (-negativeBallDivergence A pθ.1 z) -
      (-negativeBallDivergence Aθ p.1 z) = 0
    ring
  obtain h := eqOn_closedUnitBall_of_negativeBallDivergence_eq_zero contDiff_const
    (uniformlyEllipticOn_const_one_one (fixedBallOpens dim : Set (X dim))) e hE hT
  exact fun z hz => sub_eq_zero.mp (h hz)

theorem eqOn_radial_angular_harmonicFiniteDriftVariation (i j : Fin dim)
    (ell : X dim →L[ℝ] ℝ) (f : HarmonicFiniteCoefficients dim) :
    let u := harmonicFiniteDriftVariationSmooth ell f
    let v := harmonicFiniteDriftVariationSmooth ell (finiteHarmonicRotationL i j f)
    let qθ := harmonicFiniteDriftVariationSmooth (ell.comp (ballRotationGeneratorL i j)) f
    EqOn (fun z => sphereRotationDerivative i j (fun w => fderiv ℝ u.1 w w) z-fderiv ℝ v.1 z z)
      (fun z => fderiv ℝ qθ.1 z z) (standardSphere dim) := by
  dsimp only
  intro z hz
  exact (angularBallCorrection_radialDerivative i j _ _ z).symm.trans
    (eqOn_radialDerivative_of_eqOn_closedUnitBall (eqOn_angular_harmonicFiniteDriftVariation i j ell f) hz)

end CalderonN
