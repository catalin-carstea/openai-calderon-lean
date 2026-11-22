module

public import Proof.CalderonN.FixedBallWeakConormalTraceAgreement
public import Proof.CalderonN.ActualRelativeWeakConormalTaylor

import Proof.CalderonN.PolynomialConormalFirstVariation
import Mathlib.Tactic

/-! The weak Taylor family and the physical conormal remainder have
identical finite-harmonic matrix elements along the physical radius. -/

public section

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem fixedBallWeakConormalTaylor_eq_remainder_on_finite
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (f g : HarmonicFiniteCoefficients dim)
    (U : ConormalTaylorSolutions A ell (harmonicFiniteSmooth f))
    (r s : ℝ) (E₁ E₂ : FixedBallEnergyOperator dim)
    (hE : fixedBallFlatEnergyL dim+r • E₁+r^2 • E₂ = fixedBallSmoothEnergyL hA.continuous)
    (hE₁ : r • E₁ = s • fixedBallSmoothEnergyL (show Continuous (fun z => ell z • (1 : Mat dim))
      from ell.continuous.smul continuous_const)) :
    fixedBallWeakConormalTaylor r E₁ E₂ (harmonicBoundaryFiniteL (1/2:ℝ) f)
      (harmonicBoundaryFiniteL (1/2:ℝ) g) = unitSphereArea dim *
      ∫ w : ↥(standardSphere dim), (harmonicFiniteSmooth g).1 w*(U.remainder hA s).1 w
        ∂(sphereProbability dim) := by
  let L := harmonicBoundaryFiniteL (dim:=dim) (1/2:ℝ)
  let v := harmonicFiniteSmooth g
  let T (u : SmoothData dim) := ∫ w : ↥(standardSphere dim),v.1 w*u.1 w ∂(sphereProbability dim)
  let C : SmoothData dim := ⟨smoothBallConormal A U.actual.1,contDiff_smoothBallConormal hA U.actual⟩
  have hActual := fixedBallWeakConormal_eq_flux_on_finite hA hEll f g U.actual U.actualTrace U.actualEquation
  have hEll₀ := uniformlyEllipticOn_const_one_one (n:=Fin dim) (fixedBallOpens dim : Set (X dim))
  have hFlat := fixedBallWeakPoisson_eq_smooth_on_finite contDiff_const hEll₀ f U.flat
    U.flatTrace U.flatEquation
  have hFlatPoly := fixedBallWeakPoisson_eq_smooth_on_finite contDiff_const hEll₀ f (harmonicFiniteSmooth f)
    (fun _ _ => rfl) (fun z _ => negativeBallDivergence_flat_harmonicFiniteSmooth f z)
  have hU : smoothSobolev (harmonicFiniteSmooth f) = smoothSobolev U.flat :=
    hFlatPoly.symm.trans hFlat
  have h₀ : fixedBallWeakConormalAffine (fixedBallFlatEnergyL dim) (L f) (L g) =
      unitSphereArea dim*T U.degree := by
    rw [fixedBallWeakConormalAffine,ContinuousLinearMap.bilinearComp_apply,harmonicFirstOrderLift_finite_smooth,
      harmonicFirstOrderLift_finite_smooth,hU,fixedBallFlatEnergyL,fixedBallSmoothEnergyL_apply,
      energyFormH1_smooth_eq_boundary_flux contDiff_const U.flat v U.flatEquation]
    congr 1
    apply integral_congr_ae
    filter_upwards with w
    congr 1
    simpa only [one_smul,one_mul,smoothBallConormal,ConormalTaylorSolutions.degree,smoothBallRadialDerivative]
      using inner_smoothBallFlux_scalar (fun _ => 1) U.flat.1 (w : X dim)
  have h₁ : r*fixedBallWeakConormalAffine E₁ (L f) (L g) =
      s*(unitSphereArea dim*T U.affineConormal) := by
    change (r • E₁) (harmonicFirstOrderLift dim (L f)) (harmonicFirstOrderLift dim (L g)) = _
    rw [hE₁,harmonicFirstOrderLift_finite_smooth,harmonicFirstOrderLift_finite_smooth,hU]
    simp only [smul_apply,smul_eq_mul,fixedBallSmoothEnergyL_apply]
    exact congrArg (s*·) (affineEnergy_eq_firstConormal_of_firstVariation ell U.flat U.first g
      U.firstTrace (fun z hz => by rw [U.firstEquation hz]; exact neg_add_cancel _))
  have hI (u : SmoothData dim) : Integrable (fun w : ↥(standardSphere dim) => v.1 w*u.1 w)
      (sphereProbability dim) := by
    let : CompactSpace ↥(standardSphere dim) :=
      isCompact_iff_compactSpace.mp (isCompact_sphere (0:X dim) 1)
    exact ((v.2.continuous.mul u.2.continuous).comp continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hR : T (U.remainder hA s) = T C-T U.degree-s*T U.affineConormal := by
    dsimp only [T]
    have hPt (w : ↥(standardSphere dim)) :
        v.1 w*(U.remainder hA s).1 w =
          (v.1 w*C.1 w-v.1 w*U.degree.1 w)-s*(v.1 w*U.affineConormal.1 w) := by
      change v.1 w*(C.1 w-U.degree.1 w-s*U.affineConormal.1 w) = _
      ring
    simp_rw [hPt]
    have hJ : Integrable (fun w : ↥(standardSphere dim) => v.1 w*C.1 w-v.1 w*U.degree.1 w)
        (sphereProbability dim) := (hI C).sub (hI U.degree)
    rw [integral_sub hJ ((hI U.affineConormal).const_mul s),integral_sub (hI C) (hI U.degree),
      integral_const_mul]
  change fixedBallWeakConormalTaylor r E₁ E₂ (L f) (L g) = _
  unfold fixedBallWeakConormalTaylor
  simp only [sub_apply,smul_apply,smul_eq_mul]
  rw [hE,h₀,h₁,hActual,show (∫ w : ↥(standardSphere dim),v.1 w*smoothBallConormal A U.actual.1 w
    ∂(sphereProbability dim)) = T C from rfl]
  change unitSphereArea dim*T C-unitSphereArea dim*T U.degree-s*(unitSphereArea dim*T U.affineConormal) =
    unitSphereArea dim*T (U.remainder hA s)
  rw [hR]
  ring

theorem ActualRelativeWeakConormalGerm.eq_physical_remainder_finite
    {d : Data dim} {y : X dim} {N : ℕ} {B : ℝ}
    (H : ActualRelativeWeakConormalGerm d y N B) (hr : d.radius y ≠ 0)
    {x : X dim} (hx : (x,d.radius x/d.radius y-1) ∈ H.neighborhood)
    (D : ActualGaussFiberData d x) (f g : HarmonicFiniteCoefficients dim) :
    let p := (x,d.radius x/d.radius y-1)
    fixedBallWeakConormalTaylor (d.radius y) (H.first p) (H.second p)
      (harmonicBoundaryFiniteL (1/2:ℝ) f) (harmonicBoundaryFiniteL (1/2:ℝ) g) =
      unitSphereArea dim * ∫ w : ↥(standardSphere dim),(harmonicFiniteSmooth g).1 w*
        (D.conormalRemainder (smoothSphereTrace (harmonicFiniteSmooth f))).1 w ∂(sphereProbability dim) := by
  dsimp only
  let r := d.radius y
  let s := d.radius x
  let p := (x,s/r-1)
  let ell := firstDensityCenterLinear d x
  let A₁ (z : X dim) : Mat dim := ell z • 1
  let hA₁ : Continuous A₁ := ell.continuous.smul continuous_const
  have hp : r*(1+p.2) = s := by
    have hr' : r ≠ 0 := hr
    dsimp only [p]
    rw [show 1+(s/r-1) = s/r by ring,div_eq_mul_inv,mul_left_comm, mul_inv_cancel₀ hr',mul_one]
  have hE : fixedBallFlatEnergyL dim+r • H.first p+r^2 • H.second p =
      fixedBallSmoothEnergyL D.smoothCoefficient.continuous := by
    ext u v : 2
    rw [H.energy_eq p hx]
    symm
    apply fixedBallSmoothEnergyL_eq_weak_of_eqOn
    intro z hz
    change D.coefficient z = firstNormalVelocityCoefficient d x ((r*(1+p.2)) • frameVector d.frame x z)
    rw [hp]
    exact D.coefficientEq hz
  have hFirst : H.first p = (1+p.2) • fixedBallSmoothEnergyL hA₁ := by
    ext u v : 2
    rw [H.first_eq p hx,← fixedBallSmoothEnergyL_smul hA₁,fixedBallSmoothEnergyL_apply]
    rfl
  have hFirst' : r • H.first p = s • fixedBallSmoothEnergyL hA₁ := by
    rw [hFirst,smul_smul,hp]
  rw [D.conormalRemainder_apply]
  simp only [smoothSphereTrace_apply]
  exact fixedBallWeakConormalTaylor_eq_remainder_on_finite D.smoothCoefficient
    D.ellipticCoefficient f g (D.solve _) r s (H.first p) (H.second p) hE hFirst'

end CalderonN
