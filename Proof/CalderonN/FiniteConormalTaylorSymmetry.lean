module

public import Proof.CalderonN.FiniteSmoothDegreeForm
public import Proof.CalderonN.BallRotationConormal

import Mathlib.Tactic

/-! Green's identity makes the actual conormal map and both retained
Taylor coefficients symmetric in the same real sphere pairing. -/

public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem integrable_spherePair (a b : SmoothData dim) :
    Integrable (fun z : ↥(standardSphere dim) => a.1 z*b.1 z) (sphereProbability dim) := by
  letI : CompactSpace {z // z ∈ standardSphere dim} :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : X dim) 1)
  exact ((a.2.continuous.mul b.2.continuous).comp continuous_subtype_val).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integral_smoothBallConormal_symm {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    (hSym : ∀ z ∈ ball (0 : X dim) 1, (A z).IsSymm)
    (u v b c : SmoothData dim)
    (hb : EqOn (negativeBallDivergence A b.1) 0 (ball (0 : X dim) 1))
    (hc : EqOn (negativeBallDivergence A c.1) 0 (ball (0 : X dim) 1))
    (hu : EqOn b.1 u.1 (standardSphere dim)) (hv : EqOn c.1 v.1 (standardSphere dim)) :
    (∫ z : ↥(standardSphere dim), smoothBallConormal A b.1 z*v.1 z ∂(sphereProbability dim)) =
    ∫ z : ↥(standardSphere dim), u.1 z*smoothBallConormal A c.1 z ∂(sphereProbability dim) := by
  have hSymAE : ∀ᵐ z ∂(volume : Measure (X dim)).restrict (fixedBallOpens dim : Set (X dim)), (A z).IsSymm := by
    filter_upwards [ae_restrict_mem (fixedBallOpens dim).isOpen.measurableSet] with z hz
    exact hSym z hz
  have hE := energyFormH1_comm_of_isSymm_ae (c:=0) hSymAE (smoothSobolev b) (smoothSobolev c)
  rw [energyFormH1_smooth_eq_boundary_flux hA b c hb, energyFormH1_smooth_eq_boundary_flux hA c b hc] at hE
  apply (mul_right_inj' (unitSphereArea_pos (dim:=dim)).ne').mp
  refine (?_ : _ = _).trans (hE.trans ?_)
  · congr 1
    apply integral_congr_ae
    filter_upwards with z
    rw [hv z.2,mul_comm]
    rfl
  · congr 1
    apply integral_congr_ae
    filter_upwards with z
    rw [hu z.2]
    rfl

theorem integral_finiteFlatRadial_symm (f g : HarmonicFiniteCoefficients dim) :
    let u := harmonicFiniteSmooth f
    let v := harmonicFiniteSmooth g
    (∫ z : ↥(standardSphere dim), (fderiv ℝ u.1 z) z*v.1 z ∂(sphereProbability dim)) =
    ∫ z : ↥(standardSphere dim), u.1 z*(fderiv ℝ v.1 z) z ∂(sphereProbability dim) := by
  let u := harmonicFiniteSmooth f
  let v := harmonicFiniteSmooth g
  have h (w : SmoothData dim) (z : X dim) :
      smoothBallConormal (fun _ => 1) w.1 z = (fderiv ℝ w.1 z) z := by
    simpa only [smoothBallConormal,one_smul,one_mul] using inner_smoothBallFlux_scalar (fun _ => 1) w.1 z
  have he := integral_smoothBallConormal_symm (A := fun _ => 1) contDiff_const
    (fun _ _ => Matrix.isSymm_one) u v u v
    (fun z _ => negativeBallDivergence_flat_harmonicFiniteSmooth f z)
    (fun z _ => negativeBallDivergence_flat_harmonicFiniteSmooth g z) (fun _ _ => rfl) (fun _ _ => rfl)
  simp_rw [h] at he
  exact he

theorem integral_firstFiniteConormal_symm (ell : X dim →L[ℝ] ℝ) (f g : HarmonicFiniteCoefficients dim) :
    let u := harmonicFiniteSmooth f
    let v := harmonicFiniteSmooth g
    let q := harmonicFiniteDriftVariationSmooth ell f
    let p := harmonicFiniteDriftVariationSmooth ell g
    (∫ z : ↥(standardSphere dim), (ell z*(fderiv ℝ u.1 z) z+(fderiv ℝ q.1 z) z)*v.1 z ∂(sphereProbability dim)) =
    ∫ z : ↥(standardSphere dim), u.1 z*(ell z*(fderiv ℝ v.1 z) z+(fderiv ℝ p.1 z) z) ∂(sphereProbability dim) := by
  dsimp only
  have hSym (z : X dim) : (ell z • (1 : Mat dim)).IsSymm := by
    exact Matrix.isSymm_one.smul _
  have hE := energyFormH1_comm_of_isSymm_ae (c:=0) (Filter.Eventually.of_forall hSym)
    (smoothSobolev (harmonicFiniteSmooth f)) (smoothSobolev (harmonicFiniteSmooth g))
  rw [affineEnergy_harmonicFinite_eq_firstConormal ell f g,
    affineEnergy_harmonicFinite_eq_firstConormal ell g f] at hE
  apply (mul_right_inj' (unitSphereArea_pos (dim:=dim)).ne').mp
  refine Eq.trans ?_ hE
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => mul_comm _ _)

theorem integral_finiteConormalTaylor_symm {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    (hSym : ∀ z ∈ ball (0 : X dim) 1, (A z).IsSymm)
    (ell : X dim →L[ℝ] ℝ) (r : ℝ) (f g : HarmonicFiniteCoefficients dim)
    (b c e h : SmoothData dim)
    (hb : EqOn (negativeBallDivergence A b.1) 0 (ball (0 : X dim) 1))
    (hc : EqOn (negativeBallDivergence A c.1) 0 (ball (0 : X dim) 1))
    (hu : EqOn b.1 (harmonicFiniteSmooth f).1 (standardSphere dim))
    (hv : EqOn c.1 (harmonicFiniteSmooth g).1 (standardSphere dim))
    (he : EqOn e.1 (fun z => smoothBallConormal A b.1 z-fderiv ℝ (harmonicFiniteSmooth f).1 z z -
      r*(ell z*fderiv ℝ (harmonicFiniteSmooth f).1 z z+
        fderiv ℝ (harmonicFiniteDriftVariationSmooth ell f).1 z z)) (standardSphere dim))
    (hh : EqOn h.1 (fun z => smoothBallConormal A c.1 z-fderiv ℝ (harmonicFiniteSmooth g).1 z z -
      r*(ell z*fderiv ℝ (harmonicFiniteSmooth g).1 z z+
        fderiv ℝ (harmonicFiniteDriftVariationSmooth ell g).1 z z)) (standardSphere dim)) :
    (∫ z : ↥(standardSphere dim), e.1 z*(harmonicFiniteSmooth g).1 z ∂(sphereProbability dim)) =
      ∫ z : ↥(standardSphere dim), (harmonicFiniteSmooth f).1 z*h.1 z ∂(sphereProbability dim) := by
  let u := harmonicFiniteSmooth f
  let v := harmonicFiniteSmooth g
  have split (F : HarmonicFiniteCoefficients dim) (B E V : SmoothData dim)
      (hE : EqOn E.1 (fun z => smoothBallConormal A B.1 z-fderiv ℝ (harmonicFiniteSmooth F).1 z z -
        r*(ell z*fderiv ℝ (harmonicFiniteSmooth F).1 z z+
          fderiv ℝ (harmonicFiniteDriftVariationSmooth ell F).1 z z)) (standardSphere dim)) :
      (∫ z : ↥(standardSphere dim), E.1 z*V.1 z ∂(sphereProbability dim)) =
        (∫ z : ↥(standardSphere dim), smoothBallConormal A B.1 z*V.1 z ∂(sphereProbability dim)) -
        (∫ z : ↥(standardSphere dim), fderiv ℝ (harmonicFiniteSmooth F).1 z z*V.1 z ∂(sphereProbability dim)) -
        r*(∫ z : ↥(standardSphere dim), (ell z*fderiv ℝ (harmonicFiniteSmooth F).1 z z+
          fderiv ℝ (harmonicFiniteDriftVariationSmooth ell F).1 z z)*V.1 z ∂(sphereProbability dim)) := by
    let T : SmoothData dim := ⟨smoothBallConormal A B.1,contDiff_smoothBallConormal hA B⟩
    let R := smoothBallRadialDerivative (harmonicFiniteSmooth F)
    let Q := smoothBallRadialDerivative (harmonicFiniteDriftVariationSmooth ell F)
    let W : SmoothData dim := ⟨fun z => ell z*R.1 z+Q.1 z,(ell.contDiff.mul R.2).add Q.2⟩
    have hT := integrable_spherePair T V
    have hR := integrable_spherePair R V
    have hW := integrable_spherePair W V
    change _ = (∫ z : ↥(standardSphere dim), T.1 z*V.1 z ∂(sphereProbability dim)) -
      (∫ z : ↥(standardSphere dim), R.1 z*V.1 z ∂(sphereProbability dim)) -
      r*(∫ z : ↥(standardSphere dim), W.1 z*V.1 z ∂(sphereProbability dim))
    have hTR : Integrable (fun z : ↥(standardSphere dim) =>
        T.1 z*V.1 z-R.1 z*V.1 z) (sphereProbability dim) := hT.sub hR
    rw [← integral_const_mul,← integral_sub hT hR,← integral_sub hTR (hW.const_mul r)]
    apply integral_congr_ae
    filter_upwards with z
    change E.1 z*V.1 z = (T.1 z*V.1 z-R.1 z*V.1 z)-r*(W.1 z*V.1 z)
    have he' : E.1 z = T.1 z-R.1 z-r*W.1 z := hE z.2
    rw [he']
    ring
  change (∫ z : ↥(standardSphere dim), e.1 z*v.1 z ∂(sphereProbability dim)) =
    ∫ z : ↥(standardSphere dim), u.1 z*h.1 z ∂(sphereProbability dim)
  conv_rhs =>
    arg 2
    ext z
    rw [mul_comm]
  rw [split f b e v he,split g c h u hh]
  have hC := integral_smoothBallConormal_symm hA hSym u v b c hb hc hu hv
  have hF := integral_finiteFlatRadial_symm f g
  have hQ := integral_firstFiniteConormal_symm ell f g
  dsimp only at hF hQ
  conv_rhs at hC => arg 2; ext z; rw [mul_comm]
  conv_rhs at hF => arg 2; ext z; rw [mul_comm]
  conv_rhs at hQ => arg 2; ext z; rw [mul_comm]
  rw [hC,hF,hQ]

end CalderonN
