import Proof.FirstConormalGreen
import Proof.FlatNativeWeakData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativePolynomialBulkMoments
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeWeakHalfLift nativeCoefficientWeakFunctionalInverse
  nativeCoefficientWeakEnergyL

/-- Replacing the fixed harmonic test lift by the actual weak solution does
    not change its energy pairing: their difference has zero boundary trace. -/
theorem nativeWeakEnergy_fixed_test_eq_solution_test {a : X → Mat}
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 ha))
    (f g : SphereSobolev (1/2:ℝ)) :
    TauCeti.PDE.energyFormH1 a 0 0 (nativeWeakHalfLift a 0 0 ha sphereFischerInner f) (fixedHarmonicH1LiftL g) =
      TauCeti.PDE.energyFormH1 a 0 0 (nativeWeakHalfLift a 0 0 ha sphereFischerInner f)
        (nativeWeakHalfLift a 0 0 ha sphereFischerInner g) := by
  let P := nativeWeakHalfLift a 0 0 ha sphereFischerInner
  let E := TauCeti.PDE.energyFormH1L ha
  let v : BallH1Zero := ⟨fixedHarmonicH1LiftL g-P g,
    nativeWeakHalfLift_affine_difference a 0 0 ha sphereFischerInner g⟩
  have hz := nativeWeakHalfLift_weak_solution a 0 0 ha sphereFischerInner
    (canonicalWeakEnergy_isInvertible ha hc) f v
  have hE : E (P f) (fixedHarmonicH1LiftL g-P g) = 0 :=
    (TauCeti.PDE.energyFormH1L_apply ha (P f) (fixedHarmonicH1LiftL g-P g)).trans hz
  have hSub : E (P f) (fixedHarmonicH1LiftL g)-E (P f) (P g) = 0 :=
    ((E (P f)).map_sub _ _).symm.trans hE
  exact (TauCeti.PDE.energyFormH1L_apply ha (P f) (fixedHarmonicH1LiftL g)).symm.trans
    ((sub_eq_zero.mp hSub).trans (TauCeti.PDE.energyFormH1L_apply ha (P f) (P g)))

/-- The actual weak conormal endpoint is symmetric for symmetric zero-drift
    coefficients, in the genuine positive/negative-half sphere pairing. -/
theorem nativeWeakConormal_symmetric {a : X → Mat}
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 ha))
    (hs : ∀ᵐ x ∂((volume:Measure X).restrict ballOpens),(a x).IsSymm)
    (f g : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) g (nativeWeakConormalEndpoint a 0 0 ha sphereFischerInner f) =
      sphereSobolevDualPairing (1/2:ℝ) f (nativeWeakConormalEndpoint a 0 0 ha sphereFischerInner g) := by
  have hfg := nativeWeakEnergy_fixed_test_eq_solution_test ha hc f g
  have hgf := nativeWeakEnergy_fixed_test_eq_solution_test ha hc g f
  have hSym := TauCeti.PDE.energyFormH1_comm_of_isSymm_ae (a:=a) (c:=fun _ => (0:ℝ)) hs
    (nativeWeakHalfLift a 0 0 ha sphereFischerInner f) (nativeWeakHalfLift a 0 0 ha sphereFischerInner g)
  have hEnergy := hfg.trans (hSym.trans hgf.symm)
  exact (sphereSobolevDualPairing_nativeWeakConormalEndpoint a 0 0 ha sphereFischerInner f g).trans
    ((congrArg (fun t : ℝ => sphereSurfaceMass⁻¹*t) hEnergy).trans
      (sphereSobolevDualPairing_nativeWeakConormalEndpoint a 0 0 ha sphereFischerInner g f).symm)

theorem weakFirstPoissonVariation_mem_zero (c : ℝ) {a1 : X → Mat}
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a1 x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (f : SphereSobolev (1/2:ℝ)) :
    weakFirstPoissonVariationL c a1 ha1 f ∈ TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2 := by
  let z := nativeCoefficientWeakFunctionalInverse (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)
    (nativeCoefficientWeakEnergyL a1 0 0 ha1 (fixedHarmonicH1LiftL f))
  change -((z:BallH1)) ∈ TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2
  exact (TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).neg_mem z.property

/-- The first solution variation contributes zero against a flat harmonic
    test lift; only the first coefficient energy remains. -/
theorem flatEnergy_firstPoisson_test_eq_zero (c : ℝ) {a1 : X → Mat}
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a1 x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (f g : SphereSobolev (1/2:ℝ)) :
    TauCeti.PDE.energyFormH1 (fun _ : X => c • (1:Mat)) 0 0
      (weakFirstPoissonVariationL c a1 ha1 f) (fixedHarmonicH1LiftL g) = 0 := by
  let v : BallH1Zero := ⟨weakFirstPoissonVariationL c a1 ha1 f,weakFirstPoissonVariation_mem_zero c ha1 f⟩
  have hs : ∀ᵐ x ∂((volume:Measure X).restrict ballOpens),((fun _ : X => c • (1:Mat)) x).IsSymm :=
    Filter.Eventually.of_forall (fun _ => Matrix.isSymm_one.smul c)
  have hSym := TauCeti.PDE.energyFormH1_comm_of_isSymm_ae (a:=fun _ : X => c • (1:Mat))
    (c:=fun _ => (0:ℝ)) hs (weakFirstPoissonVariationL c a1 ha1 f) (fixedHarmonicH1LiftL g)
  exact hSym.trans (fixedHarmonicH1Lift_flat_weak c g v)

theorem weakFirstConormal_coefficient_pairing (c : ℝ) {a1 : X → Mat}
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a1 x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (f g : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) g (weakFirstConormalVariationL c a1 ha1 f) =
      sphereSurfaceMass⁻¹*TauCeti.PDE.energyFormH1 a1 0 0 (fixedHarmonicH1LiftL f) (fixedHarmonicH1LiftL g) := by
  have h := weakFirstConormal_dualPairing c ha1 f g
  have hz := flatEnergy_firstPoisson_test_eq_zero c ha1 f g
  have hSum := (congrArg (fun t : ℝ => t+
    TauCeti.PDE.energyFormH1 a1 0 0 (fixedHarmonicH1LiftL f) (fixedHarmonicH1LiftL g)) hz).trans (zero_add _)
  exact h.trans (congrArg (fun t : ℝ => sphereSurfaceMass⁻¹*t) hSum)

theorem weakFirstConormal_symmetric (c : ℝ) {a1 : X → Mat}
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a1 x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hs : ∀ᵐ x ∂((volume:Measure X).restrict ballOpens),(a1 x).IsSymm)
    (f g : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) g (weakFirstConormalVariationL c a1 ha1 f) =
      sphereSobolevDualPairing (1/2:ℝ) f (weakFirstConormalVariationL c a1 ha1 g) := by
  have hSym := TauCeti.PDE.energyFormH1_comm_of_isSymm_ae (a:=a1) (c:=fun _ => (0:ℝ)) hs
    (fixedHarmonicH1LiftL f) (fixedHarmonicH1LiftL g)
  exact (weakFirstConormal_coefficient_pairing c ha1 f g).trans
    ((congrArg (fun t : ℝ => sphereSurfaceMass⁻¹*t) hSym).trans
      (weakFirstConormal_coefficient_pairing c ha1 g f).symm)

/-- The first conormal correction depends only on the first coefficient on
    the actual ball, independently of any exterior compact extension. -/
theorem weakFirstConormal_congr_on_ball (c : ℝ) {a1 b1 : X → Mat}
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a1 x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hb1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (b1 x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hPoint : ∀ x ∈ (ballOpens:Set X),a1 x = b1 x) :
    weakFirstConormalVariationL c a1 ha1 = weakFirstConormalVariationL c b1 hb1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℝ
  intro g
  change sphereSobolevDualPairing (1/2:ℝ) g _ = sphereSobolevDualPairing (1/2:ℝ) g _
  have hEnergy := energyFormH1_congr_coeff_on hPoint (fixedHarmonicH1LiftL f) (fixedHarmonicH1LiftL g)
  exact (weakFirstConormal_coefficient_pairing c ha1 f g).trans
    ((congrArg (fun t : ℝ => sphereSurfaceMass⁻¹*t) hEnergy).trans
      (weakFirstConormal_coefficient_pairing c hb1 f g).symm)

theorem fixedLowRadial_symmetric (f g : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) g (fixedLowRadialL f) =
      sphereSobolevDualPairing (1/2:ℝ) f (fixedLowRadialL g) := by
  have h0 := flat_native_weak_energy_data 1 (by norm_num)
  exact nativeWeakConormal_symmetric (flatCoefficientBound 1) h0.coercive
    (Filter.Eventually.of_forall (fun _ => Matrix.isSymm_one.smul (1:ℝ))) f g

/-- Subtracting the symmetric flat and first-coefficient terms preserves the
    actual conormal remainder's symmetry. -/
theorem nativeConormalTaylor_remainder_symmetric {a a1 : X → Mat}
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a1 x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 ha))
    (hs : ∀ᵐ x ∂((volume:Measure X).restrict ballOpens),(a x).IsSymm)
    (hs1 : ∀ᵐ x ∂((volume:Measure X).restrict ballOpens),(a1 x).IsSymm)
    (c r : ℝ) (f g : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) g
      ((nativeWeakConormalEndpoint a 0 0 ha sphereFischerInner-c • fixedLowRadialL-
        r • weakFirstConormalVariationL c a1 ha1) f) =
    sphereSobolevDualPairing (1/2:ℝ) f
      ((nativeWeakConormalEndpoint a 0 0 ha sphereFischerInner-c • fixedLowRadialL-
        r • weakFirstConormalVariationL c a1 ha1) g) := by
  have h0 := nativeWeakConormal_symmetric ha hc hs f g
  have h1 := fixedLowRadial_symmetric f g
  have h2 := weakFirstConormal_symmetric c ha1 hs1 f g
  have h01 := congrArg₂ (fun x y : ℝ => x-c*y) h0 h1
  have hAll := congrArg₂ (fun x y : ℝ => x-r*y) h01 h2
  simpa only [_root_.sub_apply,_root_.smul_apply,sphereSobolevDualPairing,
    inner_sub_right,real_inner_smul_right] using hAll

end ShrinkingSpheres
