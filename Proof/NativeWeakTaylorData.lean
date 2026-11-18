import Proof.WeakFirstVariationNorm
import Proof.FlatNativeWeakData
import Proof.FlatCanonicalWeakInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

structure NativeWeakTaylorData (a a1 : X → Mat) (c r CW DA P Q CP1 CP2 : ℝ) : Prop where
  energy : NativeWeakEnergyData a CW DA
  first_coefficient_bound : MemLp (fun x => TauCeti.PDE.energyIntegrand (a1 x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens)
  first_energy_bound : ‖TauCeti.PDE.energyFormH1L first_coefficient_bound‖ ≤ 9*P
  energy_difference_bound : ‖TauCeti.PDE.energyFormH1L energy.coefficient_bound-
    TauCeti.PDE.energyFormH1L (flatCoefficientBound c)‖ ≤ (9*P+9*Q)*r
  energy_remainder_bound : ‖TauCeti.PDE.energyFormH1L energy.coefficient_bound-
    TauCeti.PDE.energyFormH1L (flatCoefficientBound c)-r • TauCeti.PDE.energyFormH1L first_coefficient_bound‖ ≤ (9*Q)*r^2
  first_poisson_bound : ‖weakFirstPoissonVariationL c a1 first_coefficient_bound‖ ≤ CP1
  poisson_remainder_bound : ‖nativeWeakHalfLift a 0 0 energy.coefficient_bound sphereFischerInner-
    fixedHarmonicH1LiftL-r • weakFirstPoissonVariationL c a1 first_coefficient_bound‖ ≤ CP2*r^2


/-- Raw entry estimates used by the native zero-energy derivative caller. -/
structure RawAffineCoefficientBounds (a a1 : X → Mat) (c r P Q : ℝ) : Prop where
  first : ∀ x ∈ (ballOpens:Set X),∀ i j,|a1 x i j| ≤ P
  remainder : ∀ x ∈ (ballOpens:Set X),∀ i j,|(a x-c • (1:Mat)-r • a1 x) i j| ≤ Q*r^2
  difference : ∀ x ∈ (ballOpens:Set X),∀ i j,|a x i j-(c • (1:Mat)) i j| ≤ (P+Q)*r

/-- Shared weak affine Taylor construction from the SAME coefficient energy
    witness and entry estimates; used by both actual and normalized producers. -/
theorem nativeWeakTaylorData_with_entries_of_affine_bounds {a a1 : X → Mat}
    (c r CW DA C0 P Q : ℝ) (hc : 0 < c) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hCW : 0 ≤ CW) (hC0 : 0 ≤ C0) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (e : NativeWeakEnergyData a CW DA)
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a1 x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hFlatInv : ‖nativeCoefficientWeakFunctionalInverse (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)‖ ≤ C0)
    (hA1 : ∀ x ∈ (ballOpens:Set X),∀ i j,|a1 x i j| ≤ P)
    (hR : ∀ x ∈ (ballOpens:Set X),∀ i j,|(a x-c • (1:Mat)-r • a1 x) i j| ≤ Q*r^2) :
    NativeWeakTaylorData a a1 c r CW DA P Q
      (C0*(9*P)*‖fixedHarmonicH1LiftL‖)
      (CW*(9*Q+C0*(9*(P+Q))*(9*P))*‖fixedHarmonicH1LiftL‖) ∧ RawAffineCoefficientBounds a a1 c r P Q := by
  have e0 := flat_native_weak_energy_data c hc
  have hDiff (x : X) (hx : x ∈ (ballOpens:Set X)) (i j : I) : |a x i j-(c • (1:Mat)) i j| ≤ (P+Q)*r := by
    have hAlg : a x i j-(c • (1:Mat)) i j = (a x-c • (1:Mat)-r • a1 x) i j+r*a1 x i j := by
      simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
      ring
    rw [hAlg]
    calc
      _ ≤ |(a x-c • (1:Mat)-r • a1 x) i j|+|r*a1 x i j| := abs_add_le _ _
      _ ≤ Q*r^2+r*P := add_le_add (hR x hx i j) (by rw [abs_mul,abs_of_nonneg hr];gcongr;exact hA1 x hx i j)
      _ ≤ Q*r+r*P := by gcongr;nlinarith only [mul_le_mul_of_nonneg_left hr1 hr]
      _ = _ := by ring
  have hFirst := norm_weakFirstPoissonVariationL_le c ha1 C0 P hC0 hP hFlatInv hA1
  have hPoisson := norm_nativeWeakHalfLift_first_remainder_le (a:=a) (a1:=a1) e.coefficient_bound ha1 c r CW C0 (P+Q) P Q
    hr hCW hC0 (add_nonneg hP hQ) hP hQ e.coercive e0.coercive e.inverse_bound hFlatInv hDiff hA1 hR
  have hEnergy := norm_unitBall_full_energy_affine_remainder_le (a:=a) (a0:=fun _ : X => c • (1:Mat)) (a1:=a1)
    e.coefficient_bound (flatCoefficientBound c) ha1 r (Q*r^2) (mul_nonneg hQ (sq_nonneg _)) hR
  have hEDiff := norm_unitBall_full_energyForm_sub_le (a:=a) (a0:=fun _ : X => c • (1:Mat))
    e.coefficient_bound (flatCoefficientBound c) ((P+Q)*r) (mul_nonneg (add_nonneg hP hQ) hr) hDiff
  refine ⟨?_,⟨hA1,hR,hDiff⟩⟩
  refine ⟨e,ha1,(norm_nativeWeakEnergyL_of_entries (a:=a1) ha1 P hP hA1).1,
    hEDiff.trans_eq ?_,hEnergy.trans_eq ?_,hFirst,hPoisson⟩ <;> ring

theorem nativeWeakTaylorData_of_affine_bounds {a a1 : X → Mat}
    (c r CW DA C0 P Q : ℝ) (hc : 0 < c) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hCW : 0 ≤ CW) (hC0 : 0 ≤ C0) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (e : NativeWeakEnergyData a CW DA)
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a1 x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hFlatInv : ‖nativeCoefficientWeakFunctionalInverse (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)‖ ≤ C0)
    (hA1 : ∀ x ∈ (ballOpens:Set X),∀ i j,|a1 x i j| ≤ P)
    (hR : ∀ x ∈ (ballOpens:Set X),∀ i j,|(a x-c • (1:Mat)-r • a1 x) i j| ≤ Q*r^2) :
    NativeWeakTaylorData a a1 c r CW DA P Q
      (C0*(9*P)*‖fixedHarmonicH1LiftL‖)
      (CW*(9*Q+C0*(9*(P+Q))*(9*P))*‖fixedHarmonicH1LiftL‖) :=
  (nativeWeakTaylorData_with_entries_of_affine_bounds c r CW DA C0 P Q hc hr hr1 hCW hC0 hP hQ e ha1 hFlatInv hA1 hR).1

end ShrinkingSpheres
