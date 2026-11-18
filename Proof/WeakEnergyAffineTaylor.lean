import Proof.FullWeakEnergyContinuity
import Proof.Archive.CoefficientMatrixRegularity
import Proof.NativeWeakInverseBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Matrix
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem nativeZeroFunctionalInverse_eq_inverse (B : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero) :
    nativeZeroFunctionalInverse B = B.inverse := by
  change functionalInverse B = B.inverse
  exact functionalInverse_eq_inverse B

/-- The native weak inverse is the canonical Banach inverse, retaining the
    actual coefficient witness. -/
theorem nativeCoefficientWeakFunctionalInverse_eq_inverse {a : X → Mat}
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) :
    nativeCoefficientWeakFunctionalInverse a 0 0 hcoeff =
      (TauCeti.PDE.energyFormH1L0 (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff).inverse := by
  change nativeZeroFunctionalInverse (nativeZeroCoefficientEnergyL a 0 0 hcoeff) = _
  rw [nativeZeroFunctionalInverse_eq_inverse]
  rfl

/-- A local entry bound supplies the actual weak-energy coefficient witness
    even for the sign-indefinite affine first variation. -/
theorem memLp_coefficient_energy_of_entry_bound (F : SmoothCoefficientMatrix 2) (P : ℝ) (hP : 0 ≤ P)
    (hF : ∀ i j,∀ x ∈ (ballOpens : Set X),|coefficientValue 2 (F i j) x| ≤ P) :
    MemLp (fun x => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F x) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens) := by
  apply TauCeti.PDE.memLp_energyIntegrand_of_bounds (Lam:=9*P) (beta:=0) (gamma:=0)
    (by positivity) (aestronglyMeasurable_coefficientMatrixField 2 F)
    aestronglyMeasurable_const aestronglyMeasurable_const
  · intro x hx eta xi
    exact abs_dotProduct_mulVec_le_of_entry_bound _ P (fun i j => hF i j x hx) eta xi
  · intro x hx
    simp
  · intro x hx
    simp

/-- Pointwise coefficient Taylor errors give quadratic errors of the actual
    bounded full weak energy forms. -/
theorem norm_unitBall_full_energy_affine_remainder_le {a a0 a1 : X → Mat}
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha0 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a0 x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a1 x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (r q : ℝ) (hq : 0 ≤ q)
    (hDiff : ∀ x ∈ (ballOpens : Set X),∀ i j,|(a x-a0 x-r • a1 x) i j| ≤ q) :
    ‖TauCeti.PDE.energyFormH1L ha-TauCeti.PDE.energyFormH1L ha0-r • TauCeti.PDE.energyFormH1L ha1‖ ≤ 9*q := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro u v
  let R := fun x => a x-a0 x-r • a1 x
  have hSub (A B : Mat) (U V : ℝ × X) : TauCeti.PDE.energyIntegrand (A-B) 0 0 U V =
      TauCeti.PDE.energyIntegrand A 0 0 U V-TauCeti.PDE.energyIntegrand B 0 0 U V := by
    simpa only [sub_zero] using TauCeti.PDE.energyIntegrand_sub_apply A B (0:X) 0 (0:ℝ) 0 U V
  have hScale (A : Mat) (U V : ℝ × X) : TauCeti.PDE.energyIntegrand (r • A) 0 0 U V =
      r*TauCeti.PDE.energyIntegrand A 0 0 U V := by
    simpa only [smul_zero,mul_zero] using TauCeti.PDE.energyIntegrand_smul_apply A (0:X) 0 r U V
  have hLine (x : X) : TauCeti.PDE.energyIntegrand (R x) 0 0 (TauCeti.PDE.jetField u x) (TauCeti.PDE.jetField v x) =
      TauCeti.PDE.energyIntegrand (a x) 0 0 (TauCeti.PDE.jetField u x) (TauCeti.PDE.jetField v x)-
      TauCeti.PDE.energyIntegrand (a0 x) 0 0 (TauCeti.PDE.jetField u x) (TauCeti.PDE.jetField v x)-
      r*TauCeti.PDE.energyIntegrand (a1 x) 0 0 (TauCeti.PDE.jetField u x) (TauCeti.PDE.jetField v x) := by
    dsimp only [R]
    rw [hSub,hSub,hScale]
  have hEnergy : TauCeti.PDE.energyFormH1 R 0 0 u v =
      TauCeti.PDE.energyFormH1 a 0 0 u v-TauCeti.PDE.energyFormH1 a0 0 0 u v-
      r*TauCeti.PDE.energyFormH1 a1 0 0 u v := by
    have hf := TauCeti.PDE.integrable_energyIntegrand_jetField ha u v
    have hf0 := TauCeti.PDE.integrable_energyIntegrand_jetField ha0 u v
    have hf1 := TauCeti.PDE.integrable_energyIntegrand_jetField ha1 u v
    have hSplit := integral_sub (hf.sub hf0) (hf1.const_mul r)
    have hSplit0 := integral_sub hf hf0
    simp only [Pi.sub_apply] at hSplit hSplit0
    simp only [TauCeti.PDE.energyFormH1_def,TauCeti.PDE.energyFormIntegral_def,Pi.zero_apply]
    rw [integral_congr_ae (Filter.Eventually.of_forall hLine),hSplit,hSplit0,integral_const_mul]
  change ‖TauCeti.PDE.energyFormH1L ha u v-TauCeti.PDE.energyFormH1L ha0 u v-
    r*TauCeti.PDE.energyFormH1L ha1 u v‖ ≤ _
  rw [TauCeti.PDE.energyFormH1L_apply,TauCeti.PDE.energyFormH1L_apply,TauCeti.PDE.energyFormH1L_apply]
  change ‖TauCeti.PDE.energyFormH1 a 0 0 u v-TauCeti.PDE.energyFormH1 a0 0 0 u v-
    r*TauCeti.PDE.energyFormH1 a1 0 0 u v‖ ≤ _
  rw [← hEnergy]
  have hDot (x : X) (hx : x ∈ (ballOpens : Set X)) (eta xi : X) :
      |eta.ofLp ⬝ᵥ (R x *ᵥ xi.ofLp)| ≤ (9*q)*‖eta‖*‖xi‖ :=
    abs_dotProduct_mulVec_le_of_entry_bound (R x) q (hDiff x hx) eta xi
  have hn := TauCeti.PDE.norm_energyFormH1_le_of_bounds (a:=R) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ))
    (Lam:=9*q) (beta:=0) (gamma:=0) (by positivity) hDot le_rfl le_rfl
    (fun _ _ => by simp) (fun _ _ => by simp) u v
  change ‖TauCeti.PDE.energyFormH1 R (fun _ => (0:X)) (fun _ => (0:ℝ)) u v‖ ≤ _
  exact hn.trans_eq (by ring)

end ShrinkingSpheres
