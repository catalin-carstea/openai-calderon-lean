module

public import Proof.CalderonN.SupportedSphereMultiplierHigherDerivatives
public import Proof.CalderonN.SmoothSupportedFiberJetBounds

import Proof.CalderonN.WeakEnergyConormalJets
import Mathlib.Tactic

/-! A normalized germ supplies both the angular symbol at the point
and all ordinary base derivatives through order two. -/

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

@[expose] def SupportedSphereMultiplierGerm
    (m : ∀ x ∈ Y,SmoothData dim) (x : X dim) (β C : ℝ) : Prop :=
  ∃ (U : Set (X dim)) (f : X dim × X dim → ℝ),
    IsOpen U ∧ x ∈ U ∧ U ⊆ Y ∧ ContDiff ℝ ∞ f ∧
      (∀ y ∈ U,∀ hy : y ∈ Y,∀ z ∈ standardSphere dim,f (y,z) = (m y hy).1 z) ∧
      ∀ z ∈ closedBall (0:X dim) 1,LocalSmoothJetBudget
        (fun p : X dim × X dim => f (x+β⁻¹ • p.1,z+p.2)) 0 4 C

namespace SupportedSphereMultiplierGerm

variable {m : ∀ x ∈ Y,SmoothData dim} {x : X dim} {β C D : ℝ}

theorem enlarge (h : SupportedSphereMultiplierGerm m x β C) (hCD : C ≤ D) :
    SupportedSphereMultiplierGerm m x β D := by
  obtain ⟨U,f,hU,hx,hUY,hf,hRep,hJet⟩ := h
  exact ⟨U,f,hU,hx,hUY,hf,hRep,fun z hz => (hJet z hz).enlarge hCD⟩

theorem angularRepresentative (h : SupportedSphereMultiplierGerm m x β C) :
    ∃ f : SmoothData dim,supportedSphereMultiplierFamily m x = smoothSphereTraceMul f ∧
      ∀ z ∈ closedBall (0:X dim) 1,LocalSmoothJetBudget f.1 z 3 (6*C) := by
  obtain ⟨U,f,hU,hx,hUY,hf,hRep,hJet⟩ := h
  let g := smoothParametricScalarSlice f hf x
  refine ⟨g,?_,?_⟩
  · ext u : 1
    apply Subtype.ext
    funext z
    simp only [supportedSphereMultiplierFamily,dite_eq_left (hUY hx),smoothSphereTraceMul_apply,
      g,smoothParametricScalarSlice,hRep x hx (hUY hx) z.1 z.2]
  · intro z hz
    have h' := localSmoothJetBudget_angular_slice _ (0:X dim) 0 z ((hJet z hz).mono_order (by decide : 3 ≤ 4))
    simpa [g,smoothParametricScalarSlice,Nat.factorial] using h'

theorem angularBaseJets (h : SupportedSphereMultiplierGerm m x β C)
    (hY : IsOpen Y) (hβ : 0 < β) (hC : 0 ≤ C)
    (hM : SmoothSupportedTraceFiberRegular Y (supportedSphereMultiplierFamily m)) (hn : 3 ≤ dim) :
    SmoothSupportedFiberJetBound hn hY x β 2 0 (smoothTraceMultiplierJetConstant dim (2*C))
      ⟨supportedSphereMultiplierFamily m,hM⟩ := by
  intro n hn₂ a ha
  obtain ⟨U,f,hU,hx,hUY,hf,hRep,hJet⟩ := h
  rw [supportedSphereMultiplier_iteratedDerivative_eq_of_eqOn hY m hM hU hUY f hf hRep n a hx]
  let g := smoothParametricScalarSlice (parametricScalarBaseDerivative f n a)
    (contDiff_parametricScalarBaseDerivative f hf n a) x
  let g₀ : SmoothData dim := ⟨fun z => (β⁻¹)^n • g.1 z,(contDiff_const (c:=(β⁻¹)^n)).mul g.2⟩
  have hG (z : X dim) (hz : z ∈ closedBall (0:X dim) 1) :
      LocalSmoothJetBudget g₀.1 z 2 (2*C) := by
    have h' := localSmoothJetBudget_parametric_baseDerivative_slice f hf x z β hβ 2 n a ha
      ((hJet z hz).mono_order (by omega : 2+n ≤ 4))
    have h'' := h'.const_smul ((β⁻¹)^n) (pow_nonneg (inv_nonneg.mpr hβ.le) _)
    have he : (β⁻¹)^n*(((2:ℕ).factorial:ℝ)*C*β^n) = 2*C := by
      rw [inv_pow]
      norm_num
      field_simp
    rw [he] at h''
    exact h''
  have hEq : smoothSphereTraceMul g = β^n • smoothSphereTraceMul g₀ := by
    ext u : 1
    apply Subtype.ext
    funext z
    simp only [LinearMap.smul_apply,Submodule.coe_smul,Pi.smul_apply,smul_eq_mul,smoothSphereTraceMul_apply,g₀]
    rw [← mul_assoc,← mul_assoc,← mul_pow, mul_inv_cancel₀ hβ.ne',one_pow,one_mul]
  change SmoothTraceAngularBound hn 0 _ (smoothSphereTraceMul g)
  rw [hEq]
  have h' := (smoothTraceMultiplier_angularBound_of_jets hn g₀ (2*C) (by positivity) hG).const_smul (β^n)
  rwa [abs_of_nonneg (pow_nonneg hβ.le n),mul_comm] at h'

end SupportedSphereMultiplierGerm

theorem supportedSphereMultiplier_bounds_of_germ (hn : 3 ≤ dim)
    (B : Module.End ℝ (SmoothSphereTrace dim)) (hB : SmoothTraceAdjoint hn B B)
    (hFin : ∀ f,B (finiteHarmonicSmoothTraceL f) = finiteHarmonicSmoothTraceL (finiteHarmonicDegreeL f))
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (hY : IsOpen Y) (x : X dim) (hx : x ∈ Y) (β : ℝ),0 < β →
      ∀ (m : ∀ y ∈ Y,SmoothData dim)
        (hM : SmoothSupportedTraceFiberRegular Y (supportedSphereMultiplierFamily m)),
        SupportedSphereMultiplierGerm m x β A →
        SmoothSupportedTraceCoefficientBounds hn B hY x β 0 C (supportedSphereMultiplierFamily m) hM := by
  obtain ⟨C,hC,hLift⟩ := supportedSphereMultiplier_bounds_of_normalized_jets (Y:=Y) hn B hB hFin A hA
  refine ⟨C,hC,?_⟩
  intro hY x hx β hβ m hM hG
  obtain ⟨U,f,hU,hxU,_,hf,hRep,hJet⟩ := hG
  refine hLift hY x hx β hβ m hM f hf ?_ hJet
  intro z hz
  filter_upwards [hU.mem_nhds hxU] with y hy hyY using hRep y hy hyY z hz

end CalderonN
