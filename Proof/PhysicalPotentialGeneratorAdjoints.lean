import Proof.PhysicalPotentialGeneratorBounds
import Proof.DegreeAdjointHigherEndpoint
import Proof.UniformFlatRaisingAdjointHigherEndpoints
import Proof.UniformFrameFirstErrorAdjointHigherEndpoints
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- All seven actual potential generators have genuine bounded higher
adjoints, with the radius weight retained on each first-error generator. -/
structure PhysicalPotentialGeneratorAdjoints {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (y : X) (C : ℝ) where
  high : PhysicalPotentialGeneratorIndex → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  compatible : ∀ a,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (high a)=
    (P.potentialGeneratorLow y a).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  bound : ∀ a,‖high a‖ ≤ C*potentialGeneratorWeight (d.radius y) a

lemma physical_potential_generator_adjoints {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (y : X) {CR CE : ℝ} (hr : 0 ≤ d.radius y)
    (hR : ∀ j,HalfAdjointHigherEndpointBound (flatHalfRaisingL j) CR)
    (hE : ∀ j,HalfAdjointHigherEndpointBound (P.first.low j y) (CE*d.radius y)) :
    Nonempty (PhysicalPotentialGeneratorAdjoints P y (2+|CR|+|CE|)) := by
  classical
  choose AR hAR hARN using hR
  choose AE hAE hAEN using hE
  let H : PhysicalPotentialGeneratorIndex → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
    | .inl _ => degreeHigherL
    | .inr (.inl j) => AR j
    | .inr (.inr j) => AE j
  have h2 : 2 ≤ 2+|CR|+|CE| := by linarith only [abs_nonneg CR,abs_nonneg CE]
  have hCR : CR ≤ 2+|CR|+|CE| := by linarith only [le_abs_self CR,abs_nonneg CE]
  have hCE : CE ≤ 2+|CR|+|CE| := by linarith only [le_abs_self CE,abs_nonneg CR]
  refine ⟨{high := H,compatible := ?_,bound := ?_}⟩
  · intro a
    rcases a with u | (j | j)
    · exact degreeHigherL_adjoint_pair
    · exact hAR j
    · exact hAE j
  · intro a
    rcases a with u | (j | j)
    · exact norm_degreeHigherL_le_two.trans (by simpa only [potentialGeneratorWeight,mul_one] using h2)
    · exact (hARN j).trans (by simpa only [potentialGeneratorWeight,mul_one] using hCR)
    · exact (hAEN j).trans (mul_le_mul_of_nonneg_right hCE hr)

/-- Common closed production for all actual potential generators and ANY
already selected physical principal data. No additional coefficient premise
or derivative of the arbitrary smooth frame is introduced. -/
theorem uniform_physical_potential_generator_adjoints {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ CF CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,∀ y ∈ Y,
      Nonempty (PhysicalPotentialGeneratorAdjoints P y C) := by
  have hT := uniform_native_relative_horizontal_taylor_data (Y:=Y) (Ω:=Ω) (m:=m)
    hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηT,CFT,CAT,CMT,CQ,CI,CW,F0,hηT,hηT1,hCFT,hCAT,hCMT,hCQ,hCI,hCW,hF0,hNative⟩ := hT
  obtain ⟨Q0,hQ0⟩ := exists_unit_boundary_coefficient
  have hR := uniform_flat_raising_adjoint_higher_endpoints hY hΩ hSub hm K ρ c₀ M Cj hK hρ
    CQ CI CW (zero_le_one.trans hCQ) hCI hCW F0 hF0 Q0 hQ0
  obtain ⟨ηR,CR,hηR,hηR1,hCR,hRaising⟩ := hR
  have hE := uniform_actual_frame_first_error_adjoint_higher_endpoints hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,CE,hηE,hηE1,hCE,hError⟩ := hE
  refine ⟨min ηT (min ηR ηE),2+|CR|+|CE|,lt_min hηT (lt_min hηR hηE),
    (min_le_left _ _).trans hηT1,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P y hy
  obtain ⟨s⟩ := hNative floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  exact physical_potential_generator_adjoints P y (hd.2.2.2.2.1.2 y hy).1.le
    (hRaising floor hf ε hε (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
      d hd y hy CFT CAT CMT s)
    (hError floor hf ε hε (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
      d hd P.radial P.adjoint P.center P.radial_actual P.adjoint_pair P.center_actual CF P.first y hy)
end ShrinkingSpheres
