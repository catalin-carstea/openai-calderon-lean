import Proof.UniformActualFirstErrorAdjointCommutator
import Proof.UniformNativeFirstErrorAdjointHigherEndpoints
import Proof.HigherEndpointBoundTransport
noncomputable section
set_option autoImplicit false
set_option diagnostics false
set_option maxHeartbeats 3800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- A true half-Sobolev adjoint with a genuine bounded higher realization. -/
def HalfAdjointHigherEndpointBound
    (L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (B : ℝ) : Prop :=
  ∃ H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H=
      L.adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧ ‖H‖ ≤ B

/-- Uniform actual physical higher adjoint endpoint and linear-radius
norm for ANY already selected compatible low endpoint. The common
native construction supplies the SAME inclusion-compatible operator. -/
theorem uniform_actual_first_error_adjoint_higher_endpoints {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CS : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CS ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ a : X,
      ∀ R A Ga : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      (∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (Ga x)) →
      ∀ x ∈ Y,
      ∀ La : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (actualFirstAdjointErrorFamily d a A Ga x)=
        La.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) →
      HalfAdjointHigherEndpointBound La (CS*‖a‖*d.radius x) := by
  classical
  obtain ⟨ηT,CF,CA,CM,CQ,CI,CW,F0,hηT,hηT1,hCF,hCA,hCM,hCQ,hCI,hCW,hF0,hNative⟩ :=
    uniform_native_relative_horizontal_taylor_data (Y:=Y) (Ω:=Ω) (m:=m) hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηC,CC,CH,hηC,hηC1,hCC,hCH,hCoeff⟩ :=
    uniform_relative_center_error_coefficient_families (Y:=Y) (Ω:=Ω) (m:=m) hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηV,CFV,CAV,hηV,hηV1,hCFV,hCAV,hSym⟩ :=
    uniform_native_relative_symmetric_higher_data (Y:=Y) (Ω:=Ω) (m:=m) hY hΩ 0 (by omega) K ρ c₀ M Cj hK hρ CI CW hCI hCW F0 hF0
  obtain ⟨Q0,hQ0⟩ := exists_unit_boundary_coefficient
  have hS := uniform_native_first_error_adjoint_higher_endpoints
    (Y:=Y) (Ω:=Ω) (m:=m) hY hΩ hSub hm K ρ c₀ M Cj hK hρ CQ CI CW (zero_le_one.trans hCQ) hCI hCW F0 hF0 Q0 hQ0 CC CH (zero_le_one.trans hCC)
  obtain ⟨ηS,CS,hηS,hηS1,hCS,hSelf⟩ := hS
  refine ⟨min ηT (min ηC (min ηV ηS)),CS,lt_min hηT (lt_min hηC (lt_min hηV hηS)),
    (min_le_left _ _).trans hηT1,hCS,?_⟩
  intro floor hf ε hε hSmall d hd a R A Ga hR hA hGa x hx La hLa
  have hSmallT := hSmall.trans (min_le_left _ _)
  have hSmallC := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallV := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hSmallS := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨s⟩ := hNative floor hf ε hε hSmallT d hd x hx
  obtain ⟨V⟩ := hSym floor hf ε hε hSmallV d hd x hx CQ CF CA CM s
  let Ca : (j : I) → RelativeCenterErrorCoefficientFamily d x a j CC CH :=
    fun j => Classical.choice (hCoeff floor hf ε hε hSmallC d hd x hx a j)
  let p : NormalFrameRelativeParameter := ((x,frameVectorLinear d.frame x),0)
  have hr := (hd.2.2.2.2.1.2 x hx).1.ne'
  have hLaEq := (s.actual_first_error_native_identification V.neighborhood hY hΩ hSub hd.1
    (zero_lt_one.trans_le hK) hx hr hd.2.2.2.2.1.1 Ca R A Ga hR hA hGa hF0 La hLa).2
  change ∃ Ha, _
  exact exists_higher_endpoint_bound_congr
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    ((s.firstAdjointHalfErrorFamily Ca p).adjoint) La.adjoint (CS*‖a‖*d.radius x)
    (congrArg (fun T => T.adjoint) hLaEq.symm)
    (hSelf floor hf ε hε hSmallS d hd x hx CF CA CM s a Ca)

end ShrinkingSpheres
