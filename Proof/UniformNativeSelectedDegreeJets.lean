import Proof.NativeDegreeRotationGraph
import Proof.UniformNativeRelativeDegreeHigherData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The common native degree jet producer works for ANY already selected
domain. Exact physical block/germ uniqueness transfers the bounds without
changing the native packet or introducing a new degree commutator witness. -/
theorem uniform_native_selected_degree_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (N : ℕ) (hNm : N+6 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CI CW : ℝ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1) :
    ∃ η CD : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ CD ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CQ CF CA CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      ∀ V : s.response.SymmetricAdjointDomain,
      SmoothFiniteJetBound (V.degreeFamily hd.1.1 (zero_lt_one.trans_le hK) (by norm_num))
        ((y,frameVectorLinear d.frame y),0) N (CD*(d.radius y)^2) := by
  obtain ⟨η,CFD,CAD,CD,hη,hη1,hCFD,hCAD,hCD,hDegree⟩ := uniform_native_relative_degree_higher_data
    hY hΩ N hNm K ρ c₀ M Cj hK hρ CI CW hCI hCW F0 hF0
  refine ⟨η,CD,hη,hη1,hCD,?_⟩
  intro floor hf ε hε hSmall d hd y hy CQ CF CA CM s V
  obtain ⟨W,hFJ,hAJ,hDJ⟩ := hDegree floor hf ε hε hSmall d hd y hy CQ CF CA CM s
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  have hGerm := V.degreeFamily_germ_eq W hd.1.1 (zero_lt_one.trans_le hK) (by norm_num) p V.pointMem W.pointMem
  refine ⟨mul_nonneg (zero_le_one.trans hCD) (sq_nonneg _),
    (V.contDiffOn_degreeFamily hΩ hd.1.1 (zero_lt_one.trans_le hK) (by norm_num)).contDiffAt
      (V.domainOpen.mem_nhds V.pointMem),?_⟩
  intro n hn
  rw [(hGerm.iteratedFDeriv ℝ n).eq_of_nhds]
  exact hDJ n hn
end ShrinkingSpheres
