import Proof.NativeRelativeDegreeHigherData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- Every previously selected native physical packet has a smooth actual
    half-order degree-commutator family with uniformly gained mixed jets.
    All constants precede the geometry and the chosen packet. -/
theorem uniform_native_relative_degree_higher_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (N : ℕ) (hNm : N+6 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CI CW : ℝ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) :
    ∃ η CF CA CD : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ CF ∧ 1 ≤ CA ∧ 1 ≤ CD ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CQ CF0 CA0 CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF0 CA0 CM,
      ∃ V : s.response.SymmetricAdjointDomain,
        (∀ n : ℕ,n ≤ N+1 →
          ‖iteratedFDeriv ℝ n s.response.forwardTaylor ((y,frameVectorLinear d.frame y),0)‖ ≤ CF*(d.radius y)^2) ∧
        (∀ n : ℕ,n ≤ N+1 →
          ‖iteratedFDeriv ℝ n s.response.adjointTaylor ((y,frameVectorLinear d.frame y),0)‖ ≤ CA*(d.radius y)^2) ∧
        (∀ n : ℕ,n ≤ N →
          ‖iteratedFDeriv ℝ n (V.degreeFamily hd.1.1 (zero_lt_one.trans_le hK) (by norm_num))
            ((y,frameVectorLinear d.frame y),0)‖ ≤ CD*(d.radius y)^2) := by
  obtain ⟨η,CF,CA,hη,hη1,hCF,hCA,hHigher⟩ :=
    uniform_native_relative_symmetric_higher_data hY hΩ (N+1) (by omega)
      K ρ c₀ M Cj hK hρ CI CW hCI hCW F0 hF0
  obtain ⟨CG,hCG,hAngular⟩ := uniform_relative_angular_derivative_higher_jets
    (E := SphereSobolev 1 →L[ℝ] SphereSobolev 0) hΩ N (by omega) K M hK
  let BD := CF+CG*(CF+CA)
  let CD := 1+(12*Real.sqrt 2)*BD
  have hCF0 : 0 ≤ CF := zero_le_one.trans hCF
  have hCA0 : 0 ≤ CA := zero_le_one.trans hCA
  have hCG0 : 0 ≤ CG := zero_le_one.trans hCG
  have hBD : 0 ≤ BD := by dsimp only [BD];positivity
  have hCD : 1 ≤ CD := by
    have hh : 0 ≤ (12*Real.sqrt 2)*BD := by positivity
    dsimp only [CD];linarith only [hh]
  have hFBD : CF ≤ BD := by dsimp only [BD];nlinarith only [mul_nonneg hCG0 (add_nonneg hCF0 hCA0)]
  have hCBD : CG*CF ≤ BD := by dsimp only [BD];nlinarith only [hCF0,mul_nonneg hCG0 hCA0]
  have hABD : CG*CA ≤ BD := by dsimp only [BD];nlinarith only [hCF0,mul_nonneg hCG0 hCF0]
  refine ⟨η,CF,CA,CD,hη,hη1,hCF,hCA,hCD,?_⟩
  intro floor hf ε hε hSmall d hd y hy CQ CF0 CA0 CM s
  obtain ⟨H⟩ := hHigher floor hf ε hε hSmall d hd y hy CQ CF0 CA0 CM s
  let V := H.neighborhood
  let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  have he (i j : I) : metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j)) = if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using
      hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy) i j
  have hForward := hAngular d.γ d.g₁ d.g₂ d.frame hd.1 y (hd.2.1.center_mem hy)
    (frameVectorLinear d.frame y) he s.response.forwardTaylor s.response.contDiffAt_forwardTaylor
    (CF*(d.radius y)^2) (by positivity) H.forwardJets
  have hAdjoint := hAngular d.γ d.g₁ d.g₂ d.frame hd.1 y (hd.2.1.center_mem hy)
    (frameVectorLinear d.frame y) he s.response.adjointTaylor s.response.contDiffAt_adjointTaylor
    (CA*(d.radius y)^2) (by positivity) H.adjointJets
  refine ⟨V,H.forwardJets,H.adjointJets,?_⟩
  intro n hn
  have hData : ‖iteratedFDeriv ℝ n s.response.degreeData p0‖ ≤ BD*(d.radius y)^2 :=
    s.response.norm_iteratedFDeriv_degreeData_le p0 s.response.contDiffAt_forwardTaylor
      (fun ij => (hForward ij.1 ij.2).1) (fun ij => (hAdjoint ij.1 ij.2).1)
      n (BD*(d.radius y)^2) (by positivity)
      ((H.forwardJets n (by omega)).trans (mul_le_mul_of_nonneg_right hFBD (sq_nonneg _)))
      (fun ij => ((hForward ij.1 ij.2).2 n hn).trans
        (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hCBD (sq_nonneg (d.radius y))))
      (fun ij => ((hAdjoint ij.1 ij.2).2 n hn).trans
        (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hABD (sq_nonneg (d.radius y))))
  have hh := CoarseDegreeCompatibility.norm_iteratedFDeriv_halfFamily_le s.response.degreeData
    V.domain V.domainOpen (V.degreeData_constraint hd.1.1 (zero_lt_one.trans_le hK) (by norm_num))
    (V.contDiffOn_degreeData hΩ hd.1.1 (zero_lt_one.trans_le hK)) p0 V.pointMem
    (BD*(d.radius y)^2) (by positivity) n hData
  have hConst : (12*Real.sqrt 2)*BD ≤ CD := by dsimp only [CD];linarith
  exact hh.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hConst (sq_nonneg (d.radius y)))

end ShrinkingSpheres
