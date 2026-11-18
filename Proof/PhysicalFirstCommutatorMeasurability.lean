import Proof.PhysicalFirstCommutatorDensity
import Proof.UniformPhysicalFirstCommutatorPacket
import Proof.PhysicalFirstHigherSmooth
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
namespace PhysicalFirstCommutatorPacket
variable {Y Ω : Set X} {d : Data} {CF CT CB CS ε : ℝ}
  {P : PhysicalPrincipalData Y d CF CT}

/-- Chosen low commutators act smoothly on the actual horizontal section,
because their genuine graph identifies the action using smooth endpoints. -/
lemma contDiffOn_apply_horizontal (W : PhysicalFirstCommutatorPacket P CB CS ε)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ} {L : ℂ →L[ℝ] ℝ}
    (Q : AngularComponentData E d.radius L) (i j : I) :
    ContDiffOn ℝ ∞ (fun x => W.commLow i j x (Q.horizontalHalfSection j x)) Y := by
  let U := Q.horizontalThreeHalfSection j
  have hU : ContDiff ℝ ∞ U := contDiff_ambientSobolevSection _ _ _ _
  let Adj : (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) →L[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hAdj := Adj.contDiff.comp_contDiffOn (P.firstDerivativeHalfL_smooth hY hΩ hd hK i)
  have hHigh := P.firstDerivativeHigherL_smooth hY hΩ hd hK j
  have hRight := (hAdj.clm_apply (hHigh.clm_apply hU.contDiffOn)).sub
    ((P.firstDerivativeHalfL_smooth hY hΩ hd hK j).clm_apply ((W.adjoint_smooth i).clm_apply hU.contDiffOn))
  apply hRight.congr
  intro x hx
  have hG := DFunLike.congr_fun (W.comm_graph i j x hx) (U x)
  simp only [ContinuousLinearMap.comp_apply,_root_.sub_apply] at hG
  rw [Q.horizontalThreeHalfSection_inclusion] at hG
  exact hG.symm

lemma contDiffOn_form (W : PhysicalFirstCommutatorPacket P CB CS ε)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ} {L : ℂ →L[ℝ] ℝ}
    (Q : AngularComponentData E d.radius L) :
    ContDiffOn ℝ ∞ (fun x => firstCommutatorForm (fun i j => W.commLow i j x)
      (fun i => Q.horizontalHalfSection i x)) Y := by
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  exact (contDiff_ambientSobolevSection (1/2:ℝ) (by norm_num) _ _).contDiffOn.inner ℝ
    (W.contDiffOn_apply_horizontal hY hΩ hd hK Q i j)

lemma firstCommutatorDensity_aestronglyMeasurable (W : PhysicalFirstCommutatorPacket P CB CS ε)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ}
    (D : AngularModelData E d.radius) :
    AEStronglyMeasurable (D.firstCommutatorDensity W.commLow) (volume.restrict Y) := by
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  exact ((hg.contDiffOn_density hK).mul
    ((W.contDiffOn_form hY hΩ hd hK D.realComponent).add
      (W.contDiffOn_form hY hΩ hd hK D.imagComponent))).continuousOn.aestronglyMeasurable hY.measurableSet
end PhysicalFirstCommutatorPacket
end ShrinkingSpheres
