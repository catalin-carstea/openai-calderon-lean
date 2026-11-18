import Proof.CanonicalPrincipalEnergyReduction
import Mathlib.Analysis.Normed.Module.RCLike.Real
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily

/-- A one-sided quadratic comparison supplies the existential norm partner
of the existing reduction. This partner is only a Hilbert-space vector; no
claim that it is a formal adjoint is made or used. -/
lemma norm_square_partner_of_lower_bound {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (a b w : H) {q : ℝ} (hq : 0 ≤ q)
    (hLower : 4*(‖a‖^2-‖b‖^2) ≤ ‖w‖^2+q) :
    ∃ v : H,|(‖w‖^2-‖v‖^2)-4*(‖a‖^2-‖b‖^2)| ≤ q := by
  classical
  by_cases hSub : Subsingleton H
  · letI := hSub
    refine ⟨0,?_⟩
    have ha : a=0 := Subsingleton.elim _ _
    have hb : b=0 := Subsingleton.elim _ _
    have hw : w=0 := Subsingleton.elim _ _
    simpa only [ha,hb,hw,norm_zero,zero_pow,sub_self,mul_zero,abs_zero] using hq
  · letI : Nontrivial H := not_subsingleton_iff_nontrivial.mp hSub
    let δ := ‖w‖^2-4*(‖a‖^2-‖b‖^2)
    by_cases hδ : 0 ≤ δ
    · obtain ⟨v,hv⟩ := exists_norm_eq H (Real.sqrt_nonneg δ)
      refine ⟨v,?_⟩
      rw [hv,Real.sq_sqrt hδ]
      have hZero : (‖w‖^2-δ)-4*(‖a‖^2-‖b‖^2)=0 := by dsimp only [δ];ring
      rw [hZero,abs_zero]
      exact hq
    · refine ⟨0,?_⟩
      rw [norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),sub_zero]
      change |δ| ≤ q
      rw [abs_of_nonpos (le_of_not_ge hδ)]
      dsimp only [δ]
      linarith

/-- The exact lower bound needed after dropping the nonnegative partner
norm in the manuscript. It still quantifies over every admitted profile,
the actual principal output and the SAME canonical correction J. -/
def UniformCanonicalPrincipalLowerBound (Y Ω : Set X) (K ρ c₀ : ℝ) {m : ℕ}
    (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) : Prop :=
  ∃ Q : SmoothCoefficientJets 2,∃ B η CE : ℝ,
    (∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[nhds z] (fun _ => (1:ℝ))) ∧
    0 < η ∧ 0 ≤ CE ∧
    ∀ floor,B ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ φ,Test Y d.γ d.frame φ →
      ∀ (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) (O : AngularProductOutputs D)
        (PP : PhysicalOutputRealization Y d.γ d.frame (principalMovingTrace d.γ d.g₂ d.radius d.adjoint φ)),
      ∀ J : SobolevFamilyOutput d E (fun x => firstCorrectionCrossRemainderL Q d x),
        let P0 : Output Y d := PP.output
        4*(‖O.raisingOutput‖^2-‖O.loweringOutput‖^2) ≤
          ‖P0-J.output‖^2+CE*ε*(energyNorm Y d φ)^2

theorem uniformCanonicalPrincipalEnergy_of_lowerBound {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hLower : UniformCanonicalPrincipalLowerBound Y Ω K ρ c₀ M Cj) :
    UniformCanonicalPrincipalEnergy Y Ω K ρ c₀ M Cj := by
  obtain ⟨Q,B,η,CE,hQ,hη,hCE,hProduce⟩ := hLower
  refine ⟨Q,B,η,CE,hQ,hη,hCE,?_⟩
  intro floor hf ε hε hSmall d hd φ hφ E D O PP J
  let P0 : Output Y d := PP.output
  let W : Output Y d := P0-J.output
  obtain ⟨V,hV⟩ := norm_square_partner_of_lower_bound O.raisingOutput O.loweringOutput W
    (show 0 ≤ CE*ε*(energyNorm Y d φ)^2 by positivity)
    (hProduce floor hf ε hε hSmall d hd φ hφ E D O PP J)
  refine ⟨V-(2:ℝ) • O.loweringOutput,?_⟩
  have hW : (2:ℝ) • O.raisingOutput+canonicalPrincipalPerturbation O.raisingOutput P0 J.output=W := by
    dsimp only [canonicalPrincipalPerturbation,W]
    abel
  have hPartner : (2:ℝ) • O.loweringOutput+(V-(2:ℝ) • O.loweringOutput)=V := by abel
  change |(‖(2:ℝ) • O.raisingOutput+canonicalPrincipalPerturbation O.raisingOutput P0 J.output‖^2-
    ‖(2:ℝ) • O.loweringOutput+(V-(2:ℝ) • O.loweringOutput)‖^2)-
    4*(‖O.raisingOutput‖^2-‖O.loweringOutput‖^2)| ≤ CE*ε*(energyNorm Y d φ)^2
  rw [hW,hPartner]
  exact hV

theorem uniformCanonicalPrincipalLowerBound_of_energy {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hEnergy : UniformCanonicalPrincipalEnergy Y Ω K ρ c₀ M Cj) :
    UniformCanonicalPrincipalLowerBound Y Ω K ρ c₀ M Cj := by
  obtain ⟨Q,B,η,CE,hQ,hη,hCE,hProduce⟩ := hEnergy
  refine ⟨Q,B,η,CE,hQ,hη,hCE,?_⟩
  intro floor hf ε hε hSmall d hd φ hφ E D O PP J
  let P0 : Output Y d := PP.output
  obtain ⟨Ud,hBound⟩ := hProduce floor hf ε hε hSmall d hd φ hφ E D O PP J
  have hW : (2:ℝ) • O.raisingOutput+canonicalPrincipalPerturbation O.raisingOutput P0 J.output=
      P0-J.output := by dsimp only [canonicalPrincipalPerturbation];abel
  change |(‖(2:ℝ) • O.raisingOutput+canonicalPrincipalPerturbation O.raisingOutput P0 J.output‖^2-
    ‖(2:ℝ) • O.loweringOutput+Ud‖^2)-4*(‖O.raisingOutput‖^2-‖O.loweringOutput‖^2)| ≤
    CE*ε*(energyNorm Y d φ)^2 at hBound
  rw [hW] at hBound
  have h := (abs_le.mp hBound).1
  nlinarith [sq_nonneg ‖(2:ℝ) • O.loweringOutput+Ud‖]

theorem uniformEstimate_of_canonicalPrincipalLowerBound {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hSub : Y ⊆ Ω) {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (hc₀ : 0 < c₀)
    (hLower : UniformCanonicalPrincipalLowerBound Y Ω K ρ c₀ M Cj) :
    ∃ floor ε₀ C : ℝ,1 ≤ floor ∧ 0 < ε₀ ∧ 0 < C ∧ UniformEstimate Y Ω K ρ c₀ M Cj floor ε₀ C :=
  uniformEstimate_of_canonicalPrincipalEnergy hY hΩ hSub hm K ρ c₀ M Cj hK hρ hc₀
    (uniformCanonicalPrincipalEnergy_of_lowerBound hLower)
end ShrinkingSpheres
