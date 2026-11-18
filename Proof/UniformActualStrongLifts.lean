import Proof.UniformActualStrongInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

lemma energyFormH1_congr_coeff_on {a a0 : X → Mat}
    (hEq : ∀ x ∈ (ballOpens : Set X),a x = a0 x) (u v : BallH1) :
    TauCeti.PDE.energyFormH1 a (fun _ => (0:X)) (fun _ => (0:ℝ)) u v =
      TauCeti.PDE.energyFormH1 a0 (fun _ => (0:X)) (fun _ => (0:ℝ)) u v := by
  have hAE : a =ᵐ[(volume : Measure X).restrict ballOpens] a0 := by
    filter_upwards [ae_restrict_mem ballOpens.isOpen.measurableSet] with x hx
    exact hEq x hx
  unfold TauCeti.PDE.energyFormH1
  exact TauCeti.PDE.energyFormIntegral_congr_ae ((volume : Measure X).restrict ballOpens)
    a (fun _ => (0:X)) (fun _ => (0:ℝ)) (TauCeti.PDE.jetField u) (TauCeti.PDE.jetField v)
    hAE Filter.EventuallyEq.rfl
    Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl

/-- Uniformly bounded strong lifts of the intrinsic weak energy equation. -/
structure StrongDirichletLiftData (a : X → Mat) (C : ℝ) : Prop where
  solve : ∀ f : BallSobolev 0,∃ U : StrongDirichletSpace 0,
    (∀ v : BallH1Zero,TauCeti.PDE.energyFormH1 a (fun _ => (0:X)) (fun _ => (0:ℝ))
      (strongDirichletProjectionL 0 U : BallH1) (v : BallH1) =
      TauCeti.PDE.dirichletForcing (mu:=(volume:Measure X)) (Omega:=ballOpens)
        (TauCeti.Wkp.value (mu:=(volume:Measure X)) (Omega:=ballOpens) (p:=2) 0 f) v) ∧ ‖U‖ ≤ C*‖f‖

theorem StrongDirichletLiftData.of_representative {a : X → Mat} {C : ℝ}
    (F : SmoothCoefficientMatrix 2)
    (hPoint : ∀ x ∈ (ballOpens : Set X),coefficientMatrixField 2 F x = a x)
    (hInvertible : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (hInv : ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖ ≤ C) :
    StrongDirichletLiftData a C := by
  refine ⟨?_⟩
  intro f
  let A := strongDirichletOperator fixedSobolevCalculus 0 F
  let U := A.inverse f
  have hAU : A U = f := hInvertible.self_apply_inverse f
  refine ⟨U,?_,((A.inverse).le_opNorm f).trans (mul_le_mul_of_nonneg_right hInv (norm_nonneg f))⟩
  intro v
  have hEnergy := strongCoefficientOperator_energy fixedSobolevCalculus 0 F U v
  change TauCeti.PDE.dirichletForcing (mu:=(volume:Measure X)) (Omega:=ballOpens)
    (TauCeti.Wkp.value (mu:=(volume:Measure X)) (Omega:=ballOpens) (p:=2) 0 (A U)) v = _ at hEnergy
  rw [hAU] at hEnergy
  exact (energyFormH1_congr_coeff_on hPoint (strongDirichletProjectionL 0 U) (v : BallH1)).symm.trans
    (by simpa only [TauCeti.PDE.energyFormH1_def,Pi.zero_apply] using hEnergy.symm)

/-- Uniform H2 lifts solving the actual weak equation, with no added regularity
    or inverse-bound premise on the admitted geometric data. -/
theorem uniform_actual_strong_dirichlet_lifts {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ 0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      StrongDirichletLiftData
        (principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))) C := by
  obtain ⟨ηS,C,hηS,hC,hS⟩ := uniform_actual_strong_dirichlet_inverse
    (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,hηE,hE⟩ := uniform_enlarged_framed_normal_elliptic
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨min ηS ηE,C,lt_min hηS hηE,hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  obtain ⟨F,hRep,hInv⟩ := hS floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  let H := framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)
  have hEll : Elliptic (Metric.closedBall (0:X) 2) (4*K^2) H :=
    hE floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy d.g₁ (by simp)
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hKP : 1 ≤ 4*K^2 := by nlinarith only [hK,sq_nonneg (K-1)]
  have hPoint (x : X) (hx : x ∈ (ballOpens : Set X)) : coefficientMatrixField 2 F x = principalCoefficient H x := by
    ext i j
    exact (hRep x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds
  have hUE0 := (hEll.principalCoefficient_tau hKP).mono_set unitBall_subset_closedBall_two
  have hUE := hUE0.congr hPoint
  have hInvertible := strongDirichletOperator_isInvertible_of_elliptic
    fixedSobolevCalculus fixedDirichletRegularity 0 F hUE
  exact StrongDirichletLiftData.of_representative
    (a:=principalCoefficient H) F hPoint hInvertible hInv

end ShrinkingSpheres
