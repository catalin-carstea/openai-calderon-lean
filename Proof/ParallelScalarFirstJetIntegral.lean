import Proof.ParallelScalarFirstJetMassIdentity
import Proof.ParallelScalarFirstConditional
import Proof.UniformEffectiveFirstLowEndpointData
import Proof.PhysicalScalarSelfIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The sole remaining jet sector follows from genuine forward strong
half two-jets. All original quantifiers and the SAME WF remain fixed. -/
theorem uniform_scalar_first_jet_bound_of_forward_packets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (hPackets : ∃ η Q : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ Q ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,∀ CB CS : ℝ,
      ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
        Nonempty (EffectiveFirstForwardStrongHalfTwoJets WF Q))
    (CF CT CB CS : ℝ) : ScalarFirstJetBound Y Ω K ρ c₀ M Cj CF CT CB CS := by
  obtain ⟨ηP,QP,hηP,hηP1,hQP,hPacket⟩ := hPackets
  obtain ⟨ηB,QB,hηB,hηB1,hQB,hLow⟩ := uniform_effective_first_low_endpoint_data
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηD,QD,hηD,hηD1,hQD,hDer⟩ := uniform_effective_first_strong_half_derivative_bound
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηH,hηH,hηH1,hBalanced⟩ := uniform_full_first_derivative_balanced_endpoints
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let Q := QP+QB+QD
  have hQ : 0 ≤ Q := by dsimp only [Q];positivity
  have hPQ : QP ≤ Q := by dsimp only [Q];linarith only [hQB,hQD]
  have hBQ : QB ≤ Q := by dsimp only [Q];linarith only [hQP,hQD]
  have hDQ : QD ≤ Q := by dsimp only [Q];linarith only [hQP,hQB]
  obtain ⟨C0,hC0,hMass⟩ := uniform_scalar_first_mass_contraction_bound hY hΩ hSub (by omega)
    K ρ c₀ M Cj hK Q hQ
  let η := min ηP (min ηB (min ηD ηH))
  have hη : 0 < η := lt_min hηP (lt_min hηB (lt_min hηD hηH))
  have hη1 : η ≤ 1 := (min_le_left _ _).trans hηP1
  refine ⟨η,108*C0,hη,hη1,mul_nonneg (by norm_num) hC0,?_⟩
  intro floor hf ε hε hSmall d hd P WF φ E D hφ
  have hε1 : ε ≤ 1 := hSmall.trans hη1
  have hSmallP : ε ≤ ηP := hSmall.trans (min_le_left _ _)
  have hSmallB : ε ≤ ηB := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallD : ε ≤ ηD := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hSmallH : ε ≤ ηH := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨p⟩ := hPacket floor hf ε hε hSmallP d hd CF CT P CB CS WF
  have hData (t : Fin 2) (k : I) :
      ContDiffOn ℝ ∞ (scalarFirstMassCoefficient p t k) Y ∧
      (∀ y ∈ Y,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (scalarFirstMassHigher p t k y)=
        (scalarFirstMassCoefficient p t k y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) ∧
      (∀ y ∈ Y,‖scalarFirstMassCoefficient p t k y‖ ≤ Q*ε) ∧
      (∀ y ∈ Y,∀ i : I,∃ L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
        halfOperatorCovariantDerivativeL d (scalarFirstMassCoefficient p t k) (scalarFirstMassHigher p t k) y (axis i)=
          L.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
        ‖L‖ ≤ Q*ε*beta d.γ d.radius y) := by
    by_cases ht : t=0
    · simp only [scalarFirstMassCoefficient,scalarFirstMassHigher,ht,ite_true]
      refine ⟨p.low_smooth k k,p.higher_graph k k,?_,?_⟩
      · intro y hy
        exact (p.low_norm k k y hy).trans (mul_le_mul_of_nonneg_right hPQ hε)
      · intro y hy i
        obtain ⟨L,hL,hLN⟩ := p.second k k i y hy
        exact ⟨L,hL,hLN.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hPQ hε) (zero_le_one.trans (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)))⟩
    · have hCeq : scalarFirstMassCoefficient p t k=P.firstCovariantCoordinateHalfL k := by
        funext x
        exact if_neg ht
      have hHeq : scalarFirstMassHigher p t k=P.firstCovariantCoordinateHigherL k := by
        funext x
        exact if_neg ht
      rw [hCeq,hHeq]
      have hL := hLow floor hf ε hε hSmallB d hd CF CT P k
      refine ⟨hL.1,?_,?_,?_⟩
      · intro y hy
        exact P.firstCovariantCoordinateHigherL_balanced k y (P.firstDerivativeCoordinate_balanced y
          (hBalanced floor hf ε hε hSmallH d hd CF CT P y hy) k)
      · intro y hy
        have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
        exact (hL.2 y hy).trans ((div_le_self (mul_nonneg hQB hε) hβ).trans
          (mul_le_mul_of_nonneg_right hBQ hε))
      · intro y hy i
        obtain ⟨L,hLD,hLA,hLN,hLAN⟩ := hDer floor hf ε hε hSmallD d hd CF CT P CB CS WF y hy k i
        refine ⟨L,hLD,hLN.trans ?_⟩
        have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
        exact (mul_le_mul_of_nonneg_right hDQ hε).trans
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hβ (mul_nonneg hQ hε))
  let F := fun (a b k : I) (t : Fin 2) => scalarFirstMassTermComplexDensity p t a b k E
  have hSingle (a b k : I) (t : Fin 2) : IntegrableOn (F a b k t) Y ∧
      |∫ y in Y,F a b k t y| ≤ C0*ε^2*energySq Y d.γ d.frame d.radius φ :=
    hMass floor hf ε hε hε1 d hd (scalarFirstMassCoefficient p t k) (scalarFirstMassHigher p t k)
      (hData t k).1 (hData t k).2.1 (hData t k).2.2.1 (hData t k).2.2.2 t a b k φ E D hφ
  have hInt (a b k : I) (t : Fin 2) : IntegrableOn (F a b k t) Y := (hSingle a b k t).1
  have hSumI : IntegrableOn (fun y => ∑ a : I,∑ b : I,∑ k : I,∑ t : Fin 2,F a b k t y) Y :=
    integrable_finsetSum Finset.univ (fun a _ => integrable_finsetSum Finset.univ (fun b _ =>
      integrable_finsetSum Finset.univ (fun k _ => integrable_finsetSum Finset.univ (fun t _ => hInt a b k t))))
  have hEq : scalarFirstJetComplexDensity P WF E=ᵐ[volume.restrict Y]
      (fun y => 2*(∑ a : I,∑ b : I,∑ k : I,∑ t : Fin 2,F a b k t y)) := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    exact scalarFirstJetComplexDensity_eq_mass_terms P WF p E hy
  have hIntegral : (∫ y in Y,scalarFirstJetComplexDensity P WF E y)=
      2*(∑ a : I,∑ b : I,∑ k : I,∑ t : Fin 2,∫ y in Y,F a b k t y) := by
    rw [integral_congr_ae hEq,integral_const_mul]
    congr 1
    rw [integral_finsetSum Finset.univ (fun a _ => integrable_finsetSum Finset.univ (fun b _ =>
      integrable_finsetSum Finset.univ (fun k _ => integrable_finsetSum Finset.univ (fun t _ => hInt a b k t))))]
    apply Finset.sum_congr rfl
    intro a _
    rw [integral_finsetSum Finset.univ (fun b _ => integrable_finsetSum Finset.univ (fun k _ =>
      integrable_finsetSum Finset.univ (fun t _ => hInt a b k t)))]
    apply Finset.sum_congr rfl
    intro b _
    rw [integral_finsetSum Finset.univ (fun k _ => integrable_finsetSum Finset.univ (fun t _ => hInt a b k t))]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_finsetSum Finset.univ (fun t _ => hInt a b k t)]
  refine ⟨(hSumI.const_mul 2).congr hEq.symm,?_⟩
  rw [hIntegral,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  have hTwo (a b k : I) : |∑ t : Fin 2,∫ y in Y,F a b k t y| ≤
      2*(C0*ε^2*energySq Y d.γ d.frame d.radius φ) := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun t _ => (hSingle a b k t).2)).trans_eq
      (by simp only [Fin.sum_univ_two];ring))
  have hh := abs_fin_three_sum_le (fun a => ∑ b : I,∑ k : I,∑ t : Fin 2,∫ y in Y,F a b k t y)
    (3*(3*(2*(C0*ε^2*energySq Y d.γ d.frame d.radius φ)))) (fun a =>
      abs_fin_three_sum_le _ (3*(2*(C0*ε^2*energySq Y d.γ d.frame d.radius φ))) (fun b =>
        abs_fin_three_sum_le _ (2*(C0*ε^2*energySq Y d.γ d.frame d.radius φ)) (hTwo a b)))
  exact (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)

end ShrinkingSpheres.ParallelEnergy
