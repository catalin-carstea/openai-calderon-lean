import Proof.FixedSpatialMultiplierCutoff
import Proof.SmoothFiniteJetBounds
import Proof.MetricPairFamilyHigherJetBounds
import Proof.NormalFrameMatrixInputJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def boundaryNormalContraction (A : P × X → Mat) (q : P × X) : ℝ :=
  ∑ i : I,∑ j : I,A q i j*q.2 i*q.2 j

lemma contDiff_boundaryNormalContraction (A : P × X → Mat) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (boundaryNormalContraction A) := by
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact (((contDiff_pi.mp (contDiff_pi.mp hA i) j).mul
    ((EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.comp contDiff_snd)).mul
      ((EuclideanSpace.proj (𝕜:=ℝ) j).contDiff.comp contDiff_snd))

lemma norm_iteratedFDeriv_boundaryNormalContraction_le (A : P × X → Mat) (hA : ContDiff ℝ ∞ A)
    (p : P) (z : X) (hz : ‖z‖ ≤ 4) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hAJets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n A (p,z)‖ ≤ B)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (boundaryNormalContraction A) (p,z)‖ ≤
      9*(2^N*(2^N*B*4)*4) := by
  let V := ContinuousLinearMap.snd ℝ P X
  have hV (k : ℕ) (_hk : k ≤ N) : ‖iteratedFDeriv ℝ k (V : P × X → X) (p,z)‖ ≤ 4 := by
    cases k with
    | zero =>
      rw [norm_iteratedFDeriv_zero]
      exact hz
    | succ k => exact (norm_iteratedFDeriv_clm_le_one V (ContinuousLinearMap.norm_snd_le ℝ P X) _ _ (by omega)).trans (by norm_num)
  exact norm_iteratedFDeriv_metricPair_families_le A V V (p,z) hA.contDiffAt V.contDiff.contDiffAt V.contDiff.contDiffAt
    N B 4 4 hB (by norm_num) (by norm_num) hAJets hV hV n hn

variable [FiniteDimensional ℝ P]

theorem exists_closed_boundary_normal_contraction_family (N : ℕ) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ (A : P × X → Mat),ContDiff ℝ ∞ A → ∀ p : P,∀ B : ℝ,0 ≤ B →
      (∀ j : ℕ,j ≤ N+3 → ∀ z ∈ Metric.closedBall (0:X) 4,‖iteratedFDeriv ℝ j A (p,z)‖ ≤ B) →
      ∃ b : P × X → ℝ,∃ hb : ContDiff ℝ ∞ b,∃ S : Set X,∃ hS : IsCompact S,
        ∃ hz : ∀ p z,z ∉ S → b (p,z)=0,
        ∃ V : Set P,IsOpen V ∧ p ∈ V ∧
          (∀ q ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,b =ᶠ[𝓝 (q,z)] boundaryNormalContraction A) ∧
          SmoothFiniteJetBound (commonSupportClosedCoefficientFamily 3 b hb S hS hz) p N (C*B) := by
  obtain ⟨C0,hC0,hProduce⟩ := exists_uniform_commonSupport_closed_multiplier_family (P:=P) N
  let J : ℝ := 9*(2^(N+3)*(2^(N+3)*4)*4)
  let C : ℝ := 1+C0*J
  have hC00 := zero_le_one.trans hC0
  have hJ : 0 ≤ J := by dsimp only [J];positivity
  have hC : 1 ≤ C := by dsimp only [C];nlinarith only [mul_nonneg hC00 hJ]
  refine ⟨C,hC,?_⟩
  intro A hA p B hB hAJets
  have hBJet (j : ℕ) (hj : j ≤ N+3) (z : X) (hz : z ∈ Metric.closedBall (0:X) 4) :
      ‖iteratedFDeriv ℝ j (boundaryNormalContraction A) (p,z)‖ ≤ J*B := by
    have hzNorm : ‖z‖ ≤ 4 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    exact (norm_iteratedFDeriv_boundaryNormalContraction_le A hA p z hzNorm (N+3) B hB
      (fun k hk => hAJets k hk z hz) j hj).trans_eq (by dsimp only [J];ring)
  obtain ⟨b,hb,S,hS,hz,V,hV,hpV,hRep,hJets⟩ := hProduce (boundaryNormalContraction A) univ p
    isOpen_univ (contDiff_boundaryNormalContraction A hA).contDiffOn (by simp) (J*B) (mul_nonneg hJ hB) hBJet
  refine ⟨b,hb,S,hS,hz,V,hV,hpV,hRep,?_⟩
  refine ⟨mul_nonneg (zero_le_one.trans hC) hB,
    (contDiff_commonSupportClosedCoefficientFamily 3 b hb S hS hz).contDiffAt,?_⟩
  intro n hn
  exact (hJets n hn).trans (by dsimp only [C];nlinarith only [hB])
end ShrinkingSpheres
