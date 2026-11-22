module

public import Proof.CalderonN.BallPoissonOperator
public import Proof.CalderonN.BallForcingJetBounds

import Mathlib.Tactic

/-! Adapted from `UniformBallPoissonJets` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 3000000

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
open CalderonN.BallDirichlet

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

local instance (priority := 1500) ballOperatorNorm (m : ℕ) :
    NormedAddCommGroup ((BallSobolev dim) m →L[ℝ] (BallSobolev dim) m) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance (priority := 1500) ballOperatorSpace (m : ℕ) :
    NormedSpace ℝ ((BallSobolev dim) m →L[ℝ] (BallSobolev dim) m) :=
  ContinuousLinearMap.toNormedSpace

/-- The smooth harmonic replacement and its first parameter derivative
have bounds in closed-ball spatial jets, from one fixed Sobolev order. -/
theorem exists_uniform_ballPoisson_replacement_jet_bounds
    (s : ℕ) (a : P × (X dim) → (Mat dim)) (ha : ContDiff ℝ ∞ a)
    (K : Set (X dim)) (hK : IsCompact K) (hSupp : ∀ p z, z ∉ K → a (p,z) = 0)
    {V J : Set P} (hV : IsOpen V) (hJ : IsCompact J) (hJV : J ⊆ V)
    (lo hi : P → ℝ)
    (hEll : ∀ p ∈ V, TauCeti.PDE.UniformlyEllipticOn (fixedBallOpens dim : Set (X dim))
      (fun z => a (p,z)) (lo p) (hi p)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (d : P × (X dim) → ℝ) (hd : ContDiff ℝ ∞ d) (L : Set (X dim)) (hL : IsCompact L),
      (∀ p z, z ∉ L → d (p,z) = 0) →
      ∃ b : P → (X dim) → ℝ, (∀ p, ContDiff ℝ ∞ (b p)) ∧
      (∀ p ∈ V, EqOn (b p) (fun z => d (p,z)) (standardSphere dim) ∧
        EqOn (negativeBallDivergence (fun z => a (p,z)) (b p)) 0 (ball (0 : (X dim)) 1)) ∧
      (∀ k : ℕ, k ≤ s → ∀ z ∈ closedBall (0 : (X dim)) 1,
        ContDiffOn ℝ ∞ (fun q => iteratedFDeriv ℝ k (b q) z) V) ∧
      ∀ p ∈ J, ∀ v M N, 0 ≤ M → 0 ≤ N →
        (∀ k : ℕ, k ≤ s+dim+2 → ∀ z, ‖iteratedFDeriv ℝ k (fun x => d (p,x)) z‖ ≤ M) →
        (∀ k : ℕ, k ≤ s+dim+2 → ∀ z,
          ‖fderiv ℝ (fun q : P => iteratedFDeriv ℝ k (fun x => d (q,x)) z) p v‖ ≤ N) →
        ∀ k : ℕ, k ≤ s → ∀ z ∈ closedBall (0 : (X dim)) 1,
          ‖iteratedFDeriv ℝ k (b p) z‖ ≤ C*M ∧
          ‖fderiv ℝ (fun q => iteratedFDeriv ℝ k (b q) z) p v‖ ≤ C*(N+M*‖v‖) := by
  let N₀ := s+dim-1
  let m := N₀+2
  have hm : s+dim+1 = m := by have hd := NeZero.ne dim; dsimp [m,N₀]; omega
  have hm' : m+1 = s+dim+2 := by omega
  let T (p : P) : (BallSobolev dim) m →L[ℝ] (BallSobolev dim) m :=
    ballPoissonOperatorL N₀ (commonSupportMatrixFamily m a ha K hK hSupp p)
  have hT : ContDiffOn ℝ ∞ T V := contDiffOn_ballPoissonOperator_family N₀ a ha K hK hSupp V lo hi hEll
  have hTS : ContinuousOn (fun p => ‖T p‖ + ‖fderiv ℝ T p‖) J :=
    (hT.continuousOn.norm.add ((hT.fderiv_of_isOpen (m := ∞) hV (by simp)).continuousOn.norm)).mono hJV
  obtain ⟨D,hD⟩ := hJ.exists_bound_of_continuousOn hTS
  let B := max 0 D
  have hB : 0 ≤ B := le_max_left _ _
  have hTB (p : P) (hp : p ∈ J) : ‖T p‖ ≤ B ∧ ‖fderiv ℝ T p‖ ≤ B := by
    have h : ‖T p‖ + ‖fderiv ℝ T p‖ ≤ B :=
      (le_abs_self _).trans ((hD p hp).trans (le_max_right _ _))
    exact ⟨(le_add_of_nonneg_right (ContinuousLinearMap.opNorm_nonneg (fderiv ℝ T p))).trans h,
      (le_add_of_nonneg_left (norm_nonneg _)).trans h⟩
  obtain ⟨A,hA,hAjet⟩ := exists_ballForcingFamily_jet_bounds (dim := dim) (P := P) m
  let C := (ballJetEmbeddingConstant dim) * (B*A)
  refine ⟨C,mul_nonneg (ballJetEmbeddingConstant_nonneg dim) (mul_nonneg hB hA),?_⟩
  intro d hd L hL hSuppL
  let D₀ := ballForcingFamily m d hd L hL hSuppL
  let u (p : P) := T p (D₀ p)
  have hD₀ : ContDiff ℝ ∞ D₀ := contDiff_ballForcingFamily m d hd L hL hSuppL
  have hu : ContDiffOn ℝ ∞ u V := hT.clm_apply hD₀.contDiffOn
  have hdSlice (p : P) : ContDiff ℝ ∞ (fun z => d (p,z)) :=
    hd.comp (contDiff_const.prodMk contDiff_id)
  have hDval (p : P) : D₀ p = smoothBallSobolev m ⟨fun z => d (p,z),hdSlice p⟩ := by
    apply TauCeti.Wkp.ext m
    apply Lp.ext
    exact (ballForcingFamily_value m d hd L hL hSuppL p).trans
      (value_smoothBallSobolev_ae m ⟨fun z => d (p,z),hdSlice p⟩).symm
  have hb (p : P) (hp : p ∈ V) :
      ∃ (b : (X dim) → ℝ) (hb : ContDiff ℝ ∞ b), EqOn b (fun z => d (p,z)) (standardSphere dim) ∧
        EqOn (negativeBallDivergence (fun z => a (p,z)) b) 0 (ball (0 : (X dim)) 1) ∧
        u p = smoothBallSobolev m ⟨b,hb⟩ := by
    obtain ⟨b,hb,hbT,hbL,hRep⟩ := exists_smooth_representative_ballPoissonOperator
      a ha K hK hSupp V lo hi hEll d hd p hp
    refine ⟨b,hb,hbT,hbL,?_⟩
    dsimp only [u,T]
    rw [hDval]
    exact hRep N₀
  classical
  choose b₀ hb₀ hbT hbL hbRep using hb
  let b (p : P) := if hp : p ∈ V then b₀ p hp else 0
  have hbd (p : P) : ContDiff ℝ ∞ (b p) := by
    by_cases hp : p ∈ V
    · simpa only [b,dite_eq_left hp] using hb₀ p hp
    · rw [show b p = (fun _ : (X dim) => (0 : ℝ)) from dite_eq_right hp]
      exact contDiff_const
  let inc : (ClosedBallSobolev dim) m →ₗᵢ[ℝ] (BallSobolev dim) m := ((closedBallSobolev dim) m).toSubmodule.subtypeₗᵢ
  let w (p : P) : (ClosedBallSobolev dim) m :=
    if hp : p ∈ V then (denseSmoothBallSobolev dim) m ⟨b₀ p hp,hb₀ p hp⟩ else 0
  have hEq : EqOn (inc ∘ w) u V := by
    intro p hp
    simp only [Function.comp_apply,w,dite_eq_left hp]
    exact (hbRep p hp).symm
  have hw : ContDiffOn ℝ ∞ w V :=
    contDiffOn_top_of_closedRangeLinearIsometry hV inc w (hu.congr hEq)
  let E (k : ℕ) (z : (UnitClosedBall dim)) : (ClosedBallSobolev dim) m →L[ℝ] (BallJet dim) k :=
    (ContinuousMap.evalCLM ℝ z).comp ((closedBallJetL dim) k m)
  have hE (k : ℕ) (hk : k ≤ s) (z : (UnitClosedBall dim)) :
      EqOn (E k z ∘ w) (fun p => iteratedFDeriv ℝ k (b p) z) V := by
    intro p hp
    simp only [Function.comp_apply,E,ContinuousLinearMap.comp_apply,w,b,dite_eq_left hp,
      closedBallJetL_on_smooth k m (by omega : k+dim+1 ≤ m)]
    rfl
  refine ⟨b,hbd,fun p hp => ?_,fun k hk z hz => ?_,?_⟩
  · simpa only [b,dite_eq_left hp] using And.intro (hbT p hp) (hbL p hp)
  · exact ((E k ⟨z,hz⟩).contDiff.comp_contDiffOn hw).congr (fun p hp => (hE k hk ⟨z,hz⟩ hp).symm)
  intro p hp v M N hM hN hD₁ hD₂ k hk z hz
  let z₀ : (UnitClosedBall dim) := ⟨z,hz⟩
  have hpV := hJV hp
  obtain ⟨hDV,hDD⟩ := hAjet d hd L hL hSuppL p v M N hM hN (fun i hi => hD₁ i (by omega)) (fun i hi => hD₂ i (by omega))
  have hwV : ‖w p‖ ≤ (B*A)*M := by
    rw [← inc.norm_map]
    change ‖(inc ∘ w) p‖ ≤ _
    rw [hEq hpV]
    calc
      ‖T p (D₀ p)‖ ≤ ‖T p‖ * ‖D₀ p‖ := (T p).le_opNorm _
      _ ≤ B*(A*M) := mul_le_mul (hTB p hp).1 hDV (norm_nonneg _) hB
      _ = _ := by ring
  have hDiffW := (hw.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp)
  have hDiffT := (hT.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp)
  have hEq' : (inc ∘ w) =ᶠ[𝓝 p] u := by
    filter_upwards [hV.mem_nhds hpV] with q hq
    exact hEq hq
  have hWDer : inc (fderiv ℝ w p v) = fderiv ℝ u p v := by
    have h := (inc.toContinuousLinearMap.hasFDerivAt.comp p hDiffW.hasFDerivAt).fderiv
    change fderiv ℝ (inc ∘ w) p = inc.toContinuousLinearMap.comp (fderiv ℝ w p) at h
    rw [hEq'.fderiv_eq] at h
    exact (congrArg (fun L : P →L[ℝ] (BallSobolev dim) m => L v) h).symm
  have hwD : ‖fderiv ℝ w p v‖ ≤ (B*A)*(N+M*‖v‖) := by
    rw [← inc.norm_map,hWDer]
    change ‖fderiv ℝ (fun p => T p (D₀ p)) p v‖ ≤ _
    rw [fderiv_clm_apply hDiffT (hD₀.differentiable (by simp) p)]
    simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply]
    have hT' : ‖fderiv ℝ T p v‖ ≤ B*‖v‖ :=
      ((fderiv ℝ T p).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hTB p hp).2 (norm_nonneg _))
    calc
      ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
      _ ≤ B*(A*N) + (B*‖v‖)*(A*M) := add_le_add
        (((T p).le_opNorm _).trans (mul_le_mul (hTB p hp).1 hDD (norm_nonneg _) hB))
        (((fderiv ℝ T p v).le_opNorm _).trans
          (mul_le_mul hT' hDV (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))))
      _ = _ := by ring
  have hEval (f : (ClosedBallSobolev dim) m) :
      ‖E k z₀ f‖ ≤ (ballJetEmbeddingConstant dim) * ‖f‖ :=
    norm_closedBallJetL_apply_le k m (by omega) f z₀
  have hE' : (E k z₀ ∘ w) =ᶠ[𝓝 p] (fun q => iteratedFDeriv ℝ k (b q) z) := by
    filter_upwards [hV.mem_nhds hpV] with q hq
    exact hE k hk z₀ hq
  constructor
  · have he : E k z₀ (w p) = iteratedFDeriv ℝ k (b p) z := hE k hk z₀ hpV
    rw [← he]
    exact (hEval _).trans ((mul_le_mul_of_nonneg_left hwV (ballJetEmbeddingConstant_nonneg dim)).trans_eq (by dsimp [C]; ring))
  · rw [← hE'.fderiv_eq,((E k z₀).hasFDerivAt.comp p hDiffW.hasFDerivAt).fderiv]
    exact (hEval _).trans ((mul_le_mul_of_nonneg_left hwD (ballJetEmbeddingConstant_nonneg dim)).trans_eq (by dsimp [C]; ring))

end CalderonN
