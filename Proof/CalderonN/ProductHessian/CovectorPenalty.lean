module

public import Proof.CalderonN.ProductHessian.ProductMoments

/-! Adapted from `Calderon/StrictWeightCovectorPenalty.lean` at d6704c49395a38eb07e0249afeb8ea83d67971cc
in the earlier anisotropic Calderón formalization. -/

@[expose] public section

/-! Product-Hessian cone proof: compact choice of the positive covector penalty. -/
set_option autoImplicit false
noncomputable section
open Set Metric Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
namespace CalderonN.ProductHessianSeparation

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

local notation "FactorVector" => (Fin dim → ℝ)
local notation "ProductIndex" => (Fin dim ⊕ Fin dim)
local notation "ProductVector" => (ProductIndex → ℝ)
local notation "FactorMatrix" => Matrix (Fin dim) (Fin dim) ℝ
local notation "ProductMatrix" => Matrix ProductIndex ProductIndex ℝ
local notation "ProductSelfAdjoint" => selfAdjoint ProductMatrix

theorem exists_pos_covector_penalty_of_tangentSphere_positive
    (G1 G2 : FactorMatrix) (hG1 : G1.PosDef) (hG2 : G2.PosDef)
    (ell1 ell2 a1 a2 : FactorVector)
    (ha1 : dotProduct ell1 a1 = 1) (ha2 : dotProduct ell2 a2 = 1)
    (H : ProductMatrix) (hH : H.IsHermitian)
    (hsource : ∀ v1 ∈ metricTangentSphere G1 ell1 a1,
      ∀ v2 ∈ metricTangentSphere G2 ell2 a2,
      0 < dotProduct (Sum.elim a1 (-a2)) (H *ᵥ Sum.elim a1 (-a2)) +
        dotProduct (Sum.elim v1 v2) (H *ᵥ Sum.elim v1 v2)) :
    ∃ K : ℝ, 0 < K ∧
      ∀ D ∈ productMetricMomentSection G1 G2 ell1 ell2 a1 a2,
        0 < Matrix.trace ((H + K • Matrix.vecMulVec (Sum.elim ell1 ell2)
          (Sum.elim ell1 ell2)) * (D : ProductMatrix)) := by
  classical
  let A : Set ProductSelfAdjoint := productMetricMomentSection G1 G2 ell1 ell2 a1 a2
  let ell : ProductVector := Sum.elim ell1 ell2
  let n : ProductVector := Sum.elim a1 (-a2)
  let h : ProductSelfAdjoint → ℝ := fun D => Matrix.trace (H*(D : ProductMatrix))
  let q : ProductSelfAdjoint → ℝ := fun D => dotProduct ell ((D : ProductMatrix)*ᵥ ell)
  have hEntry (i j : ProductIndex) : Continuous (fun D : ProductSelfAdjoint => (D : ProductMatrix) i j) :=
    Continuous.comp (f := fun D : ProductSelfAdjoint => (D : ProductMatrix))
      (g := fun B : ProductMatrix => B i j) (continuous_apply_apply i j) continuous_subtype_val
  have hhContinuous : Continuous h := by
    have hRow (i : ProductIndex) : Continuous (fun D : ProductSelfAdjoint => ∑ j : ProductIndex, H i j*(D : ProductMatrix) j i) :=
      continuous_finsetSum Finset.univ (fun j _ => (hEntry j i).const_mul (H i j))
    change Continuous (fun D : ProductSelfAdjoint => ∑ i : ProductIndex, ∑ j : ProductIndex, H i j*(D : ProductMatrix) j i)
    exact continuous_finsetSum Finset.univ (fun i _ => hRow i)
  have hqContinuous : Continuous q := by
    have hRow (i : ProductIndex) : Continuous (fun D : ProductSelfAdjoint => ∑ j : ProductIndex, (D : ProductMatrix) i j*ell j) :=
      continuous_finsetSum Finset.univ (fun j _ => (hEntry i j).mul_const (ell j))
    change Continuous (fun D : ProductSelfAdjoint => ∑ i : ProductIndex, ell i*(∑ j : ProductIndex, (D : ProductMatrix) i j*ell j))
    exact continuous_finsetSum Finset.univ (fun i _ => (hRow i).const_mul (ell i))
  have hqNonneg (D : ProductSelfAdjoint) (hD : D ∈ A) : 0 ≤ q D := by
    have hp : (D : ProductMatrix).PosSemidef := hD.1
    simpa only [q,star_trivial] using hp.dotProduct_mulVec_nonneg ell
  have hPenalty (D : ProductSelfAdjoint) (K : ℝ) :
      Matrix.trace ((H+K • Matrix.vecMulVec ell ell)*(D : ProductMatrix)) = h D+K*q D := by
    have hRank : Matrix.trace (Matrix.vecMulVec ell ell*(D : ProductMatrix)) = q D := by
      rw [Matrix.trace_mul_comm,Matrix.mul_vecMulVec,Matrix.trace_vecMulVec]
      exact dotProduct_comm _ _
    rw [Matrix.add_mul,Matrix.smul_mul,Matrix.trace_add,Matrix.trace_smul,hRank]
    rfl
  have hZeroPositive (D : ProductSelfAdjoint) (hD : D ∈ A) (hq : q D = 0) : 0 < h D := by
    have hp : (D : ProductMatrix).PosSemidef := hD.1
    have hne : (D : ProductMatrix) ≠ 0 := by
      have htr : Matrix.trace (D : ProductMatrix) = 1 := hD.2.2.2
      intro hz
      rw [hz,Matrix.trace_zero] at htr
      norm_num at htr
    have hker : (D : ProductMatrix)*ᵥ ell = 0 := by
      apply hp.dotProduct_mulVec_zero_iff.mp
      simpa only [q,star_trivial] using hq
    let P : ProductMatrix := Matrix.fromBlocks
      (1-Matrix.vecMulVec a1 ell1) 0 0 (1-Matrix.vecMulVec a2 ell2)
    let T : ProductMatrix := P*(D : ProductMatrix)*P.transpose
    have hDec := exists_pos_normal_tangent_decomposition G1 G2 hG1 hG2
      ell1 ell2 a1 a2 ha1 ha2 (D : ProductMatrix) hp hne hD.2.1 hD.2.2.1 hker
    dsimp only at hDec
    obtain ⟨d,hd,hd1,hd2,hN1,hN2,hC1,hC2,hQP,hPQ,hDsum,hTPSD,
      hTker1,hTker2,hTtrace1,hTtrace2⟩ := hDec
    change (D : ProductMatrix) = d • Matrix.vecMulVec n n+T at hDsum
    change T.PosSemidef at hTPSD
    change T*ᵥ Sum.elim ell1 (0 : FactorVector) = 0 at hTker1
    change T*ᵥ Sum.elim (0 : FactorVector) ell2 = 0 at hTker2
    change Matrix.trace (G1*T.toBlocks₁₁) = d*dotProduct a1 (G1*ᵥ a1) at hTtrace1
    change Matrix.trace (G2*T.toBlocks₂₂) = d*dotProduct a2 (G2*ᵥ a2) at hTtrace2
    let Sm : ProductMatrix := d⁻¹ • T
    have hSPSD : Sm.PosSemidef := hTPSD.smul (inv_nonneg.mpr hd.le)
    let S : ProductSelfAdjoint := ⟨Sm,hSPSD.isHermitian⟩
    have hS : S ∈ tangentMetricMomentSection G1 G2 ell1 ell2 a1 a2 := by
      refine ⟨hSPSD,?_,?_,?_,?_⟩
      · change (d⁻¹ • T)*ᵥ Sum.elim ell1 (0 : FactorVector) = 0
        rw [Matrix.smul_mulVec,hTker1,smul_zero]
      · change (d⁻¹ • T)*ᵥ Sum.elim (0 : FactorVector) ell2 = 0
        rw [Matrix.smul_mulVec,hTker2,smul_zero]
      · change Matrix.trace (G1*(d⁻¹ • T.toBlocks₁₁)) = dotProduct a1 (G1*ᵥ a1)
        rw [Matrix.mul_smul,Matrix.trace_smul,hTtrace1]
        change d⁻¹*(d*dotProduct a1 (G1*ᵥ a1)) = dotProduct a1 (G1*ᵥ a1)
        rw [← mul_assoc,inv_mul_cancel₀ hd.ne',one_mul]
      · change Matrix.trace (G2*(d⁻¹ • T.toBlocks₂₂)) = dotProduct a2 (G2*ᵥ a2)
        rw [Matrix.mul_smul,Matrix.trace_smul,hTtrace2]
        change d⁻¹*(d*dotProduct a2 (G2*ᵥ a2)) = dotProduct a2 (G2*ᵥ a2)
        rw [← mul_assoc,inv_mul_cancel₀ hd.ne',one_mul]
    have hRank := exists_rankOne_minimizer_tangentMetricMomentSection
      G1 G2 hG1 hG2 ell1 ell2 a1 a2 ha1 ha2 (⟨H,hH⟩ : ProductSelfAdjoint)
    dsimp only at hRank
    obtain ⟨v1,hv1,v2,hv2,S0,hS0,hS0mem,hMin⟩ := hRank
    let v : ProductVector := Sum.elim v1 v2
    have hBound : dotProduct v (H*ᵥ v) ≤ Matrix.trace (H*Sm) := by
      have hb := hMin S hS
      change Matrix.trace (H*(S0 : ProductMatrix)) ≤ Matrix.trace (H*Sm) at hb
      rw [hS0,Matrix.mul_vecMulVec,Matrix.trace_vecMulVec,dotProduct_comm] at hb
      exact hb
    have hOriginal : 0 < dotProduct n (H*ᵥ n)+dotProduct v (H*ᵥ v) :=
      hsource v1 hv1 v2 hv2
    have hPositive : 0 < dotProduct n (H*ᵥ n)+Matrix.trace (H*Sm) :=
      lt_of_lt_of_le hOriginal (add_le_add_right hBound _)
    have hTS : T = d • Sm := by
      simp only [Sm,smul_smul,mul_inv_cancel₀ hd.ne',one_smul]
    have hTraceD : h D = d*(dotProduct n (H*ᵥ n)+Matrix.trace (H*Sm)) := by
      change Matrix.trace (H*(D : ProductMatrix)) = _
      rw [hDsum,hTS,Matrix.mul_add,Matrix.mul_smul,Matrix.mul_smul,
        Matrix.trace_add,Matrix.trace_smul,Matrix.trace_smul,
        Matrix.mul_vecMulVec,Matrix.trace_vecMulVec,dotProduct_comm]
      change d*dotProduct n (H*ᵥ n)+d*Matrix.trace (H*Sm) = _
      ring
    rw [hTraceD]
    exact mul_pos hd hPositive
  have hCompact : IsCompact A :=
    isCompact_productMetricMomentSection G1 G2 hG1 hG2 ell1 ell2 a1 a2 ha1 ha2
  rcases A.eq_empty_or_nonempty with hEmpty | hNonempty
  · refine ⟨1,zero_lt_one,?_⟩
    intro D hD
    change D ∈ A at hD
    rw [hEmpty] at hD
    exact False.elim hD
  let B : Set ProductSelfAdjoint := A ∩ {D : ProductSelfAdjoint | h D ≤ (0 : ℝ)}
  have hBadClosed : IsClosed {D : ProductSelfAdjoint | h D ≤ (0 : ℝ)} :=
    isClosed_le (f := h) (g := fun _ : ProductSelfAdjoint => (0 : ℝ)) hhContinuous continuous_const
  have hBadCompact : IsCompact B := hCompact.inter_right hBadClosed
  rcases B.eq_empty_or_nonempty with hBEmpty | hBNonempty
  · refine ⟨1,zero_lt_one,?_⟩
    intro D hD
    change D ∈ A at hD
    have hPositive : 0 < h D := by
      apply lt_of_not_ge
      intro hn
      have hDB : D ∈ B := ⟨hD,hn⟩
      rw [hBEmpty] at hDB
      exact hDB
    change 0 < Matrix.trace ((H+1 • Matrix.vecMulVec ell ell)*(D : ProductMatrix))
    rw [hPenalty D 1]
    exact add_pos_of_pos_of_nonneg hPositive (mul_nonneg zero_le_one (hqNonneg D hD))
  have hqPositive (D : ProductSelfAdjoint) (hD : D ∈ B) : 0 < q D := by
    by_contra hn
    have hz : q D = 0 := le_antisymm (le_of_not_gt hn) (hqNonneg D hD.1)
    exact (not_lt_of_ge hD.2) (hZeroPositive D hD.1 hz)
  obtain ⟨delta,hdelta,hdeltaBound⟩ :=
    hBadCompact.exists_forall_le' hqContinuous.continuousOn hqPositive
  obtain ⟨Dmin,hDmin,hMinH⟩ :=
    hCompact.exists_isMinOn hNonempty hhContinuous.continuousOn
  let M : ℝ := max 0 (-h Dmin)
  have hM : 0 ≤ M := le_max_left _ _
  have hLower (D : ProductSelfAdjoint) (hD : D ∈ A) : -M ≤ h D := by
    have hm : -h Dmin ≤ M := le_max_right _ _
    have hmin : h Dmin ≤ h D := hMinH hD
    linarith only [hm,hmin]
  let K : ℝ := (M+1)/delta
  have hK : 0 < K := div_pos (by linarith only [hM]) hdelta
  have hKdelta : K*delta = M+1 := div_mul_cancel₀ _ hdelta.ne'
  refine ⟨K,hK,?_⟩
  intro D hD
  change D ∈ A at hD
  change 0 < Matrix.trace ((H+K • Matrix.vecMulVec ell ell)*(D : ProductMatrix))
  rw [hPenalty D K]
  by_cases hDB : D ∈ B
  · have hqLower : delta ≤ q D := hdeltaBound D hDB
    have hKq : K*delta ≤ K*q D := mul_le_mul_of_nonneg_left hqLower hK.le
    have hhLower : -M ≤ h D := hLower D hD
    linarith only [hKdelta,hKq,hhLower]
  · have hPositive : 0 < h D := by
      apply lt_of_not_ge
      intro hn
      exact hDB ⟨hD,hn⟩
    exact add_pos_of_pos_of_nonneg hPositive (mul_nonneg hK.le (hqNonneg D hD))


end CalderonN.ProductHessianSeparation
