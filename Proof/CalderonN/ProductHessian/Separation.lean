module

public import Proof.CalderonN.ProductHessian.CovectorPenalty

/-! Adapted from `Calderon/StrictWeightProductHessianSeparation.lean` at d6704c49395a38eb07e0249afeb8ea83d67971cc
in the earlier anisotropic Calderón formalization. -/

@[expose] public section

/-! Pointwise separation of the product Hessian. -/
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
local notation "FactorSelfAdjoint" => selfAdjoint FactorMatrix
local notation "ProductSelfAdjoint" => selfAdjoint ProductMatrix

theorem exists_strict_block_forms_of_tangentSphere_positive
    (G1 G2 : FactorMatrix) (hG1 : G1.PosDef) (hG2 : G2.PosDef)
    (ell1 ell2 a1 a2 : FactorVector)
    (ha1 : dotProduct ell1 a1 = 1) (ha2 : dotProduct ell2 a2 = 1)
    (H : ProductMatrix) (hH : H.IsHermitian)
    (hsource : ∀ v1 ∈ metricTangentSphere G1 ell1 a1,
      ∀ v2 ∈ metricTangentSphere G2 ell2 a2,
      0 < dotProduct (Sum.elim a1 (-a2)) (H *ᵥ Sum.elim a1 (-a2)) +
        dotProduct (Sum.elim v1 v2) (H *ᵥ Sum.elim v1 v2)) :
    ∃ (P1 P2 : FactorSelfAdjoint) (K : ℝ), 0 < K ∧
      P1 ∈ strictSphereCone G1 ell1 a1 ∧ P2 ∈ strictSphereCone G2 ell2 a2 ∧
      (H + K • Matrix.vecMulVec (Sum.elim ell1 ell2) (Sum.elim ell1 ell2) -
        Matrix.fromBlocks (P1 : FactorMatrix) 0 0 (P2 : FactorMatrix)).PosDef := by
  classical
  letI : ContinuousSMul ℝ ProductSelfAdjoint :=
    Topology.IsInducing.continuousSMul
      (M := ℝ) (X := ProductMatrix) (Y := ProductSelfAdjoint)
      (g := fun D : ProductSelfAdjoint => (D : ProductMatrix)) (f := fun t : ℝ => t)
      Topology.IsInducing.subtypeVal continuous_id (fun {_ _} => rfl)
  have hAffineLimit (a b : ℝ) (h : ∀ t : ℝ, 0 < t → 0 ≤ a+t*b) : 0 ≤ a := by
    by_contra hn
    have ha : a < 0 := lt_of_not_ge hn
    let t : ℝ := (-a)/(2*(|b|+1))
    have hden : 0 < 2*(|b|+1) := by positivity
    have ht : 0 < t := div_pos (neg_pos.mpr ha) hden
    have hEq : t*(2*(|b|+1)) = -a := div_mul_cancel₀ _ hden.ne'
    have hBound : t*b ≤ t*|b| := mul_le_mul_of_nonneg_left (le_abs_self b) ht.le
    have hNonneg := h t ht
    nlinarith only [hEq,hBound,hNonneg,ht,ha]
  let block : FactorSelfAdjoint → FactorSelfAdjoint → ProductSelfAdjoint := fun P Q =>
    ⟨Matrix.fromBlocks (P : FactorMatrix) 0 0 (Q : FactorMatrix),by
      change (Matrix.fromBlocks (P : FactorMatrix) 0 0 (Q : FactorMatrix))ᴴ = _
      have hP : (P : FactorMatrix)ᴴ = (P : FactorMatrix) := P.2
      have hQ : (Q : FactorMatrix)ᴴ = (Q : FactorMatrix) := Q.2
      rw [Matrix.fromBlocks_conjTranspose,hP,hQ,Matrix.conjTranspose_zero]⟩
  have hBlockAdd (P Q R S : FactorSelfAdjoint) :
      block (P+R) (Q+S) = block P Q+block R S := by
    apply Subtype.ext
    change Matrix.fromBlocks ((P : FactorMatrix)+(R : FactorMatrix)) 0 0 ((Q : FactorMatrix)+(S : FactorMatrix)) =
      Matrix.fromBlocks (P : FactorMatrix) 0 0 (Q : FactorMatrix)+Matrix.fromBlocks (R : FactorMatrix) 0 0 (S : FactorMatrix)
    ext i j
    cases i <;> cases j <;> simp only [block,Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
      Matrix.add_apply,Matrix.zero_apply,zero_add]
  have hBlockScale (t : ℝ) (P Q : FactorSelfAdjoint) : block (t • P) (t • Q) = t • block P Q := by
    apply Subtype.ext
    change Matrix.fromBlocks (t • (P : FactorMatrix)) 0 0 (t • (Q : FactorMatrix)) =
      t • Matrix.fromBlocks (P : FactorMatrix) 0 0 (Q : FactorMatrix)
    ext i j
    cases i <;> cases j <;> simp only [block,Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
      Matrix.smul_apply,smul_eq_mul,Matrix.zero_apply,mul_zero]
  have hBlockSplit (P Q : FactorSelfAdjoint) : block P Q = block P 0+block 0 Q := by
    simpa only [add_zero,zero_add] using hBlockAdd P 0 0 Q
  have hBlockTrace (P Q : FactorSelfAdjoint) (D : ProductSelfAdjoint) :
      Matrix.trace ((block P Q : ProductMatrix)*(D : ProductMatrix)) =
        Matrix.trace ((P : FactorMatrix)*(D : ProductMatrix).toBlocks₁₁)+
        Matrix.trace ((Q : FactorMatrix)*(D : ProductMatrix).toBlocks₂₂) := by
    simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Fintype.sum_sum_type,
      block,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
      Matrix.toBlocks₁₁,Matrix.toBlocks₂₂,Matrix.of_apply,Matrix.zero_apply,zero_mul,
      Finset.sum_const_zero,add_zero,zero_add]
  have hConeScale (G : FactorMatrix) (ell a : FactorVector) (P : FactorSelfAdjoint)
      (hP : P ∈ strictSphereCone G ell a) (t : ℝ) (ht : 0 < t) :
      t • P ∈ strictSphereCone G ell a := by
    intro v hv
    have h := hP v hv
    change 0 < dotProduct a ((t • (P : FactorMatrix))*ᵥ a)+
      dotProduct v ((t • (P : FactorMatrix))*ᵥ v)
    simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
    rw [← mul_add]
    exact mul_pos ht h
  let q : ProductSelfAdjoint × ProductVector → ℝ := fun z => dotProduct z.2 ((z.1 : ProductMatrix)*ᵥ z.2)
  have hQuadScale (P : ProductSelfAdjoint) (t : ℝ) (v : ProductVector) :
      q (P,t • v) = t^2*q (P,v) := by
    simp only [q,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
    ring
  have hPDScale (P : ProductSelfAdjoint) (hP : (P : ProductMatrix).PosDef) (t : ℝ) (ht : 0 < t) :
      ((t • P : ProductSelfAdjoint) : ProductMatrix).PosDef := by
    change (t • (P : ProductMatrix)).PosDef
    exact hP.smul ht
  have hPDConvex (P Q : ProductSelfAdjoint) (hP : (P : ProductMatrix).PosDef) (hQ : (Q : ProductMatrix).PosDef)
      (t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t+s=1) :
      ((t • P+s • Q : ProductSelfAdjoint) : ProductMatrix).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos (t • P+s • Q).2
    intro v hv
    have hPv : 0 < q (P,v) := by simpa only [q,star_trivial] using hP.dotProduct_mulVec_pos hv
    have hQv : 0 < q (Q,v) := by simpa only [q,star_trivial] using hQ.dotProduct_mulVec_pos hv
    have hLin : dotProduct v (((t • P+s • Q : ProductSelfAdjoint) : ProductMatrix)*ᵥ v) =
        t*q (P,v)+s*q (Q,v) := by
      change dotProduct v ((t • (P : ProductMatrix)+s • (Q : ProductMatrix))*ᵥ v) =
        t*q (P,v)+s*q (Q,v)
      simp only [q,Matrix.add_mulVec,Matrix.smul_mulVec,dotProduct_add,
        dotProduct_smul,smul_eq_mul]
    simp only [star_trivial]
    rw [hLin]
    by_cases ht0 : t=0
    · have hs1 : s=1 := by linarith only [ht0,hts]
      simpa only [ht0,hs1,zero_mul,one_mul,zero_add] using hQv
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (lt_of_le_of_ne ht (Ne.symm ht0)) hPv) (mul_nonneg hs hQv.le)
  have hEntry (i j : ProductIndex) : Continuous (fun P : ProductSelfAdjoint => (P : ProductMatrix) i j) :=
    Continuous.comp (f := fun P : ProductSelfAdjoint => (P : ProductMatrix))
      (g := fun A : ProductMatrix => A i j) (continuous_apply_apply i j) continuous_subtype_val
  have hJointEntry (i j : ProductIndex) : Continuous (fun z : ProductSelfAdjoint × ProductVector => (z.1 : ProductMatrix) i j) :=
    Continuous.comp (f := fun z : ProductSelfAdjoint × ProductVector => z.1)
      (g := fun P : ProductSelfAdjoint => (P : ProductMatrix) i j) (hEntry i j) continuous_fst
  have hJointVector (i : ProductIndex) : Continuous (fun z : ProductSelfAdjoint × ProductVector => z.2 i) :=
    Continuous.comp (f := fun z : ProductSelfAdjoint × ProductVector => z.2)
      (g := fun v : ProductVector => v i) (continuous_apply i) continuous_snd
  have hqContinuous : Continuous q := by
    have hRows (i : ProductIndex) : Continuous (fun z : ProductSelfAdjoint × ProductVector =>
        ∑ j : ProductIndex, z.2 i*(z.1 : ProductMatrix) i j*z.2 j) :=
      continuous_finsetSum Finset.univ (fun j _ =>
        ((hJointVector i).mul (hJointEntry i j)).mul (hJointVector j))
    have hSum : Continuous (fun z : ProductSelfAdjoint × ProductVector =>
        ∑ i : ProductIndex, ∑ j : ProductIndex, z.2 i*(z.1 : ProductMatrix) i j*z.2 j) :=
      continuous_finsetSum Finset.univ (fun i _ => hRows i)
    simpa only [q,dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc] using hSum
  have hPDOpen : IsOpen {P : ProductSelfAdjoint | (P : ProductMatrix).PosDef} := by
    apply isOpen_iff_mem_nhds.mpr
    intro P hP
    have hNear : ∀ᶠ Q : ProductSelfAdjoint in 𝓝 P, ∀ v ∈ Metric.sphere (0 : ProductVector) 1, 0 < q (Q,v) := by
      apply (isCompact_sphere (0 : ProductVector) 1).eventually_forall_of_forall_eventually
      intro v hv
      have hvNorm : ‖v‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hv
      have hvNe : v ≠ 0 := by
        intro hv0
        rw [hv0,norm_zero] at hvNorm
        norm_num at hvNorm
      have hp : 0 < q (P,v) := by simpa only [q,star_trivial] using hP.dotProduct_mulVec_pos hvNe
      exact (isOpen_lt continuous_const hqContinuous).mem_nhds hp
    filter_upwards [hNear] with Q hQ
    apply Matrix.PosDef.of_dotProduct_mulVec_pos Q.2
    intro v hv
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let u : ProductVector := ‖v‖⁻¹ • v
    have hu : ‖u‖ = 1 := by
      simp only [u,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hn,
        inv_mul_cancel₀ hn.ne']
    have huSphere : u ∈ Metric.sphere (0 : ProductVector) 1 := by
      simpa only [Metric.mem_sphere,dist_zero_right] using hu
    have hvu : ‖v‖ • u = v := by
      dsimp only [u]
      rw [smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
    have hPosU := hQ u huSphere
    have hScale : q (Q,v) = ‖v‖^2*q (Q,u) := by
      calc
        q (Q,v) = q (Q,‖v‖ • u) := congrArg (fun w : ProductVector => q (Q,w)) hvu.symm
        _ = ‖v‖^2*q (Q,u) := hQuadScale Q ‖v‖ u
    have hPosV : 0 < q (Q,v) := by
      rw [hScale]
      exact mul_pos (sq_pos_of_pos hn) hPosU
    simpa only [q,star_trivial] using hPosV
  obtain ⟨_,_,_,hConv1,⟨P10,hP10⟩,hDual1⟩ :=
    metricMomentCondition_closed_convex_dual G1 hG1 ell1 a1 ha1
  obtain ⟨_,_,_,hConv2,⟨P20,hP20⟩,hDual2⟩ :=
    metricMomentCondition_closed_convex_dual G2 hG2 ell2 a2 ha2
  let C : Set ProductSelfAdjoint := {Q | ∃ P1 ∈ strictSphereCone G1 ell1 a1,
    ∃ P2 ∈ strictSphereCone G2 ell2 a2, ((Q-block P1 P2 : ProductSelfAdjoint) : ProductMatrix).PosDef}
  have hCOpen : IsOpen C := by
    apply isOpen_iff_mem_nhds.mpr
    rintro Q ⟨P1,hP1,P2,hP2,hR⟩
    have hCont : Continuous (fun E : ProductSelfAdjoint => E-block P1 P2) := continuous_id.sub continuous_const
    have hNear : ∀ᶠ E : ProductSelfAdjoint in 𝓝 Q, ((E-block P1 P2 : ProductSelfAdjoint) : ProductMatrix).PosDef :=
      hCont.continuousAt.eventually_mem (hPDOpen.mem_nhds hR)
    filter_upwards [hNear] with E hE
    exact ⟨P1,hP1,P2,hP2,hE⟩
  have hCConvex : Convex ℝ C := by
    intro P hP Q hQ t s ht hs hts
    rcases hP with ⟨P1,hP1,P2,hP2,hRP⟩
    rcases hQ with ⟨Q1,hQ1,Q2,hQ2,hRQ⟩
    refine ⟨t • P1+s • Q1,hConv1 hP1 hQ1 ht hs hts,
      t • P2+s • Q2,hConv2 hP2 hQ2 ht hs hts,?_⟩
    have hR : t • P+s • Q-block (t • P1+s • Q1) (t • P2+s • Q2) =
        t • (P-block P1 P2)+s • (Q-block Q1 Q2) := by
      rw [hBlockAdd,hBlockScale,hBlockScale,smul_sub,smul_sub]
      abel
    rw [hR]
    exact hPDConvex (P-block P1 P2) (Q-block Q1 Q2) hRP hRQ t s ht hs hts
  have hCScale (t : ℝ) (ht : 0 < t) (Q : ProductSelfAdjoint) (hQ : Q ∈ C) : t • Q ∈ C := by
    rcases hQ with ⟨P1,hP1,P2,hP2,hR⟩
    refine ⟨t • P1,hConeScale G1 ell1 a1 P1 hP1 t ht,
      t • P2,hConeScale G2 ell2 a2 P2 hP2 t ht,?_⟩
    rw [hBlockScale,← smul_sub]
    exact hPDScale (Q-block P1 P2) hR t ht
  let I : ProductSelfAdjoint := 1
  have hI : (I : ProductMatrix) = 1 := rfl
  have hINonneg : (I : ProductMatrix).PosSemidef := by rw [hI]; exact Matrix.PosSemidef.one
  have hIPositive : (I : ProductMatrix).PosDef := by rw [hI]; exact Matrix.PosDef.one
  have hCNonempty : C.Nonempty := by
    refine ⟨I+block P10 P20,P10,hP10,P20,hP20,?_⟩
    simpa only [add_sub_cancel_right] using hIPositive
  obtain ⟨K,hKPositive,hK⟩ := exists_pos_covector_penalty_of_tangentSphere_positive
    G1 G2 hG1 hG2 ell1 ell2 a1 a2 ha1 ha2 H hH hsource
  let ell : ProductVector := Sum.elim ell1 ell2
  let Rell : ProductSelfAdjoint := ⟨Matrix.vecMulVec ell ell,by
    change (Matrix.vecMulVec ell ell).IsHermitian
    simpa only [star_trivial] using (Matrix.posSemidef_vecMulVec_self_star ell).isHermitian⟩
  let B : ProductSelfAdjoint := (⟨H,hH⟩ : ProductSelfAdjoint)+K • Rell
  have hBValue : (B : ProductMatrix) = H+K • Matrix.vecMulVec ell ell := rfl
  have hBin : B ∈ C := by
    by_contra hNot
    obtain ⟨f,hSep⟩ := geometric_hahn_banach_point_open hCConvex hCOpen hNot
    obtain ⟨E0,hE0⟩ := hCNonempty
    have hfNe : f ≠ 0 := by
      intro hf
      have h := hSep E0 hE0
      have hFalse : (0 : ℝ) < 0 := by
        simpa only [hf,ContinuousLinearMap.zero_apply] using h
      exact (lt_irrefl (0 : ℝ)) hFalse
    have hfNonneg (E : ProductSelfAdjoint) (hE : E ∈ C) : 0 ≤ f E := by
      apply hAffineLimit (f E) (-f B)
      intro s hs
      have h := hSep (s⁻¹ • E) (hCScale s⁻¹ (inv_pos.mpr hs) E hE)
      rw [map_smul] at h
      change f B < s⁻¹*f E at h
      have hMul := mul_lt_mul_of_pos_left h hs
      have hCancel : s*(s⁻¹*f E) = f E := by rw [← mul_assoc,mul_inv_cancel₀ hs.ne',one_mul]
      rw [hCancel] at hMul
      linarith only [hMul]
    have hfB : f B ≤ 0 := by
      have h : 0 ≤ -f B := hAffineLimit (-f B) (f E0) (by
        intro t ht
        have hSepT := hSep (t • E0) (hCScale t ht E0 hE0)
        rw [map_smul] at hSepT
        change f B < t*f E0 at hSepT
        linarith only [hSepT])
      linarith only [h]
    have hfPD (R : ProductSelfAdjoint) (hR : (R : ProductMatrix).PosDef) : 0 ≤ f R := by
      apply hAffineLimit (f R) (f (block P10 P20))
      intro t ht
      have hIn : R+t • block P10 P20 ∈ C := by
        refine ⟨t • P10,hConeScale G1 ell1 a1 P10 hP10 t ht,
          t • P20,hConeScale G2 ell2 a2 P20 hP20 t ht,?_⟩
        rw [hBlockScale,add_sub_cancel_right]
        exact hR
      have h := hfNonneg _ hIn
      simpa only [map_add,map_smul,smul_eq_mul] using h
    have hfBlock (P Q : FactorSelfAdjoint) (hP : P ∈ strictSphereCone G1 ell1 a1)
        (hQ : Q ∈ strictSphereCone G2 ell2 a2) : 0 ≤ f (block P Q) := by
      apply hAffineLimit (f (block P Q)) (f I)
      intro t ht
      have hIn : block P Q+t • I ∈ C := by
        refine ⟨P,hP,Q,hQ,?_⟩
        have hR : block P Q+t • I-block P Q = t • I := by abel
        rw [hR]
        exact hPDScale I hIPositive t ht
      have h := hfNonneg _ hIn
      simpa only [map_add,map_smul,smul_eq_mul] using h
    have hfBlock1 (P : FactorSelfAdjoint) (hP : P ∈ strictSphereCone G1 ell1 a1) :
        0 ≤ f (block P 0) := by
      apply hAffineLimit (f (block P 0)) (f (block 0 P20))
      intro t ht
      have h := hfBlock P (t • P20) hP (hConeScale G2 ell2 a2 P20 hP20 t ht)
      have hSplit : block P (t • P20) = block P 0+t • block 0 P20 := by
        rw [hBlockSplit P (t • P20),← hBlockScale]
        simp only [smul_zero]
      rw [hSplit,map_add,map_smul] at h
      exact h
    have hfBlock2 (Q : FactorSelfAdjoint) (hQ : Q ∈ strictSphereCone G2 ell2 a2) :
        0 ≤ f (block 0 Q) := by
      apply hAffineLimit (f (block 0 Q)) (f (block P10 0))
      intro t ht
      have h := hfBlock (t • P10) Q (hConeScale G1 ell1 a1 P10 hP10 t ht) hQ
      have hSplit : block (t • P10) Q = block 0 Q+t • block P10 0 := by
        rw [hBlockSplit (t • P10) Q,← hBlockScale]
        simp only [smul_zero]
        abel
      rw [hSplit,map_add,map_smul] at h
      exact h
    obtain ⟨D,hPair,_⟩ := exists_unique_selfAdjoint_trace_pairing f
    have hDNe : (D : ProductMatrix) ≠ 0 := by
      intro hD
      apply hfNe
      apply ContinuousLinearMap.ext
      intro Q
      rw [hPair Q,hD,Matrix.mul_zero,Matrix.trace_zero]
      rfl
    have hDPSD : (D : ProductMatrix).PosSemidef := by
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg D.2
      intro v
      let Rv : ProductSelfAdjoint := ⟨Matrix.vecMulVec v v,by
        change (Matrix.vecMulVec v v).IsHermitian
        simpa only [star_trivial] using (Matrix.posSemidef_vecMulVec_self_star v).isHermitian⟩
      have hRvPSD : (Rv : ProductMatrix).PosSemidef := by
        simpa only [Rv,star_trivial] using Matrix.posSemidef_vecMulVec_self_star v
      have hRv : 0 ≤ f Rv := by
        apply hAffineLimit (f Rv) (f I)
        intro t ht
        have hPD : ((Rv+t • I : ProductSelfAdjoint) : ProductMatrix).PosDef := by
          apply Matrix.PosDef.of_dotProduct_mulVec_pos (Rv+t • I).2
          intro w hw
          have hR : 0 ≤ dotProduct w ((Rv : ProductMatrix)*ᵥ w) := by
            simpa only [star_trivial] using hRvPSD.dotProduct_mulVec_nonneg w
          have hIW : 0 < dotProduct w ((I : ProductMatrix)*ᵥ w) := by
            simpa only [star_trivial] using hIPositive.dotProduct_mulVec_pos hw
          change 0 < dotProduct w (((Rv : ProductMatrix)+t • (I : ProductMatrix))*ᵥ w)
          simp only [star_trivial,Matrix.add_mulVec,Matrix.smul_mulVec,dotProduct_add,
            dotProduct_smul,smul_eq_mul]
          exact add_pos_of_nonneg_of_pos hR (mul_pos ht hIW)
        have h := hfPD (Rv+t • I) hPD
        simpa only [map_add,map_smul,smul_eq_mul] using h
      rw [hPair Rv] at hRv
      change 0 ≤ Matrix.trace (Matrix.vecMulVec v v*(D : ProductMatrix)) at hRv
      rw [Matrix.trace_mul_comm,Matrix.mul_vecMulVec,Matrix.trace_vecMulVec] at hRv
      simpa only [star_trivial,dotProduct_comm] using hRv
    have hTracePositive : 0 < Matrix.trace (D : ProductMatrix) := by
      have hNonneg := hDPSD.trace_nonneg
      have hNe : Matrix.trace (D : ProductMatrix) ≠ 0 := by
        intro h0
        exact hDNe ((hDPSD.trace_eq_zero_iff).mp h0)
      exact lt_of_le_of_ne hNonneg (Ne.symm hNe)
    let D1 : FactorSelfAdjoint := ⟨(D : ProductMatrix).toBlocks₁₁,(show (D : ProductMatrix).IsHermitian from D.2).submatrix Sum.inl⟩
    let D2 : FactorSelfAdjoint := ⟨(D : ProductMatrix).toBlocks₂₂,(show (D : ProductMatrix).IsHermitian from D.2).submatrix Sum.inr⟩
    have hD1Dual (P : FactorSelfAdjoint) (hP : P ∈ strictSphereCone G1 ell1 a1) :
        0 ≤ Matrix.trace ((P : FactorMatrix)*(D1 : FactorMatrix)) := by
      have h := hfBlock1 P hP
      rw [hPair (block P 0),hBlockTrace] at h
      change 0 ≤ Matrix.trace ((P : FactorMatrix)*(D : ProductMatrix).toBlocks₁₁)+
        Matrix.trace ((0 : FactorMatrix)*(D : ProductMatrix).toBlocks₂₂) at h
      simpa only [D1,Matrix.zero_mul,Matrix.trace_zero,add_zero] using h
    have hD2Dual (Q : FactorSelfAdjoint) (hQ : Q ∈ strictSphereCone G2 ell2 a2) :
        0 ≤ Matrix.trace ((Q : FactorMatrix)*(D2 : FactorMatrix)) := by
      have h := hfBlock2 Q hQ
      rw [hPair (block 0 Q),hBlockTrace] at h
      change 0 ≤ Matrix.trace ((0 : FactorMatrix)*(D : ProductMatrix).toBlocks₁₁)+
        Matrix.trace ((Q : FactorMatrix)*(D : ProductMatrix).toBlocks₂₂) at h
      simpa only [D2,Matrix.zero_mul,Matrix.trace_zero,zero_add] using h
    have hMoment1 : metricMomentCondition G1 ell1 a1 (D1 : FactorMatrix) := (hDual1 D1).mp hD1Dual
    have hMoment2 : metricMomentCondition G2 ell2 a2 (D2 : FactorMatrix) := (hDual2 D2).mp hD2Dual
    let t : ℝ := (Matrix.trace (D : ProductMatrix))⁻¹
    have ht : 0 < t := inv_pos.mpr hTracePositive
    let E : ProductSelfAdjoint := t • D
    let E1 : FactorSelfAdjoint := ⟨(E : ProductMatrix).toBlocks₁₁,(show (E : ProductMatrix).IsHermitian from E.2).submatrix Sum.inl⟩
    let E2 : FactorSelfAdjoint := ⟨(E : ProductMatrix).toBlocks₂₂,(show (E : ProductMatrix).IsHermitian from E.2).submatrix Sum.inr⟩
    have hE1Value : (E1 : FactorMatrix) = t • (D1 : FactorMatrix) := by ext i j; rfl
    have hE2Value : (E2 : FactorMatrix) = t • (D2 : FactorMatrix) := by ext i j; rfl
    have hEMoment1 : metricMomentCondition G1 ell1 a1 (E1 : FactorMatrix) := by
      apply (hDual1 E1).mp
      intro P hP
      rw [hE1Value,Matrix.mul_smul,Matrix.trace_smul]
      exact mul_nonneg ht.le (hD1Dual P hP)
    have hEMoment2 : metricMomentCondition G2 ell2 a2 (E2 : FactorMatrix) := by
      apply (hDual2 E2).mp
      intro Q hQ
      rw [hE2Value,Matrix.mul_smul,Matrix.trace_smul]
      exact mul_nonneg ht.le (hD2Dual Q hQ)
    have hETrace : Matrix.trace (E : ProductMatrix) = 1 := by
      change Matrix.trace (t • (D : ProductMatrix)) = 1
      rw [Matrix.trace_smul]
      exact inv_mul_cancel₀ hTracePositive.ne'
    have hEin : E ∈ productMetricMomentSection G1 G2 ell1 ell2 a1 a2 :=
      ⟨hDPSD.smul ht.le,hEMoment1,hEMoment2,hETrace⟩
    have hPos := hK E hEin
    have hNonpos : Matrix.trace ((B : ProductMatrix)*(E : ProductMatrix)) ≤ 0 := by
      change Matrix.trace ((B : ProductMatrix)*(t • (D : ProductMatrix))) ≤ 0
      rw [Matrix.mul_smul,Matrix.trace_smul]
      change t*Matrix.trace ((B : ProductMatrix)*(D : ProductMatrix)) ≤ 0
      rw [← hPair B]
      exact mul_nonpos_of_nonneg_of_nonpos ht.le hfB
    change 0 < Matrix.trace ((B : ProductMatrix)*(E : ProductMatrix)) at hPos
    exact (not_lt_of_ge hNonpos) hPos
  rcases hBin with ⟨P1,hP1,P2,hP2,hR⟩
  exact ⟨P1,P2,K,hKPositive,hP1,hP2,hR⟩

end CalderonN.ProductHessianSeparation

