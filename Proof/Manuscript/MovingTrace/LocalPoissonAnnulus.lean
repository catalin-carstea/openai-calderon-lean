module

public import Proof.Manuscript.MovingTrace.AnnularPoissonCorrection
public import Proof.Manuscript.MovingTrace.PlaneWaveDirichletData
public import Proof.Manuscript.MovingTrace.NormalizedPlaneAmplitude
public import Proof.Manuscript.MovingTrace.CompactPowerSeriesTail
public import Proof.Manuscript.AnnulusJets
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 4300000
set_option backward.isDefEq.respectTransparency false

open CalderonN CalderonPatch CalderonPatch.BoundaryLayer Set Metric
open scoped ContDiff Topology InnerProductSpace

namespace CalderonPaper

variable {n : ℕ} [Nontrivial (Fin (n+1))]
local notation "Z" => X (n+1)
local notation "E" => X n
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
local notation "Q" => P × E

local instance : Fact (Module.finrank ℝ Z = (n + 1) - 1 + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]; omega⟩

namespace SignedPoissonCollar

variable {G : BallPoissonTube P (n+1)} (C : SignedPoissonCollar G)

def rawPoissonSymbol (a : P × E → ℂ) (p : P × E) (ξ : E) : ℂ :=
  dephase 1 ((p.1,ξ),p.2) *
    G.angularPoissonReadout (angularPoint C.pole)
      (C.physicalDatum (fun q => a (q.1.1,q.2)) 1) ((p.1,ξ),p.2)

theorem rawPoissonSymbol_contDiffOn {a : P × E → ℂ} (ha : ContDiff ℝ ∞ a)
    {Kx : Set E} (hKx : IsCompact Kx) (ha₀ : ∀ (p : P) x, x ∉ Kx → a (p,x) = 0) :
    ContDiffOn ℝ ∞ (Function.uncurry (C.rawPoissonSymbol a)) ((G.V ×ˢ univ) ×ˢ univ) := by
  let σ : (P × E) × E → (P × E) × E := fun q => ((q.1.1,q.2),q.1.2)
  have hσ : ContDiff ℝ ∞ σ := (contDiff_fst.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd
  let a' : Q × E → ℂ := fun q => a (q.1.1,q.2)
  have ha' : ContDiff ℝ ∞ a' := ha.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have ht := C.angularPoissonReadout_physicalDatum_contDiffOn ha' hKx (fun p x hx => ha₀ p.1 x hx) 1
  exact ((dephase_contDiff 1).contDiffOn.mul ht).comp hσ.contDiffOn
    (fun q hq => ⟨⟨hq.1.1,mem_univ _⟩,mem_univ _⟩)

theorem normalizedPoissonResponse_eq_symbol (a : P × E → ℂ) (b : Q × E → ℂ)
    {p : P} {ν : E} (hAmp : ∀ x, b ((p,ν),x) = a (p,x)) (h : ℝ) (x : E) :
    C.normalizedPoissonResponse b h ((p,ν),x) = h • C.rawPoissonSymbol a (p,x) (h⁻¹ • ν) := by
  have hPhase : dephase h ((p,ν),x) = dephase 1 ((p,h⁻¹ • ν),x) := by
    change (phase h ((p,ν),x))⁻¹ = (phase 1 ((p,h⁻¹ • ν),x))⁻¹
    rw [phase_eq_angularFourierPhase,phase_eq_angularFourierPhase,inv_one,one_smul]
  unfold normalizedPoissonResponse rawPoissonSymbol
  rw [hPhase,Complex.real_smul,mul_assoc]
  congr 2
  unfold BallPoissonTube.angularPoissonReadout BallPoissonTube.complexPoisson
  congr 2
  funext z
  simp only [Prod.fst,Prod.snd,C.physicalDatum_scale_eq a b p ν hAmp h]

/-- Symbol jet estimates at reciprocal frequency h. They are uniform on
compact geometry sets and compact angular readout sets. All derivatives
are at fixed h and include the frequency direction. -/
theorem exists_radialPoisson_annulus
    {J : Set P} (hJ : IsCompact J) (hJV : J ⊆ G.V)
    {a : P × E → ℂ} (ha : ContDiff ℝ ∞ a)
    {Kx : Set E} (hKx : IsCompact Kx) (ha₀ : ∀ (p : P) x, x ∉ Kx → a (p,x) = 0) :
    ∃ (U : Set P) (D : Set E) (b : ℕ → (P × E) → E → ℂ),
      IsOpen U ∧ J ⊆ U ∧ U ⊆ G.V ∧ IsOpen D ∧ unitAnnulus E ⊆ D ∧
      D ⊆ {0}ᶜ ∧
      (∀ k, ContDiffOn ℝ ∞ (Function.uncurry (b k)) ((U ×ˢ univ) ×ˢ D)) ∧
      (∀ k (p : P) (x ξ : E), x ∉ Kx → b k (p,x) ξ = 0) ∧
      (∀ p ∈ U, ∀ x, ∀ ν ∈ D,
        b 0 (p,x) ν = (C.coefficients.kappa ((p,ν),x) : ℂ) * a (p,x)) ∧
      ∀ {J' : Set P}, IsCompact J' → J' ⊆ U → ∀ {Kout : Set E}, IsCompact Kout →
        ∀ R N : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ h ∈ Ioc (0:ℝ) 1,
          ∀ p ∈ J', ∀ x ∈ Kout, ∀ ν ∈ unitAnnulus E, ∀ j ≤ N,
            ‖iteratedFDeriv ℝ j
              (fun q : Q × E => normalizedAnnulusRemainder (C.rawPoissonSymbol a) b R h
                (q.1.1,q.2) q.1.2) ((p,ν),x)‖ ≤ B*h^R := by
  obtain ⟨U,D,K,A,hU,hJU,hUV,hD,hDD,hD₀,hK,hKU,hKproj,hAs,hA₀,hAmp⟩ :=
    exists_normalized_plane_amplitude G.openV hJ hJV hKx a ha ha₀
  let b (k : ℕ) (p : P × E) (ν : E) := C.transportCoefficient A k ((p.1,ν),p.2)
  have hBS (k : ℕ) : ContDiffOn ℝ ∞ (C.transportCoefficient A k) (baseDomain G) :=
    C.transportCoefficient_contDiffOn hK.isClosed A hAs.contDiffOn hA₀ k
  let σ : (P × E) × E → (P × E) × E := fun q => ((q.1.1,q.2),q.1.2)
  have hσ : ContDiff ℝ ∞ σ := (contDiff_fst.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd
  refine ⟨U,D,b,hU,hJU,hUV,hD,hDD,hD₀,?_,?_,?_,?_⟩
  · intro k
    exact (hBS k).comp hσ.contDiffOn (fun q hq => ⟨⟨hUV hq.1.1,hD₀ hq.2⟩,mem_univ _⟩)
  · intro k p x ξ hx
    exact C.transportCoefficient_zero_of_notMem hK.isClosed A hAs.contDiffOn hA₀ k
      (fun h => hx (hKproj _ h))
  · intro p hp x ν hν
    change C.transportCoefficient A 0 ((p,ν),x) = _
    rw [C.transportCoefficient_principal,hAmp p hp ν hν x]
  · intro J' hJ' hJ'U Kout hOut R N
    let L := 2*N+n+4
    let M := R+3*L+N
    let T := (J' ×ˢ unitAnnulus E) ×ˢ Kout
    let O : Set (Q × E) := (U ×ˢ D) ×ˢ univ
    have hO : IsOpen O := (hU.prod hD).prod isOpen_univ
    have hT : IsCompact T := (hJ'.prod unitAnnulus_isCompact).prod hOut
    have hTO : T ⊆ O := fun q hq => ⟨⟨hJ'U hq.1.1,hDD hq.1.2⟩,mem_univ _⟩
    have hTB : T ⊆ baseDomain G := fun q hq =>
      ⟨⟨hUV (hJ'U hq.1.1),unitAnnulus_ne_zero hq.1.2⟩,mem_univ _⟩
    obtain ⟨B₁,hB₁,hFinite⟩ := C.normalizedPoissonResponse_full_finite_expansion
      hK.isClosed hKU A hAs.contDiffOn hA₀ hKx hKproj hJ' (hJ'U.trans hUV)
      unitAnnulus_isCompact unitAnnulus_ne_zero hOut R N
    obtain ⟨B₂,hB₂,hTail⟩ := compactPowerSeries_tail_jets
      (baseDomain_open (G := G)) hT hTB (C.transportCoefficient A) hBS R (M+1) N (by dsimp only [M]; omega)
    let f (h : ℝ) (q : Q × E) := normalizedAnnulusRemainder (C.rawPoissonSymbol a) b R h
      (q.1.1,q.2) q.1.2
    have hEq (h : ℝ) : EqOn (f h) (fun q => C.normalizedPoissonResponse A h q -
        ∑ k ∈ Finset.range R, (h : ℂ)^k * C.transportCoefficient A k q) O := by
      intro q hq
      have hExact := C.normalizedPoissonResponse_eq_symbol a A (hAmp q.1.1 hq.1.1 q.1.2 hq.1.2) h q.2
      change f h q = C.normalizedPoissonResponse A h q - _
      rw [show C.normalizedPoissonResponse A h q = h • C.rawPoissonSymbol a (q.1.1,q.2) (h⁻¹ • q.1.2) from hExact]
      simp only [f,normalizedAnnulusRemainder,b,Complex.real_smul,Complex.ofReal_pow,Prod.eta]
    have hSmall (h : ℝ) (hh : 0 < h) (hhδ : h ≤ C.δ/2) (q : Q × E) (hq : q ∈ T)
        (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j (f h) q‖ ≤ (B₁+B₂)*h^R := by
      let F (q : Q × E) := C.normalizedPoissonResponse A h q -
        ∑ k ∈ Finset.range (M+1), (h : ℂ)^k * C.transportCoefficient A k q
      let H (q : Q × E) := (∑ k ∈ Finset.range (M+1), (h : ℂ)^k * C.transportCoefficient A k q) -
        ∑ k ∈ Finset.range R, (h : ℂ)^k * C.transportCoefficient A k q
      have he : EqOn (f h) (F+H) O := fun z hz => by
        rw [hEq h hz]
        change _ = F z + H z
        simp only [F,H]
        abel
      have hSum (r : ℕ) : ContDiffAt ℝ ∞
          (fun q => ∑ k ∈ Finset.range r, (h : ℂ)^k * C.transportCoefficient A k q) q :=
        ContDiffAt.sum (fun k _ => contDiffAt_const.mul ((hBS k).contDiffAt
          ((baseDomain_open (G := G)).mem_nhds (hTB hq))))
      have hResp : ContDiffAt ℝ ∞ (C.normalizedPoissonResponse A h) q :=
        (C.normalizedPoissonResponse_contDiffOn hK.isClosed hKU A hAs.contDiffOn hA₀ hKx hKproj hh hhδ).contDiffAt
          (((G.openV.prod isOpen_univ).prod isOpen_univ).mem_nhds
            (show q ∈ (G.V ×ˢ univ) ×ˢ univ from ⟨⟨hUV (hJ'U hq.1.1),mem_univ _⟩,mem_univ _⟩))
      rw [← iteratedFDerivWithin_of_isOpen j hO (hTO hq),iteratedFDerivWithin_congr he (hTO hq) j,
        iteratedFDerivWithin_of_isOpen j hO (hTO hq)]
      rw [iteratedFDeriv_add_apply ((hResp.sub (hSum (M+1))).of_le (by simp))
        (((hSum (M+1)).sub (hSum R)).of_le (by simp)),add_mul]
      exact (norm_add_le _ _).trans <| add_le_add (hFinite h hh hhδ q.1.1 hq.1.1 q.1.2 hq.1.2 q.2 hq.2 j hj)
        (hTail h hh (hhδ.trans (by linarith [C.small])) q hq j hj)
    have hJoint : ContDiffOn ℝ ∞ (Function.uncurry f) (Ioi (0:ℝ) ×ˢ O) := by
      let qMap (z : ℝ × (Q × E)) := ((z.2.1.1,z.2.2),z.1⁻¹ • z.2.1.2)
      have hInv : ContDiffOn ℝ ∞ (fun z : ℝ × (Q × E) => z.1⁻¹) (Ioi 0 ×ˢ O) :=
        contDiffOn_fst.inv (fun z hz => (show 0 < z.1 from hz.1).ne')
      have hMap : ContDiffOn ℝ ∞ qMap (Ioi 0 ×ˢ O) :=
        (contDiffOn_snd.fst.fst.prodMk contDiffOn_snd.snd).prodMk (hInv.smul contDiffOn_snd.fst.snd)
      have hVal := (C.rawPoissonSymbol_contDiffOn ha hKx ha₀).comp hMap
        (fun z hz => (show qMap z ∈ (G.V ×ˢ (univ : Set E)) ×ˢ (univ : Set E) from
          ⟨⟨hUV hz.2.1.1,mem_univ _⟩,mem_univ _⟩))
      have hS (k : ℕ) : ContDiffOn ℝ ∞ (fun z : ℝ × (Q × E) => C.transportCoefficient A k z.2)
          (Ioi 0 ×ˢ O) := (hBS k).comp contDiffOn_snd
        (fun z hz => ⟨⟨hUV hz.2.1.1,hD₀ hz.2.1.2⟩,mem_univ _⟩)
      exact (contDiffOn_fst.smul hVal).sub
        (ContDiffOn.sum (fun k _ => (contDiffOn_fst.pow k).smul (hS k)))
    let W := Icc (C.δ/2) 1 ×ˢ T
    have hW : IsCompact W := isCompact_Icc.prod hT
    have hWO : W ⊆ Ioi (0:ℝ) ×ˢ O := fun z hz => ⟨(half_pos C.pos).trans_le hz.1.1,hTO hz.2⟩
    have hOpen : IsOpen (Ioi (0:ℝ) ×ˢ O) := isOpen_Ioi.prod hO
    have hBig (j : Fin (N+1)) : ∃ B ≥ 0,
        ∀ z ∈ W, ‖iteratedFDeriv ℝ j.val (f z.1) z.2‖ / z.1^R ≤ B := by
      have hC : ContinuousOn (fun z : ℝ × (Q × E) =>
          ‖iteratedFDeriv ℝ j.val (f z.1) z.2‖ / z.1^R) W := by
        intro z hz
        have hPos : 0 < z.1 := (hWO hz).1
        have hJet := contDiffAt_iteratedFDeriv_snd (hJoint.contDiffAt (hOpen.mem_nhds (hWO hz))) j.val
        exact (hJet.continuousAt.norm.div (continuous_fst.pow R).continuousAt
          (pow_ne_zero _ hPos.ne')).continuousWithinAt
      obtain ⟨B,hB⟩ := hW.bddAbove_image hC
      exact ⟨max 0 B,le_max_left _ _,fun z hz => (hB ⟨z,hz,rfl⟩).trans (le_max_right _ _)⟩
    choose B hB hBig using hBig
    let K := 1 + B₁ + B₂ + ∑ j : Fin (N+1), B j
    have hSumN : 0 ≤ ∑ k : Fin (N+1), B k := Finset.sum_nonneg (fun k _ => hB k)
    have hK : 0 < K := by dsimp only [K]; linarith
    refine ⟨K,hK,?_⟩
    intro h hh p hp x hx ν hν j hj
    let q : Q × E := ((p,ν),x)
    have hq : q ∈ T := ⟨⟨hp,hν⟩,hx⟩
    by_cases hδ : h ≤ C.δ/2
    · refine (hSmall h hh.1 hδ q hq j hj).trans (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hh.1.le _))
      have hSum : 0 ≤ ∑ k : Fin (N+1), B k := Finset.sum_nonneg (fun k _ => hB k)
      dsimp only [K]
      linarith
    · let k : Fin (N+1) := ⟨j,Nat.lt_succ_of_le hj⟩
      have hz : (h,q) ∈ W := ⟨⟨le_of_not_ge hδ,hh.2⟩,hq⟩
      have hSimple : B k ≤ K := by
        have hs := Finset.single_le_sum (fun l _ => hB l) (Finset.mem_univ k)
        dsimp only [K]
        linarith
      exact (div_le_iff₀ (pow_pos hh.1 R)).mp ((hBig k (h,q) hz).trans hSimple)

end SignedPoissonCollar
end CalderonPaper
