module

public import Proof.CalderonN.WeightedGreenHorizontal
public import Proof.CalderonN.UniformBallVelocityAdjoint
public import Proof.CalderonN.ActualSignedAdjoint
public import Proof.CalderonN.ConformalGreenDensity

import Proof.CalderonN.AngularAffineDatum
import Mathlib.Tactic

/-! Adapted from `UniformMovingGreenDensity` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 9500000

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- Radius-scaled Green boundary jets give uniform weighted estimates
for the literal density and the first moving trace of its residual. -/
theorem exists_uniform_movingGreenDensity_jet_bounds
    {γ g : ℝ → (MetricField dim)} {E : ℝ → (X dim) × (X dim) → (X dim)} {e : ℝ → (Frame dim)}
    (hγ : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × (X dim) => γ p.1 p.2 i j))
    (hγPos : ∀ lam y, (γ lam y).PosDef)
    (hg : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × (X dim) => g p.1 p.2 i j))
    (hgPos : ∀ lam y, (g lam y).PosDef)
    (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
    (he : ∀ i, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => e q.1 q.2 i))
    {S : Set ℝ} {K Y Y' Ω : Set (X dim)} (hS : IsCompact S) (hK : IsCompact K)
    (hY : IsOpen Y) (hYK : Y ⊆ K) (hKY' : K ⊆ Y')
    {ρ D M L : ℝ} (hρ : 0 < ρ) (hD : 0 ≤ D) (hM : 1 ≤ M) (hL : 0 ≤ L)
    (hNormal : ∀ lam ∈ S, NormalCoordinates Y' Ω (γ lam) (E lam) (fun _ => ρ))
    (hFrame : ∀ lam ∈ S, ∀ y ∈ K, ∀ i j,
      metricPair (γ lam) y (e lam y i) (e lam y j) = if i=j then 1 else 0)
    (hGeom : ∀ lam ∈ S, ∀ y ∈ K, ∀ w ∈ (standardSphere dim),
      (∀ i, ‖connection (γ lam) y (axis i) (frameVector (e lam) y w)‖ ≤ M) ∧
      ‖fderiv ℝ (fun z => (movingBallToFrame (γ lam) (e lam) z).2)
        (y,frameVector (e lam) y w)‖ ≤ M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ lam ∈ S, ∀ r : (X dim) → ℝ, ContDiff ℝ ∞ r →
      (∀ y ∈ Y, r y ∈ Ioc 0 (ρ/2)) → (∀ y ∈ Y, ∀ i, |coordDeriv i r y| ≤ D) →
      ∀ {O : Set ((X dim) × (X dim))}, IsOpen O → ∀ G : (X dim) × (X dim) → ℝ, ContDiffOn ℝ ∞ G O →
      (∀ y ∈ Y, ∀ w : ↥(standardSphere dim), normalGreenPoint E e (lam,(y,r y)) w ∈ O) →
      ∀ y ∈ Y, ScaledSphereDatumJets (2*dim+8) (scaledNormalGreenDatum E e G) (lam,(y,r y)) (r y) L →
      ∀ w : ↥(standardSphere dim),
        let A := actualMovingTraceAdjoint (γ lam) (g lam) (E lam) (e lam) r
        let ψ := complexDensity (movingGreenFluxDensity (γ lam) (g lam) (E lam) (e lam) r G)
        let q := (y,frameVector (e lam) y w)
        ‖(r y : ℂ) * (ψ-1) q‖ ≤ B ∧
        ∀ i, ‖(r y : ℂ) * traceDerivative (γ lam) A i (ψ-1) q‖ ≤ B := by
  let R := ρ/2
  let J : Set (NormalGreenParameter dim) := S ×ˢ (K ×ˢ Icc 0 R)
  let J' : Set (SignedNormalParameter dim) := S ×ˢ (K ×ˢ (Icc 0 R ×ˢ closedBall (0 : (I dim) → ℝ) D))
  have hOrder : dim+4+dim+4 = 2*dim+8 := by omega
  have hJ : IsCompact J := hS.prod (hK.prod isCompact_Icc)
  have hJ' : IsCompact J' := hS.prod (hK.prod (isCompact_Icc.prod (isCompact_closedBall _ _)))
  let U' := signedNormalNondegenerate E e
  let Cb := closedBall (0 : (X dim)) 1
  have hU' : IsOpen U' := signedNormalNondegenerate_isOpen hE he
  have hAdmissible (lam : ℝ) (hl : lam ∈ S) (y : (X dim)) (hy : y ∈ K) (s : ℝ) (hs : s ∈ Icc 0 R)
      (b : (I dim) → ℝ) : {(lam,(y,(s,b)))} ×ˢ Cb ⊆ U' :=
    signedNormalNondegenerate_of_nonneg_radius b (hE.comp (contDiff_const.prodMk contDiff_id))
      (hNormal lam hl) (hKY' hy) (hFrame lam hl y hy) ⟨hs.1,hs.2.trans_lt (half_lt_self hρ)⟩
  have hJ'U' : J' ×ˢ Cb ⊆ U' := by
    rintro ⟨⟨lam,y,s,b⟩,w⟩ ⟨⟨hl,hy,hs,_⟩,hw⟩
    exact hAdmissible lam hl y hy s hs b ⟨mem_singleton _,hw⟩
  let I₀ (q : (NormalGreenParameter dim) × (X dim)) : (SignedNormalParameter dim) × (X dim) :=
    ((q.1.1,(q.1.2.1,(q.1.2.2,0))),q.2)
  have hI₀ : ContDiff ℝ ∞ I₀ :=
    (contDiff_fst.fst.prodMk (contDiff_fst.snd.fst.prodMk
      (contDiff_fst.snd.snd.prodMk contDiff_const))).prodMk contDiff_snd
  let U := I₀ ⁻¹' U'
  have hU : IsOpen U := hU'.preimage hI₀.continuous
  have hJU : J ×ˢ Cb ⊆ U := by
    rintro ⟨⟨lam,y,s⟩,w⟩ ⟨⟨hl,hy,hs⟩,hw⟩
    change ((lam,(y,(s,(0 : (I dim) → ℝ)))),w) ∈ U'
    exact hAdmissible lam hl y hy s hs 0 ⟨mem_singleton _,hw⟩
  have hg₀ (i j : (I dim)) : ContDiffOn ℝ ∞ (fun q => normalGreenMetric g E e q i j) U := by
    change ContDiffOn ℝ ∞ (fun q => signedNormalMetric g E e (I₀ q) i j) U
    exact ((contDiff_signedNormalMetric_entry hg hE he i j).comp hI₀).contDiffOn
  have hg₀' (q : (NormalGreenParameter dim) × (X dim)) (hq : q ∈ U) : (normalGreenMetric g E e q).PosDef := by
    change (signedNormalMetric g E e (I₀ q)).PosDef
    exact signedNormalMetric_posDef (g := g) (E := E) (e := e) (q := I₀ q) hgPos hq
  have hgs (i j : (I dim)) : ContDiffOn ℝ ∞ (fun q => signedNormalMetric g E e q i j) U' :=
    (contDiff_signedNormalMetric_entry hg hE he i j).contDiffOn
  have hgsp (q : (SignedNormalParameter dim) × (X dim)) (hq : q ∈ U') :
      (signedNormalMetric g E e q).PosDef := signedNormalMetric_posDef (E := E) (e := e) hgPos hq
  obtain ⟨C,hC,hCon⟩ := exists_uniform_ballConormalDifference_jets (dim+4) R (half_pos hρ).le hU hJ hJU hg₀ hg₀'
  have hAd (i : (I dim)) := exists_uniform_ballVelocityAdjoint_bound hU' hJ' hJ'U' hgs hgsp
    (contDiffOn_signedNormalVelocity hγ hγPos hE he i)
  choose A hA hAd using hAd
  obtain ⟨J₀,hJ₀,hJ₀jet⟩ := exists_uniform_finite_jet_bound
    (isCompact_sphere (0 : (X dim)) 1 : IsCompact (standardSphere dim)) (contDiff_const (c := (1:ℝ))) (dim+4)
  let P := |(unitSphereArea dim)| * (C*L)+J₀
  let B := R*P+P*(max 1 D+R*M^2) + (∑ i : (I dim), A i)*P
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hR : 0 ≤ R := (half_pos hρ).le
  have hA₀ : 0 ≤ ∑ i : (I dim), A i := Finset.sum_nonneg (fun i _ => hA i)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨B,hB,?_⟩
  intro lam hlam r hr hRad hrJet O hO G hG hSphere
  let Γ := γ lam
  let g' := g lam
  let E' := E lam
  let e' := e lam
  let F := movingBallToFrame Γ e'
  let L₀ := normalGreenAngularLift Γ e' lam r
  have hΓ : SmoothMetric univ Γ :=
    ⟨fun i j => ((hγ i j).comp (contDiff_const.prodMk contDiff_id)).contDiffOn,fun _ _ => hγPos _ _⟩
  have hg' : SmoothMetric univ g' :=
    ⟨fun i j => ((hg i j).comp (contDiff_const.prodMk contDiff_id)).contDiffOn,fun _ _ => hgPos _ _⟩
  have hE' : ContDiff ℝ ∞ E' := hE.comp (contDiff_const.prodMk contDiff_id)
  have he' (i : (I dim)) : ContDiff ℝ ∞ (fun y => e' y i) :=
    (he i).comp (contDiff_const.prodMk contDiff_id)
  have hF : ContDiff ℝ ∞ F := contDiff_movingBallToFrame hΓ he'
  have hFrame' (y : (X dim)) (hy : y ∈ Y) := hFrame lam hlam y (hYK hy)
  obtain ⟨U₀,hU₀,hYB,_,hgm,hgmPos,_⟩ := exists_smooth_movingBallFamilies hΓ hg' hE'
    ((hNormal lam hlam).mono_centers (hYK.trans hKY')) he' hFrame' hr
    (fun y hy => ⟨(hRad y hy).1,(hRad y hy).2.trans_lt (half_lt_self hρ)⟩)
  let Z (q : (X dim) × (X dim)) := (normalBallChartMap E' e' q.1 (r q.1) q.2,q.1)
  let T₀ := Z ⁻¹' O
  have hZ : ContDiff ℝ ∞ Z := (contDiff_movingNormalEndpoint hE' he' hr).prodMk contDiff_fst
  have hT₀ : IsOpen T₀ := hO.preimage hZ.continuous
  have hYT : Y ×ˢ (standardSphere dim) ⊆ T₀ :=
    fun q hq => hSphere q.1 hq.1 ⟨q.2,hq.2⟩
  have hDat : ContDiffOn ℝ ∞ (framedMovingGreenKernel E' e' r G) T₀ :=
    hG.comp hZ.contDiffOn (fun _ h => h)
  let ψ := movingGreenFluxDensity Γ g' E' e' r G
  let ψc := complexDensity ψ - 1
  have hψ : smoothNear ψ (bundle Y Γ) :=
    smoothNear_movingGreenFluxDensity hΓ he' hFrame' hr hU₀ hT₀ hYB hYT hgm hgmPos hDat
  have hψc : smoothNear ψc (bundle Y Γ) := by
    obtain ⟨T,hT,hYT',hp⟩ := hψ
    exact ⟨T,hT,hYT',(Complex.ofRealCLM.contDiff.comp_contDiffOn hp).sub contDiffOn_const⟩
  let u := ballConormalDifference (normalGreenMetric g E e) (scaledNormalGreenDatum E e G)
  let f (q : (NormalGreenParameter dim) × (X dim)) := (unitSphereArea dim)*u q-1
  have hCompare (q : (X dim) × (X dim)) (hy : q.1 ∈ Y) (hn : (F q).2 ≠ 0) : ψ q = (unitSphereArea dim)*u (L₀ q) := by
    let slice (z : (X dim)) := (q.1,z)
    have hI : ContDiff ℝ ∞ slice := contDiff_const.prodMk contDiff_id
    have hu : closedBall (0 : (X dim)) 1 ⊆ slice ⁻¹' U₀ := fun _ hz => hYB ⟨hy,hz⟩
    have hd' : smoothNear (fun z => framedMovingGreenKernel E' e' r G (q.1,z)) (standardSphere dim) :=
      ⟨slice ⁻¹' T₀,hT₀.preimage hI.continuous,fun _ hz => hYT ⟨hy,hz⟩,
        hDat.comp hI.contDiffOn (fun _ h => h)⟩
    exact movingGreenFluxDensity_eq_ballConormalDifference lam r G q
      (hU₀.preimage hI.continuous) hu (smoothMetric_movingBall_slice hgm hgmPos q.1) hd' hn
  have hFcmp (q : (X dim) × (X dim)) (hy : q.1 ∈ Y) (hn : (F q).2 ≠ 0) : ψc q = (f (L₀ q) : ℂ) := by
    change (ψ q : ℂ)-1 = _
    rw [hCompare q hy hn]
    exact (Complex.ofReal_sub _ _).symm
  intro y hy hJet w
  let a : (NormalGreenParameter dim) := (lam,(y,r y))
  let a' := actualSignedNormalParameter lam r y
  have hry := hRad y hy
  have ha : a ∈ J := ⟨hlam,hYK hy,hry.1.le,hry.2⟩
  have ha' : a' ∈ J' := by
    refine ⟨hlam,hYK hy,⟨hry.1.le,hry.2⟩,?_⟩
    rw [mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg hD]
    intro i
    change ‖coordDeriv i r y‖ ≤ D
    simpa only [Real.norm_eq_abs] using hrJet y hy i
  have hAbs : |r y| ≤ R := (abs_of_pos hry.1).symm ▸ hry.2
  obtain ⟨⟨V,hV,haV,huV⟩,hBounds⟩ := hCon _ a ha (r y) L hry.1.ne' hAbs hL (by simpa only [hOrder] using hJet)
  let N : Set (X dim) := ({0}ᶜ : Set (X dim))
  have hN : IsOpen N := isClosed_singleton.isOpen_compl
  have hSN : (standardSphere dim) ⊆ N := by
    intro z hz
    change z ≠ 0
    intro ht
    have hh := mem_sphere_zero_iff_norm.mp hz
    simp [ht] at hh
  have huA : ContDiffOn ℝ ∞ (fun z => u (a,z)) N :=
    huV.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun z hz => ⟨haV,hz⟩)
  obtain ⟨φ,hφ,hφJ⟩ := exists_angularAffineDatum_extension (dim+4) (unitSphereArea dim) hN hSN huA (C*L) J₀
    (mul_nonneg hC hL) hJ₀jet (fun z hz => (hBounds z hz).1)
  let q := (y,frameVector e' y w)
  have hLq : L₀ q = (a,(w:(X dim))) := normalGreenAngularLift_frame (hFrame' y hy)
  have hFq : (F q).2 = (w:(X dim)) := congrArg Prod.snd hLq
  have hψEq : ψc =ᶠ[𝓝 q] (fun z => (f (L₀ z) : ℂ)) := by
    have hn : (F q).2 ∈ N := hFq.symm ▸ hSN w.property
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (hY.mem_nhds hy),
      hF.snd.continuous.continuousAt.preimage_mem_nhds (hN.mem_nhds hn)] with z hz hz'
    exact hFcmp z hz hz'
  have hData (z : (X dim)) (hz : z ∈ (standardSphere dim)) : ψc (y,frameVector e' y z) = (φ z : ℂ) := by
    have hLg : L₀ (y,frameVector e' y z) = (a,z) := normalGreenAngularLift_frame (hFrame' y hy)
    have hFg : (F (y,frameVector e' y z)).2 = z := congrArg Prod.snd hLg
    rw [hFcmp (y,frameVector e' y z) hy (hFg.symm ▸ hSN hz),hLg]
    exact congrArg Complex.ofReal ((hφJ z hz).1.eq_of_nhds.symm)
  have hφValue : ‖φ w‖ ≤ P := by
    simpa only [norm_iteratedFDeriv_zero] using (hφJ w w.property).2 0 (by omega)
  have hValue : ‖(r y : ℂ)*ψc q‖ ≤ R*P := by
    rw [hData w w.property,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul hAbs hφValue (norm_nonneg _) hR
  have hfSmooth : ContDiffOn ℝ ∞ f (V ×ˢ N) :=
    (contDiffOn_const.mul huV).sub contDiffOn_const
  have hfAt : (a,(w:(X dim))) ∈ V ×ˢ N := ⟨haV,hSN w.property⟩
  have hFdiff : DifferentiableAt ℝ f (L₀ q) := by
    rw [hLq]
    exact (hfSmooth.contDiffAt ((hV.prod hN).mem_nhds hfAt)).differentiableAt (by simp)
  have hBase (v : (NormalGreenParameter dim)) :
      ‖fderiv ℝ (fun a' => f (a',w)) a (r y • v)‖ ≤ P*‖v‖ := by
    have huC : ContDiffOn ℝ ∞ (fun a' => u (a',w)) V :=
      huV.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun t ht => ⟨ht,hSN w.property⟩)
    have huD := (huC.contDiffAt (hV.mem_nhds haV)).differentiableAt (by simp)
    change ‖fderiv ℝ (fun a' => (unitSphereArea dim)*u (a',w)-1) a (r y • v)‖ ≤ _
    rw [fderiv_sub_const,fderiv_const_mul huD (unitSphereArea dim),smul_apply,smul_eq_mul,norm_mul,Real.norm_eq_abs]
    refine (mul_le_mul_of_nonneg_left ((hBounds w w.property).2 v) (abs_nonneg _)).trans ?_
    dsimp only [P]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (zero_le_one.trans hJ₀)) (norm_nonneg _)
  have hAngle : ‖fderiv ℝ (fun z => f (a,z)) w‖ ≤ P := by
    rw [← (hφJ w w.property).1.fderiv_eq,← norm_iteratedFDeriv_one]
    exact (hφJ w w.property).2 1 (by norm_num)
  have hHor (i : (I dim)) : ‖(r y : ℂ)*horizontal Γ ψc y q.2 (axis i)‖ ≤ P*(max 1 D+R*M^2) := by
    change ‖(r y : ℂ)*fderiv ℝ ψc q (axis i,-connection Γ y (axis i) q.2)‖ ≤ _
    rw [hψEq.fderiv_eq]
    exact norm_weighted_horizontal_normalGreenAngularLift_le hΓ he' lam hr i q hR hD hM hP hAbs
      (hrJet y hy i) ((hGeom lam hlam y (hYK hy) w w.property).1 i)
      (hGeom lam hlam y (hYK hy) w w.property).2 hFdiff
      (by
        change ∀ v : (NormalGreenParameter dim), ‖fderiv ℝ (fun a' => f (a',(L₀ q).2))
          (L₀ q).1 (r y • v)‖ ≤ P*‖v‖
        rw [hLq]
        exact hBase)
      (by
        change ‖fderiv ℝ (fun z => f ((L₀ q).1,z)) (L₀ q).2‖ ≤ P
        rw [hLq]
        exact hAngle)
  let signedSlice (z : (X dim)) := (a',z)
  let U₂ := signedSlice ⁻¹' U'
  let T₂ := U₂ ∩ N
  have hI' : ContDiff ℝ ∞ signedSlice := contDiff_const.prodMk contDiff_id
  have hU₂ : IsOpen U₂ := hU'.preimage hI'.continuous
  have hT₂ : IsOpen T₂ := hU₂.inter hN
  have hCU₂ : Cb ⊆ U₂ := fun z hz => hJ'U' ⟨ha',hz⟩
  have hST₂ : (standardSphere dim) ⊆ T₂ := fun z hz => ⟨hCU₂ (sphere_subset_closedBall hz),hSN hz⟩
  have hm₂ : SmoothMetric U₂ (fun z => signedNormalMetric g E e (a',z)) :=
    ⟨fun i j => (hgs i j).comp hI'.contDiffOn (fun _ h => h),
      fun z hz => hgsp (a',z) hz⟩
  let Adj := actualMovingTraceAdjoint Γ g' E' e' r
  have hAdj (i : (I dim)) : ‖(r y : ℂ)*adjointField Adj i ψc q‖ ≤ A i*P := by
    have hV₂ := (contDiffOn_signedNormalVelocity hγ hγPos hE he i).comp hI'.contDiffOn
      (show MapsTo signedSlice T₂ U' from fun z hz => hz.1)
    have he := scaled_actualMovingTraceAdjoint_eq_signed
      (γ := γ) (g := g) (E := E) (e := e) hy hry.1.ne' (hFrame' y hy) i ψc hψc
      (fun q => φ q.2) hU₂ hT₂ hCU₂ hST₂ inter_subset_left (fun h => h.2 rfl)
      hm₂ hV₂ hφ.contDiffOn hData w.property
    change ‖(r y : ℂ)*adjointField Adj i ψc q‖ ≤ _
    rw [he,Complex.norm_real]
    exact hAd i a' ha' φ hφ P hP (fun z hz => (hφJ z hz).2) w w.property
  refine ⟨hValue.trans ?_,fun i => ?_⟩
  · dsimp only [B]
    exact (le_add_of_nonneg_right (by positivity : 0 ≤ P*(max 1 D+R*M^2))).trans
      (le_add_of_nonneg_right (mul_nonneg hA₀ hP))
  · change ‖(r y : ℂ)*traceDerivative Γ Adj i ψc q‖ ≤ B
    rw [traceDerivative,mul_add]
    refine (norm_add_le _ _).trans ((add_le_add (hHor i) (hAdj i)).trans ?_)
    have hAi : A i ≤ ∑ i : (I dim), A i := Finset.single_le_sum (fun i _ => hA i) (Finset.mem_univ i)
    dsimp only [B]
    exact (add_le_add le_rfl (mul_le_mul_of_nonneg_right hAi hP)).trans (by linarith [mul_nonneg hR hP])

end CalderonN
