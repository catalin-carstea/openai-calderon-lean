module

public import Proof.CalderonN.ProductAffineChart
public import Proof.CalderonN.NormalBallChart

import Proof.CalderonN.SmoothLineDifference
import Proof.CalderonN.CompactFiniteJets
import Mathlib.Tactic

/-! Adapted from `ScaledGreenDatumJets` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 2400000

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

abbrev NormalGreenParameter (dim : ℕ) := ℝ × ((X dim) × ℝ)

@[expose] def normalGreenPoint (E : ℝ → (X dim) × (X dim) → (X dim)) (e : ℝ → (Frame dim)) (p : (NormalGreenParameter dim))
    (z : (X dim)) : (X dim) × (X dim) :=
  (normalBallChartMap (E p.1) (e p.1) p.2.1 p.2.2 z,p.2.1)

/-- The normalized Green boundary value with radius an independent
parameter. The kernel argument stays fixed during differentiation. -/
@[expose] def scaledNormalGreenDatum (E : ℝ → (X dim) × (X dim) → (X dim)) (e : ℝ → (Frame dim))
    (G : (X dim) × (X dim) → ℝ) (q : (NormalGreenParameter dim) × (X dim)) : ℝ :=
  q.1.2.2^(dim-2) * G (normalGreenPoint E e q.1 q.2)

private abbrev B (dim : ℕ) := (NormalGreenParameter dim)
private abbrev V (dim : ℕ) := ℝ × ((X dim) × (X dim))

/-- Coordinate change from scaled parameter and angular variables to
the translated radius-scale product rectangle. -/
private def greenDatumToRectangle (E : ℝ → (X dim) × (X dim) → (X dim)) (e : ℝ → (Frame dim)) (η : ℝ)
    (p : (B dim)) (w : (X dim)) (q : (B dim) × (X dim)) : (X dim) × (X dim) :=
  let p' := p+p.2.2 • q.1
  let A : (V dim) := (p.1,(p.2.1,p.2.2 • frameVector (e p.1) p.2.1 w))
  let D : (V dim) := (q.1.1,(q.1.2.1,(1+q.1.2.2) • frameVector (e p'.1) p'.2.1 q.2 -
    frameVector (e p.1) p.2.1 w))
  (η⁻¹ • smoothLineDifference (fun u : (V dim) => E u.1 u.2) (A,(D,p.2.2)), η⁻¹ • q.1.2.1)

theorem contDiff_family_frameVector {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {e : T → I dim → X dim} (he : ∀ i, ContDiff ℝ ∞ (fun q => e q i))
    {v : T → X dim} (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (fun q => ∑ i, v q i • e q i) :=
  ContDiff.sum fun i _ => ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hv).smul (he i)

private theorem contDiff_greenDatumToRectangle {E : ℝ → (X dim) × (X dim) → (X dim)} {e : ℝ → (Frame dim)}
    (hE : ContDiff ℝ ∞ (fun u : (V dim) => E u.1 u.2))
    (he : ∀ i, ContDiff ℝ ∞ (fun u : ℝ × (X dim) => e u.1 u.2 i)) (η : ℝ) :
    ContDiff ℝ ∞ (fun q : ((B dim) × (X dim)) × ((B dim) × (X dim)) => greenDatumToRectangle E e η q.1.1 q.1.2 q.2) := by
  let T := ((B dim) × (X dim)) × ((B dim) × (X dim))
  let P (q : T) := q.1.1
  let P' (q : T) := P q+(P q).2.2 • q.2.1
  have hP : ContDiff ℝ ∞ P := contDiff_fst.fst
  have hP' : ContDiff ℝ ∞ P' := hP.add (hP.snd.snd.smul contDiff_snd.fst)
  let A (q : T) := frameVector (e (P q).1) (P q).2.1 q.1.2
  let A' (q : T) := frameVector (e (P' q).1) (P' q).2.1 q.2.2
  have hA : ContDiff ℝ ∞ A :=
    contDiff_family_frameVector (fun i => (he i).comp (hP.fst.prodMk hP.snd.fst)) contDiff_fst.snd
  have hA' : ContDiff ℝ ∞ A' :=
    contDiff_family_frameVector (fun i => (he i).comp (hP'.fst.prodMk hP'.snd.fst)) contDiff_snd.snd
  have hBase := hP.fst.prodMk (hP.snd.fst.prodMk (hP.snd.snd.smul hA))
  have hDirection : ContDiff ℝ ∞ (fun q : T => (q.2.1.1,(q.2.1.2.1,
      (1+q.2.1.2.2) • A' q-A q))) :=
    contDiff_snd.fst.fst.prodMk (contDiff_snd.fst.snd.fst.prodMk
      (((contDiff_const.add contDiff_snd.fst.snd.snd).smul hA').sub hA))
  have h := (contDiff_smoothLineDifference hE).comp
    (hBase.prodMk (hDirection.prodMk hP.snd.snd))
  exact (h.const_smul _).prodMk (contDiff_snd.fst.snd.fst.const_smul _)

private theorem greenDatumToRectangle_zero {E : ℝ → (X dim) × (X dim) → (X dim)} {e : ℝ → (Frame dim)}
    (η : ℝ) (p : (B dim)) (w : (X dim)) :
    greenDatumToRectangle E e η p w (0,w) = 0 := by
  simp [greenDatumToRectangle,smoothLineDifference,← Prod.zero_eq_mk]

private theorem separateAffineChart_greenDatumToRectangle {E : ℝ → (X dim) × (X dim) → (X dim)}
    {e : ℝ → (Frame dim)} (hE : ContDiff ℝ ∞ (fun u : (V dim) => E u.1 u.2))
    {η : ℝ} (hη : η ≠ 0) (p : (B dim)) (w : (X dim)) (q : (B dim) × (X dim)) :
    let z₀ := normalGreenPoint E e p w
    separateAffineChart z₀.1 z₀.2 (η*p.2.2) (greenDatumToRectangle E e η p w q) =
      normalGreenPoint E e (p+p.2.2 • q.1) q.2 := by
  let r := p.2.2
  let p' := p+r • q.1
  let A : (V dim) := (p.1,(p.2.1,r • frameVector (e p.1) p.2.1 w))
  let D : (V dim) := (q.1.1,(q.1.2.1,(1+q.1.2.2) • frameVector (e p'.1) p'.2.1 q.2 -
    frameVector (e p.1) p.2.1 w))
  have hScalar : (η*r)*η⁻¹ = r := by rw [mul_comm η r,mul_assoc,mul_inv_cancel₀ hη,mul_one]
  have hBase : A+r • D =
      (p'.1,(p'.2.1,p'.2.2 • frameVector (e p'.1) p'.2.1 q.2)) := by
    have hr : p'.2.2 = r*(1+q.1.2.2) := by
      change r+r*q.1.2.2 = _
      ring
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show p.1+r*q.1.1 = p'.1
      rfl
    · show p.2.1+r • q.1.2.1 = p'.2.1
      rfl
    change r • frameVector (e p.1) p.2.1 w +
      r • ((1+q.1.2.2) • frameVector (e p'.1) p'.2.1 q.2 - frameVector (e p.1) p.2.1 w) =
      p'.2.2 • frameVector (e p'.1) p'.2.1 q.2
    rw [hr,smul_sub,smul_smul]
    abel
  apply Prod.ext
  · change E A.1 A.2+(η*r) • (η⁻¹ •
      smoothLineDifference (fun u : (V dim) => E u.1 u.2) (A,(D,r))) = _
    rw [smul_smul,hScalar,smul_smoothLineDifference hE,hBase]
    change E p.1 (p.2.1,r • frameVector (e p.1) p.2.1 w) +
      (E p'.1 (p'.2.1,p'.2.2 • frameVector (e p'.1) p'.2.1 q.2) -
        E p.1 (p.2.1,r • frameVector (e p.1) p.2.1 w)) =
      E p'.1 (p'.2.1,p'.2.2 • frameVector (e p'.1) p'.2.1 q.2)
    abel
  · change p.2.1+(η*r) • (η⁻¹ • q.1.2.1) = _
    rw [smul_smul,hScalar]
    rfl

/-- Uniform product-rectangle jets give uniform jets of the normalized
Green datum in angular variables and radius-scaled parameter variables. -/
theorem exists_scaledNormalGreenDatum_jet_bound
    {E : ℝ → (X dim) × (X dim) → (X dim)} {e : ℝ → (Frame dim)}
    (hE : ContDiff ℝ ∞ (fun u : ℝ × ((X dim) × (X dim)) => E u.1 u.2))
    (he : ∀ i, ContDiff ℝ ∞ (fun u : ℝ × (X dim) => e u.1 u.2 i))
    {K : Set (NormalGreenParameter dim)} (hK : IsCompact K) {η : ℝ} (hη : η ≠ 0) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ w ∈ (standardSphere dim), ∀ G : (X dim) × (X dim) → ℝ,
      ∀ H : (X dim) × (X dim) → ℝ, ContDiff ℝ ∞ H →
      (H =ᶠ[𝓝 0] fun z => p.2.2^(dim-2) *
        G (separateAffineChart (normalGreenPoint E e p w).1 p.2.1 (η*p.2.2) z)) →
      ∀ M : ℝ, 0 ≤ M → (∀ k ≤ n, ‖iteratedFDeriv ℝ k H 0‖ ≤ M) →
      ∃ F : (NormalGreenParameter dim) × (X dim) → ℝ, ContDiff ℝ ∞ F ∧
        F =ᶠ[𝓝 (0,w)] (fun q => scaledNormalGreenDatum E e G (p+p.2.2 • q.1,q.2)) ∧
        ∀ k ≤ n, ‖iteratedFDeriv ℝ k F (0,w)‖ ≤ C*M := by
  let T := ((B dim) × (X dim)) × ((B dim) × (X dim))
  let J : Set T := (K ×ˢ (standardSphere dim)) ×ˢ ({0} ×ˢ (standardSphere dim))
  have hJ : IsCompact J := (hK.prod (isCompact_sphere _ _)).prod
    (isCompact_singleton.prod (isCompact_sphere _ _))
  let A (q : T) := greenDatumToRectangle E e η q.1.1 q.1.2 q.2
  have hA : ContDiff ℝ ∞ A := contDiff_greenDatumToRectangle hE he η
  obtain ⟨D,hD,hAd⟩ := exists_uniform_finite_jet_bound hJ hA n
  let u (q : (B dim) × (X dim)) := (1+q.1.2.2)^(dim-2)
  have hu : ContDiff ℝ ∞ u := (contDiff_const.add contDiff_fst.snd.snd).pow _
  obtain ⟨U,hU,hUd⟩ := exists_uniform_finite_jet_bound
    ((isCompact_singleton (x := (0 : (B dim)))).prod (isCompact_sphere (0 : (X dim)) 1)) hu n
  let C := (2:ℝ)^n*(U*(n.factorial*D^n))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro p hp w hw G H hH hG M hM hMd
  let A' := greenDatumToRectangle E e η p w
  have hA' : ContDiff ℝ ∞ A' := hA.comp
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : (B dim) × (X dim) => (p,w))).prodMk contDiff_id)
  have hA₀ : A' (0,w) = 0 := greenDatumToRectangle_zero η p w
  have hJetA (k : ℕ) (hk : k ≤ n) : ‖iteratedFDeriv ℝ k A' (0,w)‖ ≤ D :=
    (norm_iteratedFDeriv_slice_right_le hA (p,w) (0,w) k).trans
      (hAd ((p,w),(0,w)) ⟨⟨hp,hw⟩,mem_singleton _,hw⟩ k hk)
  let F (q : (B dim) × (X dim)) := u q*H (A' q)
  refine ⟨F,hu.mul (hH.comp hA'),?_,?_⟩
  · have heq := hG.comp_tendsto (show Tendsto A' (𝓝 (0,w)) (𝓝 0) by
      rw [← hA₀]
      exact hA'.continuous.continuousAt)
    filter_upwards [heq] with q hq
    change H (A' q) = p.2.2^(dim-2) * G
      (separateAffineChart (normalGreenPoint E e p w).1 (normalGreenPoint E e p w).2
        (η*p.2.2) (greenDatumToRectangle E e η p w q)) at hq
    change u q*H (A' q) = _
    rw [hq,separateAffineChart_greenDatumToRectangle hE hη]
    unfold scaledNormalGreenDatum
    have hRadius : (p+p.2.2 • q.1).2.2 = p.2.2 * (1+q.1.2.2) := by
      change p.2.2 + p.2.2*q.1.2.2 = _
      ring
    rw [hRadius,mul_pow]
    dsimp only [u]
    ring
  · intro k hk
    have hJet (i : ℕ) (hi : i ≤ n) :
        ‖iteratedFDeriv ℝ i (H ∘ A') (0,w)‖ ≤ n.factorial*M*D^n :=
      norm_iteratedFDeriv_comp_le_of_finite_bounds hH hA' _ hi hM hD
        (by simpa only [hA₀] using hMd) hJetA
    refine (norm_iteratedFDeriv_mul_le_of_finite_bounds hu (hH.comp hA') (0,w) hk
      (zero_le_one.trans hU) (by positivity) (hUd _ ⟨mem_singleton _,hw⟩) hJet).trans_eq ?_
    dsimp only [C]
    ring

end CalderonN
