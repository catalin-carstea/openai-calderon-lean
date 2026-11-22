module

public import Proof.CalderonN.ActualRotatedConormalTraceGerm
public import Proof.CalderonN.ActualPhysicalWeakConormalJets
public import Proof.CalderonN.FiniteSmoothTraceAngularModel

import Mathlib.Tactic

/-! Weighted chart jets for the rotation commutator of the scaled
physical conormal remainder. -/

public section

noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxSynthPendingDepth 29
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

structure ActualPhysicalRotatedConormalJet (d : Data dim) (Y : Set (X dim)) (y : X dim)
    (N : ℕ) (C : ℝ) (D : ∀ x ∈ Y, ActualGaussFiberData d x) (i j : I dim) where
  form : X dim → WeakHalfConormal dim
  smooth : ContDiffAt ℝ ∞ form y
  bound : ∀ n ≤ N, ‖iteratedFDeriv ℝ n form y‖ ≤ C*(beta d.γ d.radius y)^n
  neighborhood : Set (X dim)
  openNeighborhood : IsOpen neighborhood
  center_mem : y ∈ neighborhood
  sub : neighborhood ⊆ Y
  eq_finite : ∀ x (hx : x ∈ neighborhood), ∀ f g : HarmonicFiniteCoefficients dim,
    form x (harmonicBoundaryFiniteL (1/2:ℝ) f) (harmonicBoundaryFiniteL (1/2:ℝ) g) =
      ((d.radius x)^2)⁻¹*unitSphereArea dim *
        ∫ w : ↥(standardSphere dim),(harmonicFiniteSmooth g).1 w*
          ((smoothSphereTraceRotation i j*(D x (sub hx)).conormalRemainder-
            (D x (sub hx)).conormalRemainder*smoothSphereTraceRotation i j)
              (finiteHarmonicSmoothTraceL f)).1 w
          ∂(sphereProbability dim)

theorem uniform_actual_physicalRotatedConormal_jets (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y)) (hSub : Y ⊆ Ω)
    {m : ℕ} (N : ℕ) (hN : N ≤ 8) (hm : N+5 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i, d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ (D : ∀ x ∈ Y,ActualGaussFiberData d x),
        (∀ x (hx : x ∈ Y),∀ z ∈ ball (0:X dim) 1,((D x hx).coefficient z).IsSymm) →
        ∀ i j : I dim,∀ y ∈ Y, Nonempty (ActualPhysicalRotatedConormalJet d Y y N C D i j) := by
  obtain ⟨C,hC,hLog⟩ := uniform_background_logRadius_chart_jets hY hΩ hSub N hN (by omega)
    K M Cj (zero_lt_one.trans_le hK)
  obtain ⟨A,hA,hR⟩ := uniform_physicalRadius_restrict_quadratic_jets (F:=WeakHalfConormal dim)
    hY N (max 1 C) (le_max_left _ _)
  obtain ⟨η,B,hη,hB,hG⟩ := uniform_actual_relativeRotatedConormal_taylor hn hY hΩ hYc N hm K ρ c₀ M Cj hK hρ
  refine ⟨η,A*B,hη,mul_nonneg hA hB,?_⟩
  intro floor hf ε he hs d hd hFrame D hSym i j y hy
  let r := d.radius
  let β := beta d.γ r y
  let p (x : X dim) := (x,r x/r y-1)
  have hP := hd.2.2.2.2.1
  have hp (x : X dim) (hx : x ∈ Y) : 0 < r x := (hP.2 x hx).1
  have hb : 1 ≤ β := hf.trans (hP.2 y hy).2.1
  have hL (n : ℕ) (hnN : n ≤ N) (hn₁ : 1 ≤ n) :
      ‖iteratedFDeriv ℝ n (fun x => Real.log (r x)) y‖ ≤ max 1 C*β^n :=
    (hLog _ _ _ _ hd.1 r floor c₀ hf hP y hy n hnN hn₁).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (zero_le_one.trans hb) _))
  obtain ⟨H⟩ := hG floor hf ε he hs d hd hFrame y hy
  let G (p : X dim × ℝ) : WeakHalfConormal dim :=
    fixedBallWeakConormalRotatedTaylor (r y) (H.energy.first p) (H.energy.second p)
      (H.energy.rotFirst i j p) (H.energy.rotSecond i j p)
  have hEst := hR r hP.1 y hy hp β hb hL G B (H.remainderBound i j)
  have hpY : p y = (y,0) := by simp [p,(hp y hy).ne']
  have hps : ContinuousOn p Y :=
    continuous_id.continuousOn.prodMk ((hP.1.continuousOn.div continuousOn_const
      (fun _ _ => (hp y hy).ne')).sub continuousOn_const)
  let V := Y ∩ p ⁻¹' H.energy.neighborhood
  have hV : IsOpen V := hps.isOpen_inter_preimage hY H.energy.openNeighborhood
  have hyV : y ∈ V := ⟨hy,by rw [mem_preimage,hpY]; exact H.energy.center_mem⟩
  refine ⟨⟨fun x => ((r x)^2)⁻¹ • G (p x),hEst.1,hEst.2,V,hV,hyV,inter_subset_left,?_⟩⟩
  intro x hx f g
  have hEq := H.eq_physical_rotation_finite (hp y hy).ne' hx.2 (D x hx.1) (hSym x hx.1) i j f g
  change ((r x)^2)⁻¹ * G (p x) (harmonicBoundaryFiniteL (1/2:ℝ) f)
    (harmonicBoundaryFiniteL (1/2:ℝ) g) = _
  rw [show G (p x) (harmonicBoundaryFiniteL (1/2:ℝ) f) (harmonicBoundaryFiniteL (1/2:ℝ) g) = _ from hEq,mul_assoc]

end CalderonN
