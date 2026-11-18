import Proof.TracePairing
import Mathlib.Analysis.Calculus.TangentCone.Real

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma Dirichlet.eqOn_solutions {Y : Set X} {g g₁ : MetricField} {expMap : X × X → X} {r : X → ℝ}
    (hD : Dirichlet Y g g₁ expMap r) {y : X} (hy : y ∈ Y) (a : X → ℝ) (ha : smoothNear a (sphereAt g y))
    (u v : X → ℝ)
    (hu : HarmonicOnBall g₁ (closedBallImage g expMap r y) u ∧ ∀ w ∈ sphereAt g y,u (endpoint expMap r (y,w)) = a w)
    (hv : HarmonicOnBall g₁ (closedBallImage g expMap r y) v ∧ ∀ w ∈ sphereAt g y,v (endpoint expMap r (y,w)) = a w) :
    EqOn u v (closedBallImage g expMap r y) := by
  obtain ⟨u₀,hu₀,hunique⟩ := hD y hy a ha
  intro x hx
  exact (hunique u hu hx).symm.trans (hunique v hv hx)

lemma hasDerivAt_radialTrace (expMap : X × X → X) (r u : X → ℝ) (y w : X)
    (he : DifferentiableAt ℝ expMap (y,r y • w))
    (hu : DifferentiableAt ℝ u (endpoint expMap r (y,w))) :
    HasDerivAt (fun t : ℝ => ballPullback expMap r y u (t • w)) (radialTrace expMap r y w u) 1 := by
  have hscaled : HasDerivAt (fun t : ℝ => r y • (t • w)) (r y • w) 1 := by
    convert (((hasDerivAt_id (1:ℝ)).smul_const w).const_smul (r y)) using 1 <;> simp only [Function.id_def,one_smul]
    funext t
    rfl
  have hs : HasDerivAt (fun t : ℝ => (y,r y • (t • w))) ((0:X),r y • w) 1 :=
    (hasDerivAt_const (1:ℝ) y).prodMk hscaled
  have he' : HasFDerivAt expMap (fderiv ℝ expMap (y,r y • w)) (y,r y • ((1:ℝ) • w)) := by simpa only [one_smul] using he.hasFDerivAt
  have hu' : HasFDerivAt u (fderiv ℝ u (endpoint expMap r (y,w))) (expMap (y,r y • ((1:ℝ) • w))) := by
    simpa only [one_smul,endpoint] using hu.hasFDerivAt
  have ht := hu'.comp_hasDerivAt 1 (he'.comp_hasDerivAt 1 hs)
  rw [radialTrace_eq expMap r u y w he hu]
  exact ht

/-- The boundary radial derivative is determined by the solution inside the closed ball.
    The one-sided radial interval has unique differentiation at its boundary endpoint. -/
theorem radialTrace_congr_closedBall {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y : X} (hy : y ∈ Y) (w : X) (hw : w ∈ sphereAt d.γ y)
    (u v : X → ℝ) (hu : HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u)
    (hv : HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) v)
    (heq : EqOn u v (closedBallImage d.γ d.expMap d.radius y)) :
    radialTrace d.expMap d.radius y w u = radialTrace d.expMap d.radius y w v := by
  obtain ⟨_,hExp,hU⟩ := dirichlet_differentiability Y Ω hY hd y w hy hw u hu
  obtain ⟨_,_,hV⟩ := dirichlet_differentiability Y Ω hY hd y w hy hw v hv
  have hdu := hasDerivAt_radialTrace d.expMap d.radius u y w hExp hU
  have hdv := hasDerivAt_radialTrace d.expMap d.radius v y w hExp hV
  have hpath : ∀ t ∈ Icc (0:ℝ) 1,ballPullback d.expMap d.radius y u (t • w) = ballPullback d.expMap d.radius y v (t • w) := by
    intro t ht
    have ht2 : t^2 ≤ 1 := by nlinarith [ht.1,ht.2]
    have hmem : d.radius y • (t • w) ∈ disk d.γ y (d.radius y) := by
      change metricPair d.γ y (d.radius y • (t • w)) (d.radius y • (t • w)) ≤ (d.radius y)^2
      change metricPair d.γ y w w = 1 at hw
      simp only [metricPair_smul_left,metricPair_smul_right,hw]
      have hmul := mul_le_mul_of_nonneg_right ht2 (sq_nonneg (d.radius y))
      nlinarith only [hmul]
    exact heq ⟨d.radius y • (t • w),hmem,rfl⟩
  have hOne : (1:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have huniq := uniqueDiffOn_Icc_zero_one 1 hOne
  have hvOn := hdv.hasDerivWithinAt.congr hpath (hpath 1 hOne)
  exact (hdu.hasDerivWithinAt.derivWithin huniq).symm.trans (hvOn.derivWithin huniq)

/-- Actual Dirichlet boundary data have a uniquely determined radial response. No extra
    Dirichlet-to-Neumann axiom or external choice of a normal trace is introduced. -/
theorem Admissible.exists_radialDirichletResponse {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y : X} (hy : y ∈ Y)
    (a : X → ℝ) (ha : smoothNear a (sphereAt d.γ y)) :
    ∃ b : X → ℝ,∀ u : X → ℝ,
      HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u →
      (∀ w ∈ sphereAt d.γ y,u (endpoint d.expMap d.radius (y,w)) = a w) →
      ∀ w ∈ sphereAt d.γ y,radialTrace d.expMap d.radius y w u = b w := by
  obtain ⟨u₀,hu₀,_⟩ := hd.2.2.1 y hy a ha
  refine ⟨fun w => radialTrace d.expMap d.radius y w u₀,?_⟩
  intro u hu htrace w hw
  exact radialTrace_congr_closedBall hY hd hy w hw u u₀ hu hu₀.1
    (hd.2.2.1.eqOn_solutions hy a ha u u₀ ⟨hu,htrace⟩ hu₀)


/-- A canonical representative of the radial Dirichlet response, used only on the unit sphere. -/
def radialDirichletResponse {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y : X} (hy : y ∈ Y)
    (a : X → ℝ) (ha : smoothNear a (sphereAt d.γ y)) : X → ℝ :=
  Classical.choose (hd.exists_radialDirichletResponse hY hy a ha)

lemma radialDirichletResponse_eq {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y : X} (hy : y ∈ Y)
    (a : X → ℝ) (ha : smoothNear a (sphereAt d.γ y)) (u : X → ℝ)
    (hu : HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u)
    (htrace : ∀ w ∈ sphereAt d.γ y,u (endpoint d.expMap d.radius (y,w)) = a w)
    (w : X) (hw : w ∈ sphereAt d.γ y) :
    radialDirichletResponse hY hd hy a ha w = radialTrace d.expMap d.radius y w u :=
  (Classical.choose_spec (hd.exists_radialDirichletResponse hY hy a ha) u hu htrace w hw).symm

lemma HarmonicOnBall.const (g : MetricField) (ball : Set X) (c : ℝ) :
    HarmonicOnBall g ball (fun _ => c) := by
  refine ⟨⟨univ,isOpen_univ,subset_univ _,contDiffOn_const⟩,?_⟩
  intro x hx
  have hcoord (i : I) : coordDeriv i (fun _ : X => c) = 0 := by
    funext z
    simp [coordDeriv]
  have hz (i : I) (z : X) : coordDeriv i (0 : X → ℝ) z = 0 := by simp [coordDeriv]
  simp [laplace,hcoord,hz]

lemma radialTrace_const (expMap : X × X → X) (r : X → ℝ) (y w : X) (c : ℝ) :
    radialTrace expMap r y w (fun _ => c) = 0 := by
  change (fderiv ℝ (fun _ : X => c) w) w = 0
  simp

lemma radialDirichletResponse_const {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y : X} (hy : y ∈ Y)
    (c : ℝ) (ha : smoothNear (fun _ : X => c) (sphereAt d.γ y)) (w : X) (hw : w ∈ sphereAt d.γ y) :
    radialDirichletResponse hY hd hy (fun _ => c) ha w = 0 := by
  rw [radialDirichletResponse_eq hY hd hy _ ha (fun _ => c) (HarmonicOnBall.const _ _ c) (fun _ _ => rfl) w hw]
  exact radialTrace_const _ _ _ _ _

end ShrinkingSpheres
