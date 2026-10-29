import Mathlib

namespace GleasonKahaneZelazkoTheorem

open Set Metric
private lemma global_log (f : ℂ → ℂ) (hf : Differentiable ℂ f) (h0 : f 0 = 1)
    (hn : ∀ z, f z ≠ 0) : ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g 0 = 0 ∧ ∀ z, Complex.exp (g z) = f z := by
  have hd : Differentiable ℂ (deriv f) := by
    have h := hf.differentiableOn.analyticOnNhd isOpen_univ
    simpa only [differentiableOn_univ] using h.deriv.differentiableOn
  let q := fun z => deriv f z / f z
  have hq : Differentiable ℂ q := hd.div hf hn
  let g := fun z => Complex.wedgeIntegral 0 z q
  have hg (z : ℂ) : HasDerivAt g (q z) z := by
    let R := ‖z‖ + 1
    have hz : z ∈ ball (0 : ℂ) R := by simp [R]
    exact (hq.differentiableOn (s := ball 0 R)).isConservativeOn.hasDerivAt_wedgeIntegral hq.continuous.continuousOn hz
  have hg0 : g 0 = 0 := by simp [g, Complex.wedgeIntegral]
  refine ⟨g, fun z => (hg z).differentiableAt, hg0, ?_⟩
  have hk (z : ℂ) : HasDerivAt (fun z => f z / Complex.exp (g z)) 0 z := by
    have t := (hf z).hasDerivAt.div ((hg z).cexp) (Complex.exp_ne_zero (g z))
    convert t using 1 <;> dsimp [q] <;> field_simp [hn z, Complex.exp_ne_zero (g z)] <;> ring
  have hc : (fun z => f z / Complex.exp (g z)) = fun _ => 1 := by
    have hc := is_const_of_deriv_eq_zero (fun z => (hk z).differentiableAt) (fun z => (hk z).deriv)
    funext z
    simpa [h0, hg0] using hc z 0
  intro z
  have t := congr_fun hc z
  simp only at t
  exact (div_eq_one_iff_eq (Complex.exp_ne_zero (g z))).mp t |>.symm

private lemma linear_of_re_growth (g : ℂ → ℂ) (hg : Differentiable ℂ g) (hg0 : g 0 = 0)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ z, (g z).re ≤ C * ‖z‖ + D) : ∀ z, g z = z * deriv g 0 := by
  have hbound (z : ℂ) : ‖g z‖ ≤ (4*C + 2*D + 2) * ‖z‖ := by
    let R : ℝ := 2 * (‖z‖ + 1)
    let M : ℝ := C*R+D+1
    have hR : 0 < R := by dsimp [R]; positivity
    have hM : 0 < M := by dsimp [M]; positivity
    have hz : z ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg z]
    have hmaps : MapsTo g (ball 0 R) {z | z.re < M} := by
      intro w hw
      have hw' : ‖w‖ < R := mem_ball_zero_iff.mp hw
      change (g w).re < M
      have := hb w
      dsimp [M]
      nlinarith
    have t := Complex.borelCaratheodory_zero hM hg.differentiableOn hmaps hR hz hg0
    have hr : 0 < R - ‖z‖ := by dsimp [R]; linarith [norm_nonneg z]
    apply le_trans t
    apply (div_le_iff₀ hr).2
    dsimp [M, R]
    have := norm_nonneg z
    nlinarith [mul_nonneg hC this, mul_nonneg hD this]
  have hd : Differentiable ℂ (dslope g 0) := by
    have t := (Complex.differentiableOn_dslope (s := (univ : Set ℂ)) (c := 0) (by simp)).2 hg.differentiableOn
    simpa only [differentiableOn_univ] using t
  have hbds (z : ℂ) : ‖dslope g 0 z‖ ≤ (4*C+2*D+2) + ‖deriv g 0‖ := by
    by_cases hz : z = 0
    · subst z; rw [dslope_same]; linarith [show 0 ≤ 4*C+2*D+2 by positivity]
    · rw [dslope_of_ne _ hz, slope_def_field]
      simp only [sub_zero, hg0, norm_div]
      have := hbound z
      have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have := (div_le_iff₀ hp).2 this
      linarith [norm_nonneg (deriv g 0)]
  have hconst : ∀ z, dslope g 0 z = dslope g 0 0 := by
    intro z
    have hbnd : Bornology.IsBounded (range (dslope g 0)) := by
      apply isBounded_iff_forall_norm_le.mpr
      refine ⟨4*C + 2*D + 2 + ‖deriv g 0‖, ?_⟩
      rintro x ⟨w, rfl⟩
      exact hbds w
    exact hd.apply_eq_apply_of_bounded hbnd z 0
  intro z
  have t := sub_smul_dslope g 0 z
  rw [hconst z, dslope_same] at t
  simpa [hg0, smul_eq_mul] using t.symm

private lemma entire_exp_type (f : ℂ → ℂ) (hf : Differentiable ℂ f) (h0 : f 0 = 1)
    (hn : ∀ z, f z ≠ 0) (C K : ℝ) (hC : 0 ≤ C) (hK : 1 ≤ K)
    (hb : ∀ z, ‖f z‖ ≤ K * Real.exp (C * ‖z‖)) :
    ∀ z, f z = Complex.exp (z * deriv f 0) := by
  obtain ⟨g, hg, hg0, he⟩ := global_log f hf h0 hn
  have hre (z : ℂ) : (g z).re ≤ C * ‖z‖ + Real.log K := by
    have t := hb z
    rw [← he z, Complex.norm_exp] at t
    have ht := Real.log_le_log (Real.exp_pos _) t
    rw [Real.log_exp, Real.log_mul (by positivity : K ≠ 0) (by positivity : Real.exp (C * ‖z‖) ≠ 0), Real.log_exp] at ht
    linarith
  have hl := linear_of_re_growth g hg hg0 C (Real.log K) hC (Real.log_nonneg hK) hre
  have hd : deriv f 0 = deriv g 0 := by
    have t : HasDerivAt f (deriv g 0) 0 := by
      have tt := (hg 0).hasDerivAt.cexp
      simp only [hg0, Complex.exp_zero, one_mul] at tt
      exact tt.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z => (he z).symm))
    exact t.deriv
  intro z
  rw [hd, ← he z, hl z]

private lemma entire_exponential (f : ℂ → ℂ) (hf : Differentiable ℂ f) (h0 : f 0 = 1)
    (hn : ∀ z, f z ≠ 0) (C D : ℝ) (hC : 1 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ z, ‖f z‖ ≤ C * Real.exp (D * ‖z‖)) :
    ∀ z, f z = Complex.exp (z * deriv f 0) := by
  obtain ⟨g, hg, hg0, hfg⟩ := global_log f hf h0 hn
  have hbound (z : ℂ) : (g z).re ≤ D * ‖z‖ + Real.log C := by
    have hpos : 0 < C := by linarith
    have h := Real.log_le_log (norm_pos_iff.mpr (hn z)) (hb z)
    rw [← hfg z, Complex.norm_exp, Real.log_exp, Real.log_mul (ne_of_gt hpos)
      (ne_of_gt (Real.exp_pos _)), Real.log_exp] at h
    linarith
  have hglinear := linear_of_re_growth g hg hg0 D (Real.log C) hD (Real.log_nonneg hC) hbound
  have hderiv : deriv f 0 = deriv g 0 := by
    have heq : f = fun z => Complex.exp (g z) := funext fun z => (hfg z).symm
    rw [heq]
    simpa [hg0] using ((hg 0).hasDerivAt.cexp.deriv)
  intro z
  rw [← hfg z, hglinear z, hderiv]

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

private lemma spectral (φ : A →ₗ[ℂ] ℂ) (h1 : φ 1 = 1)
    (hunit : ∀ a : A, IsUnit a → φ a ≠ 0) (a : A) : φ a ∈ spectrum ℂ a := by
  rw [spectrum.mem_iff]
  intro h
  have hzero : φ (algebraMap ℂ A (φ a) - a) = 0 := by
    rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, h1]
    simp
  exact hunit _ h hzero

private lemma bound (φ : A →ₗ[ℂ] ℂ) (h1 : φ 1 = 1)
    (hunit : ∀ a : A, IsUnit a → φ a ≠ 0) (a : A) : ‖φ a‖ ≤ ‖a‖ * ‖(1 : A)‖ :=
  spectrum.norm_le_norm_mul_of_mem (spectral φ h1 hunit a)

private lemma cont (φ : A →ₗ[ℂ] ℂ) (h1 : φ 1 = 1)
    (hunit : ∀ a : A, IsUnit a → φ a ≠ 0) : Continuous φ := by
  apply AddMonoidHomClass.continuous_of_bound φ ‖(1 : A)‖
  intro a
  simpa [mul_comm] using bound φ h1 hunit a

private lemma square_implies_mul (φ : A →ₗ[ℂ] ℂ)
    (hsq : ∀ a, φ (a*a) = φ a * φ a) (x y : A) : φ (x*y) = φ x * φ y := by
  have jordan (a b : A) : φ (a*b) + φ (b*a) = 2 * φ a * φ b := by
    have h := hsq (a+b)
    rw [show (a+b)*(a+b) = a*a + (a*b + b*a) + b*b by noncomm_ring] at h
    simp only [map_add] at h
    linear_combination h - hsq a - hsq b
  have sandwich (a b : A) : φ (a*b*a) = φ a * φ a * φ b := by
    have h := jordan a (a*b+b*a)
    have h' := jordan (a*a) b
    rw [show a*(a*b+b*a) = a*a*b + a*b*a by noncomm_ring,
        show (a*b+b*a)*a = a*b*a + b*(a*a) by noncomm_ring] at h
    simp only [map_add] at h
    rw [jordan a b] at h
    rw [hsq a] at h'
    linear_combination (h - h') / 2
  have h := jordan (x*y) (y*x)
  have h' := hsq (x*y+y*x)
  rw [show (x*y+y*x)*(x*y+y*x) = (x*y)*(x*y) + ((x*y)*(y*x) + (y*x)*(x*y)) + (y*x)*(y*x) by noncomm_ring] at h'
  simp only [map_add] at h'
  rw [hsq (x*y), hsq (y*x), jordan x y] at h'
  have hx : φ ((x*y)*(y*x)) = φ x * φ x * (φ y * φ y) := by
    rw [show (x*y)*(y*x) = x*(y*y)*x by noncomm_ring, sandwich, hsq]
  have hy : φ ((y*x)*(x*y)) = φ y * φ y * (φ x * φ x) := by
    rw [show (y*x)*(x*y) = y*(x*x)*y by noncomm_ring, sandwich, hsq]
  rw [hx, hy] at h'
  have hz : (φ (x*y) - φ x * φ y)^2 = 0 := by
    linear_combination (h' + (φ (x*y) - φ (y*x) - 2*φ x*φ y) * (jordan x y)) / 2
  exact sub_eq_zero.mp (pow_eq_zero hz)

private lemma exp_entire (φ : A →ₗ[ℂ] ℂ) (h1 : φ 1 = 1)
    (hunit : ∀ a : A, IsUnit a → φ a ≠ 0) (a : A) :
    Differentiable ℂ (fun z : ℂ => φ (NormedSpace.exp (z • a))) ∧
    (∀ z : ℂ, φ (NormedSpace.exp (z • a)) ≠ 0) := by
  let F : A →L[ℂ] ℂ := ⟨φ, cont φ h1 hunit⟩
  constructor
  · intro z
    apply F.differentiableAt.comp z
    exact (hasDerivAt_exp_smul_const a z).differentiableAt
  · intro z
    letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
    exact hunit _ (NormedSpace.isUnit_exp (z • a))

private lemma exp_bound (x : A) : ‖NormedSpace.exp x‖ ≤ max 1 ‖(1:A)‖ * Real.exp ‖x‖ := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  calc
    _ ≤ ∑' n : ℕ, ‖((n.factorial : ℂ)⁻¹) • x^n‖ :=
      norm_tsum_le_tsum_norm (NormedSpace.norm_expSeries_summable' x)
    _ ≤ ∑' n : ℕ, max 1 ‖(1:A)‖ * (‖x‖^n / n.factorial) := by
      apply Summable.tsum_le_tsum _ (NormedSpace.norm_expSeries_summable' x)
        ((Real.summable_pow_div_factorial ‖x‖).mul_left _)
      intro n
      rw [norm_smul, norm_inv, Complex.norm_natCast]
      have hp : ‖x^n‖ ≤ max 1 ‖(1:A)‖ * ‖x‖^n := by
        cases n with
        | zero => simp
        | succ n =>
          calc
            ‖x^(n+1)‖ ≤ ‖x‖^(n+1) := norm_pow_le' x (Nat.succ_pos n)
            _ ≤ max 1 ‖(1:A)‖ * ‖x‖^(n+1) := by
              nlinarith [le_max_left (1:ℝ) ‖(1:A)‖, pow_nonneg (norm_nonneg x) (n+1)]
      rw [div_eq_mul_inv]
      nlinarith [inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) n.factorial)]
    _ = max 1 ‖(1:A)‖ * Real.exp ‖x‖ := by
      rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
      simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

private lemma exp_derivs (φ : A →ₗ[ℂ] ℂ) (hc : Continuous φ) (a : A) :
    deriv (fun z : ℂ => φ (NormedSpace.exp (z • a))) 0 = φ a ∧
    deriv (deriv (fun z : ℂ => φ (NormedSpace.exp (z • a)))) 0 = φ (a*a) := by
  let F : A →L[ℂ] ℂ := ⟨φ, hc⟩
  have hd (z : ℂ) : HasDerivAt (fun z : ℂ => φ (NormedSpace.exp (z • a)))
      (φ (NormedSpace.exp (z • a)*a)) z := by
    exact F.hasFDerivAt.comp_hasDerivAt z (hasDerivAt_exp_smul_const a z)
  constructor
  · simpa using (hd 0).deriv
  · have heq : deriv (fun z : ℂ => φ (NormedSpace.exp (z • a))) =
        fun z => φ (NormedSpace.exp (z • a)*a) := funext (fun z => (hd z).deriv)
    rw [heq]
    have h := F.hasFDerivAt.comp_hasDerivAt (0 : ℂ)
      ((hasDerivAt_exp_smul_const a 0).mul_const a)
    simpa using h.deriv

private lemma exp_functional_bound (φ : A →ₗ[ℂ] ℂ) (h1 : φ 1 = 1)
    (hunit : ∀ a : A, IsUnit a → φ a ≠ 0) (a : A) (z : ℂ) :
    ‖φ (NormedSpace.exp (z • a))‖ ≤
      (‖(1:A)‖ * max 1 ‖(1:A)‖) * Real.exp (‖z‖ * ‖a‖) := by
  calc
    _ ≤ ‖NormedSpace.exp (z • a)‖ * ‖(1:A)‖ := bound φ h1 hunit _
    _ ≤ (max 1 ‖(1:A)‖ * Real.exp ‖z • a‖) * ‖(1:A)‖ :=
      mul_le_mul_of_nonneg_right (exp_bound _) (norm_nonneg _)
    _ = _ := by rw [norm_smul]; ring

private lemma square_final (φ : A →ₗ[ℂ] ℂ) (h1 : φ 1 = 1)
    (hu : ∀ a : A, IsUnit a → φ a ≠ 0) (a : A) : φ (a*a) = φ a * φ a := by
  let f : ℂ → ℂ := fun z => φ (NormedSpace.exp (z • a))
  have h := exp_entire φ h1 hu a
  have hf0 : f 0 = 1 := by simp [f, h1]
  have hb : ∀ z, ‖f z‖ ≤ (1 + ‖(1:A)‖ * max 1 ‖(1:A)‖) * Real.exp (‖a‖ * ‖z‖) := by
    intro z
    have hh := exp_functional_bound φ h1 hu a z
    dsimp [f]
    rw [mul_comm ‖a‖ ‖z‖]
    nlinarith [Real.exp_pos (‖z‖ * ‖a‖)]
  have heq := entire_exponential f h.1 hf0 h.2 _ _ (by nlinarith [mul_nonneg (norm_nonneg (1:A)) (le_trans zero_le_one (le_max_left (1:ℝ) ‖(1:A)‖))]) (norm_nonneg a) hb
  have hder := exp_derivs φ (cont φ h1 hu) a
  change deriv f 0 = φ a ∧ deriv (deriv f) 0 = φ (a*a) at hder
  have heq' : f = fun z => Complex.exp (z * φ a) := by
    funext z
    rw [heq z, hder.1]
  have hexp (z : ℂ) : HasDerivAt (fun z : ℂ => Complex.exp (z * φ a))
      (Complex.exp (z * φ a) * φ a) z := by
    simpa [mul_comm] using (((hasDerivAt_id z).mul_const (φ a)).cexp)
  have hfirst : deriv f = fun z => Complex.exp (z * φ a) * φ a := by
    rw [heq']; exact funext fun z => (hexp z).deriv
  rw [← hder.2, hfirst]
  simpa using ((hexp 0).mul_const (φ a)).deriv

/-- Gleason-Kahane-Zelazko theorem for complex Banach algebras: a normalized complex-linear
functional on a complex Banach algebra that does not vanish on invertible elements is an algebra
homomorphism. -/
theorem MainTheorem (A : Type*) [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] :
    ∀ φ : A →ₗ[ℂ] ℂ, φ 1 = 1 →
      (∀ a : A, IsUnit a → φ a ≠ 0) →
      ∃ ψ : A →ₐ[ℂ] ℂ, ψ.toLinearMap = φ := by
  intro φ h1 hu
  let ψ : A →ₐ[ℂ] ℂ := {
    toFun := φ
    map_one' := h1
    map_mul' := square_implies_mul φ (square_final φ h1 hu)
    map_zero' := φ.map_zero
    map_add' := φ.map_add
    commutes' := fun r => by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, h1]
      simp }
  refine ⟨ψ, ?_⟩
  ext x
  rfl

end GleasonKahaneZelazkoTheorem
