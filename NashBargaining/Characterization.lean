import NashBargaining.Existence
import NashBargaining.Uniqueness

namespace NashBargaining

theorem nashSatisfiesAxioms (F : Problem → ℝ × ℝ)
    (h : ∀ P, IsNashMaximizer P (F P)) :
    NashAxioms ⟨F, fun P => (h P).1⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P y hyS hle
    let P₀ := P
    rcases P with ⟨⟨S, d⟩, hne, hcomp, hconv, hdS, hstrict⟩
    rcases h P₀ with ⟨hFS, hF1, hF2, hFmax⟩
    change F P₀ ∈ S at hFS
    change d.1 ≤ (F P₀).1 at hF1
    change d.2 ≤ (F P₀).2 at hF2
    change ∀ z ∈ S, d.1 ≤ z.1 → d.2 ≤ z.2 →
      nashProduct d z ≤ nashProduct d (F P₀) at hFmax
    change y ∈ S at hyS
    change (F P₀).1 ≤ y.1 ∧ (F P₀).2 ≤ y.2 at hle
    have hymax : IsNashMaximizer P₀ y := by
      refine ⟨hyS, le_trans hF1 hle.1, le_trans hF2 hle.2, ?_⟩
      intro z hzS hz1 hz2
      have hgain1 : (F P₀).1 - d.1 ≤ y.1 - d.1 := by linarith
      have hgain2 : (F P₀).2 - d.2 ≤ y.2 - d.2 := by linarith
      have hgain2_nonneg : 0 ≤ (F P₀).2 - d.2 := sub_nonneg.mpr hF2
      have hygain1_nonneg : 0 ≤ y.1 - d.1 :=
        sub_nonneg.mpr (le_trans hF1 hle.1)
      calc
        nashProduct d z ≤ nashProduct d (F P₀) := hFmax z hzS hz1 hz2
        _ ≤ nashProduct d y := by
          unfold nashProduct
          exact mul_le_mul hgain1 hgain2 hgain2_nonneg hygain1_nonneg
    exact nashMaximizerUnique P₀ y (F P₀) hymax (h P₀)
  · intro P hS hdeq
    let P₀ := P
    rcases P with ⟨⟨S, d⟩, hne, hcomp, hconv, hdS, hstrict⟩
    rcases h P₀ with ⟨hFS, hF1, hF2, hFmax⟩
    change F P₀ ∈ S at hFS
    change d.1 ≤ (F P₀).1 at hF1
    change d.2 ≤ (F P₀).2 at hF2
    change ∀ z ∈ S, d.1 ≤ z.1 → d.2 ≤ z.2 →
      nashProduct d z ≤ nashProduct d (F P₀) at hFmax
    have hswap_mem : Prod.swap (F P₀) ∈ S := by
      have hmem : Prod.swap (F P₀) ∈ Prod.swap '' S :=
        Set.mem_image_of_mem Prod.swap hFS
      rwa [hS] at hmem
    have hswap1 : d.1 ≤ (Prod.swap (F P₀)).1 := by
      rw [hdeq]
      exact hF2
    have hswap2 : d.2 ≤ (Prod.swap (F P₀)).2 := by
      rw [← hdeq]
      exact hF1
    have hmax_swap : IsNashMaximizer P₀ (Prod.swap (F P₀)) := by
      change Prod.swap (F P₀) ∈ S ∧ d.1 ≤ (Prod.swap (F P₀)).1 ∧
        d.2 ≤ (Prod.swap (F P₀)).2 ∧
        (∀ z ∈ S, d.1 ≤ z.1 → d.2 ≤ z.2 →
          nashProduct d z ≤ nashProduct d (Prod.swap (F P₀)))
      refine ⟨hswap_mem, hswap1, hswap2, ?_⟩
      intro z hzS hz1 hz2
      have hzswap_mem : Prod.swap z ∈ S := by
        have hmem : Prod.swap z ∈ Prod.swap '' S := Set.mem_image_of_mem Prod.swap hzS
        rwa [hS] at hmem
      have hzswap1 : d.1 ≤ (Prod.swap z).1 := by
        rw [hdeq]
        exact hz2
      have hzswap2 : d.2 ≤ (Prod.swap z).2 := by
        rw [← hdeq]
        exact hz1
      have hprod_z : nashProduct d z = nashProduct d (Prod.swap z) := by
        simp only [nashProduct, Prod.swap]
        rw [hdeq]
        ring
      have hprod_F : nashProduct d (F P₀) = nashProduct d (Prod.swap (F P₀)) := by
        simp only [nashProduct, Prod.swap]
        rw [hdeq]
        ring
      calc
        nashProduct d z = nashProduct d (Prod.swap z) := hprod_z
        _ ≤ nashProduct d (F P₀) := hFmax (Prod.swap z) hzswap_mem hzswap1 hzswap2
        _ = nashProduct d (Prod.swap (F P₀)) := hprod_F
    have heq := nashMaximizerUnique P₀ (Prod.swap (F P₀)) (F P₀) hmax_swap (h P₀)
    have hcoord := congrArg Prod.fst heq
    simpa [Prod.swap] using hcoord.symm
  · intro P Q a1 a2 b1 b2 ha1 ha2 hQS hQd
    let P₀ := P
    let Q₀ := Q
    rcases P with ⟨⟨S, d⟩, hneP, hcompP, hconvP, hdSP, hstrictP⟩
    rcases Q with ⟨⟨T, dQ⟩, hneQ, hcompQ, hconvQ, hdTQ, hstrictQ⟩
    let φ : ℝ × ℝ → ℝ × ℝ :=
      fun x => (a1 * x.1 + b1, a2 * x.2 + b2)
    change T = φ '' S at hQS
    change dQ = φ d at hQd
    rcases h P₀ with ⟨hFS, hF1, hF2, hFmax⟩
    change F P₀ ∈ S at hFS
    change d.1 ≤ (F P₀).1 at hF1
    change d.2 ≤ (F P₀).2 at hF2
    change ∀ y ∈ S, d.1 ≤ y.1 → d.2 ≤ y.2 →
      nashProduct d y ≤ nashProduct d (F P₀) at hFmax
    have hscale (x : ℝ × ℝ) :
        nashProduct dQ (φ x) = a1 * a2 * nashProduct d x := by
      rw [hQd]
      simp [nashProduct, φ]
      ring
    have hmaxφ : IsNashMaximizer Q₀ (φ (F P₀)) := by
      change φ (F P₀) ∈ T ∧ dQ.1 ≤ (φ (F P₀)).1 ∧ dQ.2 ≤ (φ (F P₀)).2 ∧
        (∀ z ∈ T, dQ.1 ≤ z.1 → dQ.2 ≤ z.2 →
          nashProduct dQ z ≤ nashProduct dQ (φ (F P₀)))
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hQS]
        exact Set.mem_image_of_mem φ hFS
      · rw [hQd]
        simp only [φ]
        have hscaled := mul_le_mul_of_nonneg_left hF1 (le_of_lt ha1)
        linarith
      · rw [hQd]
        simp only [φ]
        have hscaled := mul_le_mul_of_nonneg_left hF2 (le_of_lt ha2)
        linarith
      · intro z hzT hz1 hz2
        rw [hQS] at hzT
        change ∃ y, y ∈ S ∧ φ y = z at hzT
        rcases hzT with ⟨y, hyS, rfl⟩
        have hy1 : d.1 ≤ y.1 := by
          have hscaled : a1 * d.1 ≤ a1 * y.1 := by
            have hraw : a1 * d.1 + b1 ≤ a1 * y.1 + b1 := by
              simpa [φ, hQd] using hz1
            linarith
          by_contra hnot
          have hylt : y.1 < d.1 := lt_of_not_ge hnot
          have hmul : a1 * y.1 < a1 * d.1 := mul_lt_mul_of_pos_left hylt ha1
          linarith
        have hy2 : d.2 ≤ y.2 := by
          have hscaled : a2 * d.2 ≤ a2 * y.2 := by
            have hraw : a2 * d.2 + b2 ≤ a2 * y.2 + b2 := by
              simpa [φ, hQd] using hz2
            linarith
          by_contra hnot
          have hylt : y.2 < d.2 := lt_of_not_ge hnot
          have hmul : a2 * y.2 < a2 * d.2 := mul_lt_mul_of_pos_left hylt ha2
          linarith
        calc
          nashProduct dQ (φ y) = a1 * a2 * nashProduct d y := hscale y
          _ ≤ a1 * a2 * nashProduct d (F P₀) :=
            mul_le_mul_of_nonneg_left (hFmax y hyS hy1 hy2)
              (mul_nonneg (le_of_lt ha1) (le_of_lt ha2))
          _ = nashProduct dQ (φ (F P₀)) := (hscale (F P₀)).symm
    change F Q₀ = φ (F P₀)
    exact nashMaximizerUnique Q₀ (F Q₀) (φ (F P₀)) (h Q₀) hmaxφ
  · intro P Q hdeq hsub hmem
    let P₀ := P
    let Q₀ := Q
    rcases P with ⟨⟨S, d⟩, hneP, hcompP, hconvP, hdSP, hstrictP⟩
    rcases Q with ⟨⟨T, dQ⟩, hneQ, hcompQ, hconvQ, hdTQ, hstrictQ⟩
    change d = dQ at hdeq
    change S ⊆ T at hsub
    change F Q₀ ∈ S at hmem
    have hQ1 : dQ.1 ≤ (F Q₀).1 := by
      simpa [Q₀] using (h Q₀).2.1
    have hQ2 : dQ.2 ≤ (F Q₀).2 := by
      simpa [Q₀] using (h Q₀).2.2.1
    have hQmax : ∀ z ∈ T, dQ.1 ≤ z.1 → dQ.2 ≤ z.2 →
        nashProduct dQ z ≤ nashProduct dQ (F Q₀) := by
      simpa [Q₀] using (h Q₀).2.2.2
    have hmaxFQ : IsNashMaximizer P₀ (F Q₀) := by
      change F Q₀ ∈ S ∧ d.1 ≤ (F Q₀).1 ∧ d.2 ≤ (F Q₀).2 ∧
        (∀ z ∈ S, d.1 ≤ z.1 → d.2 ≤ z.2 →
          nashProduct d z ≤ nashProduct d (F Q₀))
      refine ⟨hmem, ?_, ?_, ?_⟩
      · rw [hdeq]
        exact hQ1
      · rw [hdeq]
        exact hQ2
      · intro z hzS hz1 hz2
        have hzT : z ∈ T := hsub hzS
        have hz1Q : dQ.1 ≤ z.1 := by rw [← hdeq]; exact hz1
        have hz2Q : dQ.2 ≤ z.2 := by rw [← hdeq]; exact hz2
        calc
          nashProduct d z = nashProduct dQ z := by rw [hdeq]
          _ ≤ nashProduct dQ (F Q₀) := hQmax z hzT hz1Q hz2Q
          _ = nashProduct d (F Q₀) := by rw [hdeq]
    exact nashMaximizerUnique P₀ (F P₀) (F Q₀) (h P₀) hmaxFQ

theorem axiomsCharacterizeNash (F : Solution) (h : NashAxioms F)
    (P : Problem) (x : ℝ × ℝ) (hx : IsNashMaximizer P x) : F P = x := by
  rcases h with ⟨hPareto, hSymm, hInv, hIIA⟩
  rcases P.property with ⟨hne, hcomp, hconv, hdS, hstrict⟩
  rcases hstrict with ⟨x₀, hx₀S, hx₀₁, hx₀₂⟩
  rcases hx with ⟨hxS, hx1, hx2, hxmax⟩
  let S : Set (ℝ × ℝ) := P.val.1
  let d : ℝ × ℝ := P.val.2

  have hprod₀ : 0 < nashProduct d x₀ := by
    unfold nashProduct
    exact mul_pos (sub_pos.mpr hx₀₁) (sub_pos.mpr hx₀₂)
  have hprod₀x : nashProduct d x₀ ≤ nashProduct d x :=
    hxmax x₀ hx₀S (le_of_lt hx₀₁) (le_of_lt hx₀₂)
  have hpos : 0 < nashProduct d x := lt_of_lt_of_le hprod₀ hprod₀x
  have hx₁ : d.1 < x.1 := by
    by_contra hnot
    have hle : x.1 ≤ d.1 := le_of_not_gt hnot
    have heq : x.1 - d.1 = 0 := by linarith
    unfold nashProduct at hpos
    rw [heq] at hpos
    simp at hpos
  have hx₂ : d.2 < x.2 := by
    by_contra hnot
    have hle : x.2 ≤ d.2 := le_of_not_gt hnot
    have heq : x.2 - d.2 = 0 := by linarith
    unfold nashProduct at hpos
    rw [heq] at hpos
    simp at hpos

  let a1 : ℝ := 1 / (x.1 - d.1)
  let a2 : ℝ := 1 / (x.2 - d.2)
  have ha1pos : 0 < a1 := one_div_pos.mpr (sub_pos.mpr hx₁)
  have ha2pos : 0 < a2 := one_div_pos.mpr (sub_pos.mpr hx₂)
  have ha1x : a1 * (x.1 - d.1) = 1 := by
    dsimp [a1]
    exact one_div_mul_cancel (ne_of_gt (sub_pos.mpr hx₁))
  have ha2x : a2 * (x.2 - d.2) = 1 := by
    dsimp [a2]
    exact one_div_mul_cancel (ne_of_gt (sub_pos.mpr hx₂))
  let φ : ℝ × ℝ → ℝ × ℝ := fun u =>
    (a1 * u.1 - a1 * d.1, a2 * u.2 - a2 * d.2)
  have hφd : φ d = (0, 0) := by
    ext <;> simp [φ]
  have hφx : φ x = (1, 1) := by
    apply Prod.ext
    · change a1 * x.1 - a1 * d.1 = 1
      rw [← mul_sub]
      exact ha1x
    · change a2 * x.2 - a2 * d.2 = 1
      rw [← mul_sub]
      exact ha2x
  have hφcont : Continuous φ := by
    exact Continuous.prodMk ((continuous_const.mul continuous_fst).sub continuous_const)
      ((continuous_const.mul continuous_snd).sub continuous_const)

  let U : Set (ℝ × ℝ) := φ '' S
  have hUconv : Convex ℝ U := by
    intro u hu v hv a b ha hb hab
    rcases hu with ⟨s₁, hs₁, rfl⟩
    rcases hv with ⟨s₂, hs₂, rfl⟩
    refine ⟨a • s₁ + b • s₂, hconv hs₁ hs₂ ha hb hab, ?_⟩
    apply Prod.ext
    · simp [φ, smul_eq_mul]
      linear_combination a1 * d.1 * hab
    · simp [φ, smul_eq_mul]
      linear_combination a2 * d.2 * hab
  have h0U : (0, 0) ∈ U := ⟨d, hdS, hφd⟩
  have h11U : (1, 1) ∈ U := ⟨x, hxS, hφx⟩
  have hQstrict₁ : 0 < (φ x₀).1 := by
    change 0 < a1 * x₀.1 - a1 * d.1
    rw [← mul_sub]
    exact mul_pos ha1pos (sub_pos.mpr hx₀₁)
  have hQstrict₂ : 0 < (φ x₀).2 := by
    change 0 < a2 * x₀.2 - a2 * d.2
    rw [← mul_sub]
    exact mul_pos ha2pos (sub_pos.mpr hx₀₂)
  let Q : Problem :=
    ⟨(U, (0, 0)), hne.image φ, hcomp.image hφcont, hUconv, h0U,
      ⟨φ x₀, ⟨x₀, hx₀S, rfl⟩, hQstrict₁, hQstrict₂⟩⟩

  have hkey (s : ℝ × ℝ) :
      nashProduct (0, 0) (φ s) = a1 * a2 * nashProduct d s := by
    simp [nashProduct, φ]
    ring
  have hQmax : IsNashMaximizer Q (1, 1) := by
    change (1, 1) ∈ U ∧ (0 : ℝ) ≤ 1 ∧ (0 : ℝ) ≤ 1 ∧
      (∀ z ∈ U, (0 : ℝ) ≤ z.1 → (0 : ℝ) ≤ z.2 →
        nashProduct (0, 0) z ≤ nashProduct (0, 0) (1, 1))
    refine ⟨h11U, by norm_num, by norm_num, ?_⟩
    intro z hzU hz1 hz2
    rcases hzU with ⟨s, hsS, rfl⟩
    have hs1 : d.1 ≤ s.1 := by
      by_contra hnot
      have hlt : s.1 < d.1 := lt_of_not_ge hnot
      have hz1' : 0 ≤ a1 * (s.1 - d.1) := by
        have ht : 0 ≤ a1 * s.1 - a1 * d.1 := by simpa [φ] using hz1
        rw [mul_sub]
        exact ht
      have hneg : a1 * (s.1 - d.1) < 0 :=
        mul_neg_of_pos_of_neg ha1pos (sub_neg.mpr hlt)
      linarith
    have hs2 : d.2 ≤ s.2 := by
      by_contra hnot
      have hlt : s.2 < d.2 := lt_of_not_ge hnot
      have hz2' : 0 ≤ a2 * (s.2 - d.2) := by
        have ht : 0 ≤ a2 * s.2 - a2 * d.2 := by simpa [φ] using hz2
        rw [mul_sub]
        exact ht
      have hneg : a2 * (s.2 - d.2) < 0 :=
        mul_neg_of_pos_of_neg ha2pos (sub_neg.mpr hlt)
      linarith
    calc
      nashProduct (0, 0) (φ s) = a1 * a2 * nashProduct d s := hkey s
      _ ≤ a1 * a2 * nashProduct d x :=
        mul_le_mul_of_nonneg_left (hxmax s hsS hs1 hs2)
          (mul_nonneg (le_of_lt ha1pos) (le_of_lt ha2pos))
      _ = nashProduct (0, 0) (φ x) := (hkey x).symm
      _ = nashProduct (0, 0) (1, 1) := by rw [hφx]

  have htangent : ∀ z ∈ U, z.1 + z.2 ≤ 2 := by
    intro z hz
    by_contra hnot
    have hsum : 2 < z.1 + z.2 := lt_of_not_ge hnot
    let c : ℝ := z.1 + z.2 - 2
    have hc : 0 < c := by dsimp [c]; linarith
    let K : ℝ := |(z.1 - 1) * (z.2 - 1)|
    let K1 : ℝ := |z.1 - 1|
    let K2 : ℝ := |z.2 - 1|
    let t : ℝ := min (min (1 / 2) (c / (2 * (K + 1))))
      (min (1 / (2 * (K1 + 1))) (1 / (2 * (K2 + 1))))
    have ht : 0 < t := by
      dsimp [t]
      apply lt_min_iff.mpr
      constructor
      · apply lt_min_iff.mpr
        constructor
        · norm_num
        · positivity
      · apply lt_min_iff.mpr
        constructor <;> positivity
    have htHalf : t ≤ 1 / 2 := by
      dsimp [t]
      exact (min_le_left _ _).trans (min_le_left _ _)
    have htC : t ≤ c / (2 * (K + 1)) := by
      dsimp [t]
      exact (min_le_left _ _).trans (min_le_right _ _)
    have htK : t * K ≤ c / 2 := by
      have hden : 0 < K + 1 := by dsimp [K]; positivity
      have htplus : t * (K + 1) ≤ c / 2 := by
        calc
          t * (K + 1) ≤ (c / (2 * (K + 1))) * (K + 1) :=
            mul_le_mul_of_nonneg_right htC (by positivity)
          _ = c / 2 := by field_simp
      calc
        t * K ≤ t * (K + 1) := by nlinarith [le_of_lt ht]
        _ ≤ c / 2 := htplus
    have htK1 : t * K1 ≤ 1 / 2 := by
      have ht₁ : t ≤ 1 / (2 * (K1 + 1)) := by
        dsimp [t]
        exact (min_le_right _ _).trans (min_le_left _ _)
      have htplus : t * (K1 + 1) ≤ 1 / 2 := by
        calc
          t * (K1 + 1) ≤ (1 / (2 * (K1 + 1))) * (K1 + 1) :=
            mul_le_mul_of_nonneg_right ht₁ (by positivity)
          _ = 1 / 2 := by
            have hpos : 0 < K1 + 1 := by dsimp [K1]; positivity
            have hrewrite : 1 / (2 * (K1 + 1)) = (1 / 2) * (1 / (K1 + 1)) := by
              field_simp
            rw [hrewrite, mul_assoc, one_div_mul_cancel (ne_of_gt hpos), mul_one]
      calc
        t * K1 ≤ t * (K1 + 1) := by nlinarith [le_of_lt ht]
        _ ≤ 1 / 2 := htplus
    have htK2 : t * K2 ≤ 1 / 2 := by
      have ht₂ : t ≤ 1 / (2 * (K2 + 1)) := by
        dsimp [t]
        exact (min_le_right _ _).trans (min_le_right _ _)
      have htplus : t * (K2 + 1) ≤ 1 / 2 := by
        calc
          t * (K2 + 1) ≤ (1 / (2 * (K2 + 1))) * (K2 + 1) :=
            mul_le_mul_of_nonneg_right ht₂ (by positivity)
          _ = 1 / 2 := by
            have hpos : 0 < K2 + 1 := by dsimp [K2]; positivity
            have hrewrite : 1 / (2 * (K2 + 1)) = (1 / 2) * (1 / (K2 + 1)) := by
              field_simp
            rw [hrewrite, mul_assoc, one_div_mul_cancel (ne_of_gt hpos), mul_one]
      calc
        t * K2 ≤ t * (K2 + 1) := by nlinarith [le_of_lt ht]
        _ ≤ 1 / 2 := htplus
    let w : ℝ × ℝ := (1 - t) • (1, 1) + t • z
    have hwU : w ∈ U := by
      apply hUconv h11U hz (by linarith [htHalf]) (le_of_lt ht)
        (by ring : (1 - t) + t = 1)
    have hw1eq : w.1 = 1 + t * (z.1 - 1) := by
      dsimp [w]
      simp
      ring
    have hw2eq : w.2 = 1 + t * (z.2 - 1) := by
      dsimp [w]
      simp
      ring
    have hw1 : 0 < w.1 := by
      have habs : |t * (z.1 - 1)| = t * K1 := by
        rw [abs_mul, abs_of_pos ht]
      have hsmall : |t * (z.1 - 1)| ≤ 1 / 2 := by rw [habs]; exact htK1
      rw [hw1eq]
      have hlow : -(1 / 2) ≤ t * (z.1 - 1) :=
        (neg_le_neg hsmall).trans (neg_abs_le _)
      linarith
    have hw2 : 0 < w.2 := by
      have habs : |t * (z.2 - 1)| = t * K2 := by
        rw [abs_mul, abs_of_pos ht]
      have hsmall : |t * (z.2 - 1)| ≤ 1 / 2 := by rw [habs]; exact htK2
      rw [hw2eq]
      have hlow : -(1 / 2) ≤ t * (z.2 - 1) :=
        (neg_le_neg hsmall).trans (neg_abs_le _)
      linarith
    have habsProd : |t * ((z.1 - 1) * (z.2 - 1))| = t * K := by
      rw [abs_mul, abs_of_pos ht]
    have hcross : -(c / 2) ≤ t * ((z.1 - 1) * (z.2 - 1)) := by
      calc
        -(c / 2) ≤ -(t * K) := by linarith [htK]
        _ = -|t * ((z.1 - 1) * (z.2 - 1))| := by rw [habsProd]
        _ ≤ t * ((z.1 - 1) * (z.2 - 1)) := neg_abs_le _
    have hcross' := mul_le_mul_of_nonneg_left hcross (le_of_lt ht)
    have hgain : 0 < t * c + t * (t * ((z.1 - 1) * (z.2 - 1))) := by
      nlinarith [mul_pos ht hc, hcross']
    have hprod : 1 < w.1 * w.2 := by
      rw [hw1eq, hw2eq]
      have heq :
          (1 + t * (z.1 - 1)) * (1 + t * (z.2 - 1)) - 1 =
            t * c + t * (t * ((z.1 - 1) * (z.2 - 1))) := by
        dsimp [c]
        ring
      linarith
    have hle := hQmax.2.2.2 w hwU (le_of_lt hw1) (le_of_lt hw2)
    have hle' : w.1 * w.2 ≤ 1 := by
      simpa [nashProduct, Q] using hle
    linarith

  have hQcomp : IsCompact U := hcomp.image hφcont
  let V : Set (ℝ × ℝ) := U ∪ Prod.swap '' U
  have hVcomp : IsCompact V := by
    dsimp [V]
    exact hQcomp.union (hQcomp.image continuous_swap)
  let T₁ : Set ℝ := Prod.fst '' V
  let T₂ : Set ℝ := Prod.snd '' V
  have hT₁comp : IsCompact T₁ := hVcomp.image continuous_fst
  have hT₂comp : IsCompact T₂ := hVcomp.image continuous_snd
  obtain ⟨M₁, hM₁⟩ := hT₁comp.bddAbove
  obtain ⟨m₁, hm₁⟩ := hT₁comp.bddBelow
  obtain ⟨M₂, hM₂⟩ := hT₂comp.bddAbove
  obtain ⟨m₂, hm₂⟩ := hT₂comp.bddBelow
  let B : ℝ := |M₁| + |m₁| + |M₂| + |m₂| + 1
  let Box : Set (ℝ × ℝ) := Set.Icc (-B) B ×ˢ Set.Icc (-B) B
  let H : Set (ℝ × ℝ) := {y | y.1 + y.2 ≤ 2}
  let W : Set (ℝ × ℝ) := Box ∩ H
  have hB₁ : |M₁| ≤ B := by dsimp [B]; linarith [abs_nonneg m₁, abs_nonneg M₂, abs_nonneg m₂]
  have hB₂ : |m₁| ≤ B := by dsimp [B]; linarith [abs_nonneg M₁, abs_nonneg M₂, abs_nonneg m₂]
  have hB₃ : |M₂| ≤ B := by dsimp [B]; linarith [abs_nonneg M₁, abs_nonneg m₁, abs_nonneg m₂]
  have hB₄ : |m₂| ≤ B := by dsimp [B]; linarith [abs_nonneg M₁, abs_nonneg m₁, abs_nonneg M₂]
  have hVbox : V ⊆ Box := by
    intro v hv
    have hv₁ : v.1 ∈ T₁ := ⟨v, hv, rfl⟩
    have hv₂ : v.2 ∈ T₂ := ⟨v, hv, rfl⟩
    have hm₁' : ∀ y ∈ T₁, m₁ ≤ y := by simpa [lowerBounds] using hm₁
    have hM₁' : ∀ y ∈ T₁, y ≤ M₁ := by simpa [upperBounds] using hM₁
    have hm₂' : ∀ y ∈ T₂, m₂ ≤ y := by simpa [lowerBounds] using hm₂
    have hM₂' : ∀ y ∈ T₂, y ≤ M₂ := by simpa [upperBounds] using hM₂
    have hv₁lo : m₁ ≤ v.1 := hm₁' v.1 hv₁
    have hv₁hi : v.1 ≤ M₁ := hM₁' v.1 hv₁
    have hv₂lo : m₂ ≤ v.2 := hm₂' v.2 hv₂
    have hv₂hi : v.2 ≤ M₂ := hM₂' v.2 hv₂
    have hv₁lo' : -B ≤ v.1 := by linarith [neg_abs_le m₁, hB₂]
    have hv₁hi' : v.1 ≤ B := by linarith [le_abs_self M₁, hB₁]
    have hv₂lo' : -B ≤ v.2 := by linarith [neg_abs_le m₂, hB₄]
    have hv₂hi' : v.2 ≤ B := by linarith [le_abs_self M₂, hB₃]
    change v.1 ∈ Set.Icc (-B) B ∧ v.2 ∈ Set.Icc (-B) B
    exact ⟨⟨hv₁lo', hv₁hi'⟩, ⟨hv₂lo', hv₂hi'⟩⟩
  have hHconv : Convex ℝ H := by
    intro u hu v hv a b ha hb hab
    have hu' : u.1 + u.2 ≤ 2 := hu
    have hv' : v.1 + v.2 ≤ 2 := hv
    have hmul₁ : 0 ≤ a * (2 - (u.1 + u.2)) :=
      mul_nonneg ha (by linarith)
    have hmul₂ : 0 ≤ b * (2 - (v.1 + v.2)) :=
      mul_nonneg hb (by linarith)
    change (a • u + b • v).1 + (a • u + b • v).2 ≤ 2
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    nlinarith [hmul₁, hmul₂]
  have hBoxconv : Convex ℝ Box :=
    (convex_Icc (-B) B).prod (convex_Icc (-B) B)
  have hWconv : Convex ℝ W := by
    dsimp [W]
    exact hBoxconv.inter hHconv
  have hHclosed : IsClosed H := by
    apply isClosed_le (continuous_fst.add continuous_snd) continuous_const
  have hWcomp : IsCompact W := by
    dsimp [W, Box]
    exact (isCompact_Icc.prod isCompact_Icc).inter_right hHclosed
  have hBge1 : 1 ≤ B := by
    dsimp [B]
    have h₁ : 0 ≤ |M₁| := abs_nonneg M₁
    have h₂ : 0 ≤ |m₁| := abs_nonneg m₁
    have h₃ : 0 ≤ |M₂| := abs_nonneg M₂
    have h₄ : 0 ≤ |m₂| := abs_nonneg m₂
    linarith
  have h0W : (0, 0) ∈ W := by
    change ((0 : ℝ) ∈ Set.Icc (-B) B ∧ (0 : ℝ) ∈ Set.Icc (-B) B) ∧
      (0 : ℝ) + 0 ≤ 2
    constructor
    · constructor <;> constructor <;> linarith
    · norm_num
  have h11W : (1, 1) ∈ W := by
    change ((1 : ℝ) ∈ Set.Icc (-B) B ∧ (1 : ℝ) ∈ Set.Icc (-B) B) ∧
      (1 : ℝ) + 1 ≤ 2
    constructor
    · constructor <;> constructor <;> linarith
    · norm_num
  have hVsum : ∀ v ∈ V, v.1 + v.2 ≤ 2 := by
    intro v hv
    rcases hv with hv | ⟨u, hu, rfl⟩
    · exact htangent v hv
    · simpa [Prod.swap, add_comm] using htangent u hu
  have hVW : V ⊆ W := by
    intro v hv
    exact ⟨hVbox hv, hVsum v hv⟩
  have hUsum : ∀ u ∈ U, u.1 + u.2 ≤ 2 := fun u hu => htangent u hu
  have hUW : U ⊆ W := by
    intro u hu
    exact hVW (Or.inl hu)
  have hWsym : Prod.swap '' W = W := by
    have hswap : ∀ y : ℝ × ℝ, y ∈ W ↔ Prod.swap y ∈ W := by
      intro y
      simp [W, Box, H, Prod.swap, Set.mem_Icc, add_comm,
        Prod.le_def, and_assoc, and_comm]
    apply Set.Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      exact (hswap z).mp hz
    · intro y hy
      refine ⟨Prod.swap y, (hswap y).mp hy, ?_⟩
      cases y
      rfl

  have hsumW : ∀ w ∈ W, w.1 + w.2 ≤ 2 := by
    intro w hw
    exact hw.2
  let R : Problem := ⟨(W, (0, 0)), ⟨(0, 0), h0W⟩, hWcomp, hWconv, h0W,
    ⟨(1, 1), h11W, by norm_num, by norm_num⟩⟩
  have hFRsym : (F R).1 = (F R).2 := hSymm R hWsym rfl
  let t : ℝ := (F R).1
  have ht1 : (F R).1 = t := rfl
  have ht2 : (F R).2 = t := by dsimp [t]; exact hFRsym.symm
  have htge : 1 ≤ t := by
    by_contra hnot
    have htlt : t < 1 := lt_of_not_ge hnot
    have hdom : (F R).1 ≤ (1, 1).1 ∧ (F R).2 ≤ (1, 1).2 := by
      simp only [ht1, ht2]
      constructor <;> linarith
    have heq := hPareto R (1, 1) h11W hdom
    have heq₁ := congrArg Prod.fst heq
    simp only [ht1] at heq₁
    linarith
  have htle : t ≤ 1 := by
    have hFRW : F R ∈ W := F.property R
    have hbound := hsumW (F R) hFRW
    rw [ht1, ht2] at hbound
    linarith
  have hFR : F R = (1, 1) := by
    apply Prod.ext <;> simp only [ht1, ht2] <;> linarith

  have hQRsub : Q.val.1 ⊆ R.val.1 := by
    change U ⊆ W
    exact hUW
  have hFRQ : F R ∈ Q.val.1 := by
    rw [hFR]
    exact h11U
  have hFQR : F Q = F R := hIIA Q R rfl hQRsub hFRQ
  have hFQ : F Q = (1, 1) := by rw [hFQR, hFR]

  have hQS : Q.val.1 =
      (fun u : ℝ × ℝ => (a1 * u.1 + -a1 * d.1, a2 * u.2 + -a2 * d.2)) ''
        P.val.1 := by
    change (fun u : ℝ × ℝ =>
      (a1 * u.1 - a1 * d.1, a2 * u.2 - a2 * d.2)) '' P.val.1 = _
    congr 1
    funext u
    apply Prod.ext <;> ring_nf
  have hQd : Q.val.2 = (a1 * d.1 + -a1 * d.1, a2 * d.2 + -a2 * d.2) := by
    change (0, 0) = _
    apply Prod.ext <;> ring_nf
  have hFQφ : F Q = φ (F P) := by
    have h := hInv P Q a1 a2 (-a1 * d.1) (-a2 * d.2)
      ha1pos ha2pos hQS hQd
    calc
      F Q = (a1 * (F P).1 + -a1 * d.1,
          a2 * (F P).2 + -a2 * d.2) := h
      _ = φ (F P) := by
        apply Prod.ext
        · simp only [φ]
          ring_nf
        · simp only [φ]
          ring_nf
  have hφinj : Function.Injective φ := by
    intro u v huv
    have he1 := congrArg Prod.fst huv
    have he2 := congrArg Prod.snd huv
    change a1 * u.1 - a1 * d.1 = a1 * v.1 - a1 * d.1 at he1
    change a2 * u.2 - a2 * d.2 = a2 * v.2 - a2 * d.2 at he2
    have hu1v1 : a1 * (u.1 - v.1) = 0 := by
      calc
        a1 * (u.1 - v.1) = a1 * u.1 - a1 * v.1 := by ring
        _ = 0 := by linarith
    have hu2v2 : a2 * (u.2 - v.2) = 0 := by
      calc
        a2 * (u.2 - v.2) = a2 * u.2 - a2 * v.2 := by ring
        _ = 0 := by linarith
    have hcoord1 : u.1 = v.1 := by
      rcases mul_eq_zero.mp hu1v1 with h | h
      · exact (False.elim ((ne_of_gt ha1pos) h))
      · linarith
    have hcoord2 : u.2 = v.2 := by
      rcases mul_eq_zero.mp hu2v2 with h | h
      · exact (False.elim ((ne_of_gt ha2pos) h))
      · linarith
    exact Prod.ext hcoord1 hcoord2
  have hφFx : φ (F P) = (1, 1) := by rw [← hFQφ, hFQ]
  have hφx' : φ x = (1, 1) := hφx
  exact hφinj (hφFx.trans hφx'.symm)

end NashBargaining
