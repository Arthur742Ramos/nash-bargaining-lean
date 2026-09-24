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
    (P : Problem) (x : ℝ × ℝ) (hx : IsNashMaximizer P x) : F P = x := sorry

end NashBargaining
