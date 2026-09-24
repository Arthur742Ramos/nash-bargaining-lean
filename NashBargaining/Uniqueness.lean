import NashBargaining.Basic

namespace NashBargaining

theorem nashMaximizerUnique : ∀ P x y, IsNashMaximizer P x → IsNashMaximizer P y → x = y := by
  intro P x y hx hy
  rcases P with ⟨⟨S, d⟩, hP⟩
  rcases hP with ⟨_, _, hconv, _, hbetter⟩
  rcases hbetter with ⟨x₀, hx₀S, hx₀₁, hx₀₂⟩
  rcases hx with ⟨hxS, hx₁, hx₂, hxmax⟩
  rcases hy with ⟨hyS, hy₁, hy₂, hymax⟩

  let a : ℝ := x.1 - d.1
  let b : ℝ := x.2 - d.2
  let c : ℝ := y.1 - d.1
  let e : ℝ := y.2 - d.2
  let M : ℝ := nashProduct d x

  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    linarith
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    linarith
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    linarith
  have he_nonneg : 0 ≤ e := by
    dsimp [e]
    linarith

  have hxyval : nashProduct d x = nashProduct d y := by
    apply le_antisymm
    · exact hymax x hxS hx₁ hx₂
    · exact hxmax y hyS hy₁ hy₂

  have hab : a * b = M := by
    dsimp [a, b, M, nashProduct]
  have hce : c * e = M := by
    calc
      c * e = nashProduct d y := by
        dsimp [c, e, nashProduct]
      _ = nashProduct d x := hxyval.symm
      _ = M := rfl

  have hMpos : 0 < M := by
    have hx₀prod : 0 < nashProduct d x₀ := by
      dsimp [nashProduct]
      exact mul_pos (sub_pos.mpr hx₀₁) (sub_pos.mpr hx₀₂)
    have hmax := hxmax x₀ hx₀S (le_of_lt hx₀₁) (le_of_lt hx₀₂)
    dsimp [M]
    exact lt_of_lt_of_le hx₀prod hmax

  have ha_pos : 0 < a := by
    by_contra h
    have ha_le : a ≤ 0 := le_of_not_gt h
    have hprod_le : a * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha_le hb_nonneg
    rw [hab] at hprod_le
    exact (not_le_of_gt hMpos) hprod_le
  have hb_pos : 0 < b := by
    by_contra h
    have hb_le : b ≤ 0 := le_of_not_gt h
    have hprod_le : a * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha_nonneg hb_le
    rw [hab] at hprod_le
    exact (not_le_of_gt hMpos) hprod_le
  have hc_pos : 0 < c := by
    by_contra h
    have hc_le : c ≤ 0 := le_of_not_gt h
    have hprod_le : c * e ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc_le he_nonneg
    rw [hce] at hprod_le
    exact (not_le_of_gt hMpos) hprod_le
  have he_pos : 0 < e := by
    by_contra h
    have he_le : e ≤ 0 := le_of_not_gt h
    have hprod_le : c * e ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc_nonneg he_le
    rw [hce] at hprod_le
    exact (not_le_of_gt hMpos) hprod_le

  by_contra hne
  have hac : a ≠ c := by
    intro hac
    have hbe : b = e := by
      have hprod : a * b = a * e := by
        calc
          a * b = c * e := by rw [hab, hce]
          _ = a * e := by rw [hac]
      exact mul_left_cancel₀ (ne_of_gt ha_pos) hprod
    apply hne
    apply Prod.ext
    · dsimp [a, c] at hac
      linarith
    · dsimp [b, e] at hbe
      linarith

  let z : ℝ × ℝ := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y
  let u : ℝ := (a + c) / 2
  let v : ℝ := (b + e) / 2

  have hzS : z ∈ S := by
    dsimp [z]
    exact hconv hxS hyS (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)

  have hz₁ : z.1 - d.1 = u := by
    dsimp [z, u, a, c]
    simp
    ring
  have hz₂ : z.2 - d.2 = v := by
    dsimp [z, v, b, e]
    simp
    ring

  have hgap : 4 * c * (u * v - M) = b * (a - c) ^ 2 := by
    calc
      4 * c * (u * v - M) = a * (c * e) + (c * c) * b + c * (c * e) - 3 * (a * b) * c := by
        dsimp [u, v, M, nashProduct]
        ring
      _ = a * (a * b) + (c * c) * b + c * (a * b) - 3 * (a * b) * c := by
        rw [show c * e = a * b by rw [hce, hab]]
      _ = b * (a - c) ^ 2 := by ring

  have hgap_pos : 0 < 4 * c * (u * v - M) := by
    rw [hgap]
    exact mul_pos hb_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hac))
  have hmid : M < u * v := by
    have hfactor : 0 < 4 * c := by positivity
    have hdiff : 0 < u * v - M := by
      by_contra hnot
      have hle : u * v - M ≤ 0 := le_of_not_gt hnot
      have hmul : 4 * c * (u * v - M) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hfactor) hle
      exact (not_le_of_gt hgap_pos) hmul
    linarith

  have hz₁_nonneg : d.1 ≤ z.1 := by
    have : 0 < z.1 - d.1 := by rw [hz₁]; dsimp [u]; positivity
    linarith
  have hz₂_nonneg : d.2 ≤ z.2 := by
    have : 0 < z.2 - d.2 := by rw [hz₂]; dsimp [v]; positivity
    linarith
  have hzval : nashProduct d z = u * v := by
    dsimp [nashProduct]
    rw [hz₁, hz₂]
  have hzmax : nashProduct d z ≤ M := by
    simpa [M] using hxmax z hzS hz₁_nonneg hz₂_nonneg
  rw [hzval] at hzmax
  exact (not_le_of_gt hmid) hzmax

end NashBargaining
