import LeanBook.Sub --#
/- # 整除関係 -/

/- ## 整除関係の推移律まで -/

/-- MyNat 上の整除関係 -/
instance : Dvd MyNat where
  dvd a b := ∃ c : MyNat, b = a * c

/-- 整除関係の反射律 -/
@[refl, simp, grind <=]
theorem MyNat.dvd_refl (n : MyNat) : n ∣ n := by
  exists 1
  simp

@[simp, grind <=]
theorem MyNat.dvd_zero (n : MyNat) : n ∣ 0 := by
  exists 0

@[grind <=, simp]
theorem MyNat.dvd_mul_left (m n : MyNat) : m ∣ n * m := by
  exists n
  ac_rfl

@[grind <=, simp]
theorem MyNat.dvd_mul_right (m n : MyNat) : m ∣ m * n := by
  exists n

/-- 整除関係の推移律 -/
@[grind →]
theorem MyNat.dvd_trans {a b c : MyNat} (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by
  obtain ⟨d, hd⟩ := h₁
  obtain ⟨e, he⟩ := h₂
  grind

/-- 整除関係を「推移的な二項関係」として登録する -/
instance : Trans (· ∣ · : MyNat → MyNat → Prop) (· ∣ ·) (· ∣ ·) where
  trans := MyNat.dvd_trans

/- ## 1 を割り切る数は 1 しかない -/

@[grind =>]
theorem MyNat.le_one_iff_eq_zero_or_eq_one (n : MyNat) : n ≤ 1 ↔ n = 0 ∨ n = 1 := by
  -- 右から左は自明なので、左から右を示す
  refine ⟨?_, by grind⟩
  intro h

  rw [MyNat.le_iff_add] at h
  obtain ⟨k, hk⟩ := h
  match k with
  | 0 => simp_all
  | 1 => simp_all
  | k + 2 => grind

@[simp↓, grind =]
theorem MyNat.mul_eq_one_iff (m n : MyNat) : m * n = 1 ↔ m = 1 ∧ n = 1 := by
  refine ⟨?_, by grind⟩
  induction m with grind

@[simp, grind =]
theorem MyNat.dvd_one (n : MyNat) : n ∣ 1 ↔ n = 1 := by
  refine ⟨?_, by grind⟩
  intro h
  obtain ⟨c, hc⟩ := h
  grind

/- ## 整除関係を足し算・引き算は保つ -/

@[grind →]
theorem MyNat.dvd_add {a b c : MyNat} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c := by
  obtain ⟨d, hd⟩ := h₁
  obtain ⟨e, he⟩ := h₂
  grind

@[grind →]
theorem MyNat.dvd_sub {a b c : MyNat} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c := by
  obtain ⟨d, hd⟩ := h₁
  obtain ⟨e, he⟩ := h₂
  grind
