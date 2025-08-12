import LeanBook.Preorder --#
/- # 前順序と足し算は整合する -/

/- ## 順序関係を足し算で置き換える -/

variable {m n k : MyNat}

/-- `a ≤ b`から和の等式を導く -/
theorem MyNat.le.dest (h : n ≤ m) : ∃ k, n + k = m := by
  induction h with
  | refl => exists 0
  | @step l h ih =>
    obtain ⟨k, ih⟩ := ih
    exists k + 1
    grind

@[grind =>]
theorem MyNat.le_add_right (n m : MyNat) : n ≤ n + m := by
  induction m with grind

/-- 和の等式から`a ≤ b`を導く -/
@[grind =>]
theorem MyNat.le.intro (h : n + k = m) : n ≤ m := by
  induction k with grind

/-- 順序関係`n ≤ m`を足し算で書き換える -/
theorem MyNat.le_iff_add : n ≤ m ↔ ∃ k, n + k = m := by
  constructor <;> grind [MyNat.le.dest]

/- ## 足し算は順序関係を保ち、キャンセル可能 -/

variable {l : MyNat}

@[grind =>]
theorem MyNat.add_le_left (h : n ≤ m) : n + k ≤ m + k := by
  induction h with grind

@[grind →]
theorem MyNat.le_of_add_le_left (h : n + k ≤ m + k) : n ≤ m := by
  rw [MyNat.le_iff_add] at h
  obtain ⟨l, h⟩ := h
  grind

@[grind =, simp↓]
theorem MyNat.add_le_left_iff : n + k ≤ m + k ↔ n ≤ m := by
  constructor <;> grind

@[grind =, simp↓]
theorem MyNat.add_le_right_iff : k + n ≤ k + m ↔ n ≤ m := by
  constructor <;> grind

@[simp↓, grind =]
theorem MyNat.add_left_le_self_iff : k + n ≤ k ↔ n ≤ 0 := by
  constructor <;> grind

@[simp↓, grind =]
theorem MyNat.add_right_le_self_iff : n + k ≤ k ↔ n ≤ 0 := by
  constructor <;> grind

/-- 足し算が前順序と整合的である -/
instance : Lean.Grind.OrderedAdd MyNat where
  add_le_left_iff := by grind
