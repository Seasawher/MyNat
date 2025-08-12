/- # 自然数は半順序集合 -/
import LeanBook.OrderedAdd --#

/- ## 補題: 具体的な数字に関する否定等号と不等式 -/

variable {m n k : MyNat}

/-- `0 ≠ 1` が成り立つ -/
@[simp, grind =>]
theorem MyNat.zero_ne_one : 0 ≠ 1 := by
  intro h
  injection h

/-- `1 ≠ 0` が成り立つ -/
@[simp]
theorem MyNat.one_neq_zero : 1 ≠ 0 := by
  intro h
  injection h

@[simp, grind =>]
theorem MyNat.not_zero_le_one : ¬ (1 ≤ 0) := by
  intro h
  cases h

/- ## 半順序集合 -/

@[grind →]
theorem MyNat.le_antisymm (h1 : n ≤ m) (h2 : m ≤ n) : n = m := by
  induction h1 with grind

/-- `MyNat`は半順序集合 -/
instance : Lean.Grind.PartialOrder MyNat where
  le_antisymm := MyNat.le_antisymm
