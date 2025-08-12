import LeanBook.LinearOrder --#
/- # 順序は決定可能 -/

/- ## 広義順序について -/

def MyNat.ble (a b : MyNat) : Bool :=
  match a, b with
  | 0, _ => true
  | _ + 1, 0 => false
  -- 再帰的に計算できる
  | a + 1, b + 1 => MyNat.ble a b

theorem MyNat.le_impl (m n : MyNat) : MyNat.ble m n = true ↔ m ≤ n := by
  fun_induction MyNat.ble m n with simp_all

/-- 広義の順序関係を決定可能にする -/
instance : DecidableLE MyNat := fun n m =>
  decidable_of_iff (MyNat.ble n m = true) (MyNat.le_impl n m)

/- ## 狭義順序について -/

theorem MyNat.lt_impl (m n : MyNat) : MyNat.ble (m + 1) n ↔ m < n := by
  rw [MyNat.le_impl, lt_iff_add_one_le]

/-- 狭義の順序関係を決定可能にする -/
instance : DecidableLT MyNat := fun n m =>
  decidable_of_iff (MyNat.ble (n + 1) m = true) (MyNat.lt_impl n m)
