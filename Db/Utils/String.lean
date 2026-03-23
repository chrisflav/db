@[simp]
theorem ToString.toString_string (s : String) : ToString.toString s = s :=
  rfl

@[simp]
theorem String.dropPrefix?_append (s pat : String) :
    (pat ++ s).dropPrefix? pat = s := by
  sorry

theorem String.dropPrefix?_append_of_ne (s : String) {pat t : String} (h : pat ≠ t) :
    (t ++ s).dropPrefix? pat = none := by
  sorry

@[simp]
theorem String.toString_toSlice (s : String) : s.toSlice.toString = s := by
  sorry
