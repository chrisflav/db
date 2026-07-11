open String List

@[simp]
theorem ToString.toString_string (s : String) : ToString.toString s = s :=
  rfl

/-- If `u` cannot be written as `pat ++ r` for any `r`, then `pat` is not a prefix of `u`
and `dropPrefix?` returns `none`. -/
theorem String.dropPrefix?_eq_none_of_forall {u pat : String}
    (H : ∀ r : String, u ≠ pat ++ r) : u.dropPrefix? pat = none := by
  cases h : u.dropPrefix? pat with
  | none => rfl
  | some res => exact absurd (eq_append_of_dropPrefix?_string_eq_some h) (H res.copy)

/-- Drop the prefix `pfx` from `s`, returning the remaining suffix as a `String`, or `none`
if `s` does not start with `pfx`. Unlike `String.dropPrefix?` this returns a genuine `String`
(rather than a `Slice`), which makes it convenient to reason about round trips. -/
def String.stripPrefix? (s pfx : String) : Option String :=
  (s.dropPrefix? pfx).map (·.toString)

@[simp]
theorem String.stripPrefix?_append (s pfx : String) :
    (pfx ++ s).stripPrefix? pfx = some s := by
  unfold String.stripPrefix?
  cases h : (pfx ++ s).dropPrefix? pfx with
  | none =>
    exfalso
    have hs : (pfx ++ s).startsWith pfx = true := by
      simp [String.startsWith_string_iff, String.toList_append]
    have hn : (pfx ++ s).dropPrefix? pfx = none ↔ (pfx ++ s).startsWith pfx = false := by
      rw [← String.dropPrefix?_toSlice, String.Slice.dropPrefix?_eq_none_iff,
        ← String.startsWith_eq_startsWith_toSlice]
    rw [hn] at h; simp [hs] at h
  | some res =>
    have he := eq_append_of_dropPrefix?_string_eq_some h
    have hr : res.copy = s := ((String.append_right_inj pfx).mp he).symm
    simp [Option.map, String.Slice.toString_eq, hr]

theorem String.stripPrefix?_eq_none {u pfx : String} (H : ∀ r : String, u ≠ pfx ++ r) :
    u.stripPrefix? pfx = none := by
  unfold String.stripPrefix?
  rw [String.dropPrefix?_eq_none_of_forall H]
  rfl

@[simp]
theorem String.toString_toSlice (s : String) : s.toSlice.toString = s := by
  simp only [String.Slice.toString_eq, String.copy_toSlice]
